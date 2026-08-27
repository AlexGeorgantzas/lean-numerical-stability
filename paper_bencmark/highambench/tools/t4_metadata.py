#!/usr/bin/env python3
"""Freeze or check the file bindings in one paper-local T4 task record."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
from typing import Any, Callable, Mapping, Sequence
import uuid

try:
    from .common import BenchmarkToolError
    from .task_tags import (
        T4_CONSTRUCTION_INPUT_KEYS,
        T4_REVIEW_CAMPAIGN_STATUSES,
        validate_t4_file_bindings,
        validate_task_source_tags,
    )
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError  # type: ignore
    from task_tags import (  # type: ignore
        T4_CONSTRUCTION_INPUT_KEYS,
        T4_REVIEW_CAMPAIGN_STATUSES,
        validate_t4_file_bindings,
        validate_task_source_tags,
    )


MODES = ("write-set", "freeze", "check")
PAPER_ID_RE = re.compile(r"^P[0-9]{2}$")
SchemaValidator = Callable[..., dict[str, Any]]


def _validate_paper_id(paper_id: str) -> None:
    if PAPER_ID_RE.fullmatch(paper_id) is None:
        raise BenchmarkToolError(
            f"paper id must have canonical P0X form (for example P06): {paper_id!r}"
        )


def _benchmark_root(path: Path) -> Path:
    if path.is_symlink() or not path.is_dir():
        raise BenchmarkToolError(
            f"benchmark root must be a non-symlink directory: {path}"
        )
    return path.resolve()


def _assert_no_symlink_components(root: Path, path: Path, label: str) -> None:
    try:
        relative = path.relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(f"{label} escapes benchmark root: {path}") from error
    cursor = root
    for part in relative.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise BenchmarkToolError(f"{label} contains a symlink component: {cursor}")


def _regular_file(root: Path, path: Path, label: str) -> None:
    _assert_no_symlink_components(root, path, label)
    if not path.is_file():
        raise BenchmarkToolError(f"{label} must be a regular file: {path}")


def _canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _read_json_bytes(path: Path, label: str) -> tuple[bytes, Mapping[str, Any]]:
    try:
        payload = path.read_bytes()
        value = json.loads(payload)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"cannot read {label} JSON {path}: {error}") from error
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object: {path}")
    return payload, value


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as error:
        raise BenchmarkToolError(f"cannot hash {path}: {error}") from error
    return digest.hexdigest()


def _paths(root: Path, paper_id: str) -> dict[str, Path]:
    task_root = root / "tasks" / paper_id / "T4"
    return {
        "task": task_root / "task.json",
        "paper_definitions_sha256": (
            root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean"
        ),
        "source_inventory_sha256": task_root / "source_inventory.json",
        "target_sha256": task_root / "Target.lean",
    }


def _write_set(paper_id: str) -> list[dict[str, str]]:
    return [{"path": f"tasks/{paper_id}/T4/task.json"}]


def _input_hashes(
    root: Path, paths: Mapping[str, Path], task_id: str
) -> dict[str, str]:
    result: dict[str, str] = {}
    for field in (
        "paper_definitions_sha256",
        "source_inventory_sha256",
        "target_sha256",
    ):
        path = paths[field]
        _regular_file(root, path, f"{task_id} {field}")
        result[field] = _sha256(path)
    return result


def _validate_identity(task: Mapping[str, Any], paper_id: str) -> None:
    task_id = f"{paper_id}-T4"
    if task.get("task_id") != task_id:
        raise BenchmarkToolError(
            f"tasks/{paper_id}/T4/task.json must have task_id {task_id!r}"
        )
    if task.get("paper_id") != paper_id:
        raise BenchmarkToolError(
            f"{task_id}.paper_id must be {paper_id!r}"
        )
    if task.get("tier") != "T4":
        raise BenchmarkToolError(f"{task_id}.tier must be 'T4'")


def _construction_inputs(task: Mapping[str, Any], task_id: str) -> Mapping[str, Any]:
    value = task.get("construction_inputs")
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{task_id}.construction_inputs must be an object")
    if set(value) != T4_CONSTRUCTION_INPUT_KEYS:
        raise BenchmarkToolError(
            f"{task_id}.construction_inputs must contain exactly "
            f"{sorted(T4_CONSTRUCTION_INPUT_KEYS)}"
        )
    status = value.get("review_campaign_status")
    if status not in T4_REVIEW_CAMPAIGN_STATUSES:
        raise BenchmarkToolError(
            f"{task_id}.construction_inputs.review_campaign_status must be one of "
            f"{T4_REVIEW_CAMPAIGN_STATUSES}"
        )
    return value


def _validate_bound_task(
    task: Mapping[str, Any],
    *,
    root: Path,
    paper_id: str,
    paths: Mapping[str, Path],
    schema_validator: SchemaValidator,
) -> tuple[dict[str, Any], dict[str, str]]:
    task_id = f"{paper_id}-T4"
    _validate_identity(task, paper_id)
    construction = _construction_inputs(task, task_id)
    summary = schema_validator(task, label=task_id)
    hashes = _input_hashes(root, paths, task_id)
    for field, digest in hashes.items():
        if construction.get(field) != digest:
            raise BenchmarkToolError(
                f"{task_id}.construction_inputs.{field} does not match {paths[field]}"
            )
    validate_t4_file_bindings(root, task, task_id=task_id)
    return summary, hashes


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _atomic_replace_if_unchanged(
    path: Path,
    payload: bytes,
    *,
    expected_task: bytes,
    root: Path,
    input_paths: Mapping[str, Path],
    expected_hashes: Mapping[str, str],
    task_id: str,
) -> bool:
    if payload == expected_task:
        return False
    temporary = path.with_name(
        f".{path.name}.t4-metadata-{os.getpid()}-{uuid.uuid4().hex}"
    )
    destination_mode = stat.S_IMODE(path.stat().st_mode)
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, destination_mode)
        _regular_file(root, path, f"{task_id} task record")
        if path.read_bytes() != expected_task:
            raise BenchmarkToolError(
                f"{task_id} task record changed concurrently; retry freeze"
            )
        observed_hashes = _input_hashes(root, input_paths, task_id)
        if observed_hashes != expected_hashes:
            raise BenchmarkToolError(
                f"{task_id} construction inputs changed concurrently; retry freeze"
            )
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    except BaseException:
        if temporary.exists() and not temporary.is_symlink():
            temporary.unlink()
        raise
    return True


def manage_t4_metadata(
    benchmark_root: Path,
    paper_id: str,
    *,
    mode: str = "check",
    schema_validator: SchemaValidator = validate_task_source_tags,
) -> dict[str, Any]:
    """Manage only ``tasks/P0X/T4/task.json`` for one paper."""

    if mode not in MODES:
        raise BenchmarkToolError(f"unsupported T4 metadata mode: {mode!r}")
    _validate_paper_id(paper_id)
    root = _benchmark_root(benchmark_root)
    write_set = _write_set(paper_id)
    result: dict[str, Any] = {
        "ok": True,
        "mode": mode,
        "paper_id": paper_id,
        "task_id": f"{paper_id}-T4",
        "write_set": write_set,
        "written": [],
    }
    if mode == "write-set":
        return result

    paths = _paths(root, paper_id)
    task_path = paths["task"]
    task_id = f"{paper_id}-T4"
    _regular_file(root, task_path, f"{task_id} task record")
    task_payload, observed = _read_json_bytes(task_path, f"{task_id} task record")
    _validate_identity(observed, paper_id)

    if mode == "check":
        validation, hashes = _validate_bound_task(
            observed,
            root=root,
            paper_id=paper_id,
            paths=paths,
            schema_validator=schema_validator,
        )
        result["validation"] = validation
        result["construction_inputs"] = {
            **hashes,
            "review_campaign_status": observed["construction_inputs"][
                "review_campaign_status"
            ],
        }
        return result

    current = _construction_inputs(observed, task_id)
    status = current["review_campaign_status"]
    hashes = _input_hashes(root, paths, task_id)
    changed_hashes = [
        field for field, digest in hashes.items() if current.get(field) != digest
    ]
    if status == "accepted" and changed_hashes:
        raise BenchmarkToolError(
            f"{task_id} has an accepted review campaign; refusing to change "
            f"authenticated construction hashes {changed_hashes!r}"
        )

    prospective = copy.deepcopy(dict(observed))
    prospective["source_inventory_file"] = (
        f"paper_bencmark/highambench/tasks/{paper_id}/T4/source_inventory.json"
    )
    prospective["construction_inputs"] = {
        **hashes,
        "review_campaign_status": status,
    }
    validation, checked_hashes = _validate_bound_task(
        prospective,
        root=root,
        paper_id=paper_id,
        paths=paths,
        schema_validator=schema_validator,
    )
    changed = _atomic_replace_if_unchanged(
        task_path,
        _canonical_json_bytes(prospective),
        expected_task=task_payload,
        root=root,
        input_paths=paths,
        expected_hashes=checked_hashes,
        task_id=task_id,
    )
    if changed:
        result["written"] = [write_set[0]["path"]]
    result["validation"] = validation
    result["construction_inputs"] = prospective["construction_inputs"]
    return result


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=MODES)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--paper-id", required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = manage_t4_metadata(
            args.benchmark_root,
            args.paper_id,
            mode=args.mode,
        )
    except (BenchmarkToolError, OSError, ValueError) as error:
        print(f"t4-metadata error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
