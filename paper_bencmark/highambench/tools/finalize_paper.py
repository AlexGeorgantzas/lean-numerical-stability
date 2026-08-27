#!/usr/bin/env python3
"""Build and register one independent HighamBench paper.

This is the user-facing paper finalizer.  It compiles only
``HighamBench.P0XDefinitions``, publishes an exact one-file trusted bundle,
then delegates the paper-local registration transaction to
``paper_registry``.  It has no corpus-wide write path.

A construction-phase registration may truthfully record readiness gates as
pending; it is a draft state, not proof of completion.  ``--dry-run`` and
``--write-set`` compile and shadow-plan only in a unique system temporary
directory that is removed on return.  They create no benchmark or scratch-pad
outputs.
"""

from __future__ import annotations

import argparse
import contextlib
from dataclasses import dataclass
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Callable, Iterator, Mapping, Sequence
import uuid

try:
    from .common import BenchmarkToolError, read_json, sha256_file
    from . import paper_registry
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file  # type: ignore
    import paper_registry  # type: ignore


BUNDLE_SCHEMA = paper_registry.BUNDLE_SCHEMA
BUNDLE_KIND = paper_registry.BUNDLE_KIND
PAPER_ID_RE = re.compile(r"^P[0-9]+$")
PHASES = ("construction", "measurement-ready")
MODES = ("write", "check", "dry-run", "write-set")
CompilerRunner = Callable[
    [Sequence[str], Path, Mapping[str, str]], subprocess.CompletedProcess[str]
]


@dataclass(frozen=True)
class BundlePaths:
    source: Path
    current_root: Path
    current_olean: Path
    retired_root: Path
    receipt: Path
    lock: Path


def _canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _canonical_digest(value: Any) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _regular_file(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"{label} must be a regular non-symlink file: {path}")
    return path


def _file_record(path: Path, relative: str) -> dict[str, Any]:
    _regular_file(path, relative)
    return {
        "path": relative,
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
    }


def _validate_paper_id(paper_id: str) -> None:
    if PAPER_ID_RE.fullmatch(paper_id) is None:
        raise BenchmarkToolError(f"invalid paper id: {paper_id!r}")


def _resolve_project_root(benchmark_root: Path, requested: Path | None) -> Path:
    root = benchmark_root.resolve()
    if requested is not None:
        candidates = [requested.resolve()]
    else:
        candidates = [root, *root.parents]
    for candidate in candidates:
        lakefile = candidate / "lakefile.toml"
        lakefile_lean = candidate / "lakefile.lean"
        if (
            (lakefile.is_file() or lakefile_lean.is_file())
            and (candidate / "lean-toolchain").is_file()
            and (candidate / "lake-manifest.json").is_file()
        ):
            try:
                root.relative_to(candidate)
            except ValueError as error:
                raise BenchmarkToolError(
                    f"benchmark root {root} is outside project root {candidate}"
                ) from error
            return candidate
    if requested is not None:
        raise BenchmarkToolError(
            f"project root lacks lakefile, lean-toolchain, or lake-manifest.json: "
            f"{candidates[0]}"
        )
    raise BenchmarkToolError(
        f"could not derive pinned Lean project root from benchmark root {root}"
    )


def _toolchain_snapshot(
    project_root: Path, benchmark_root: Path
) -> tuple[tuple[str, str, int], ...]:
    tool_root = Path(__file__).resolve().parent
    candidates = [
        project_root / "lean-toolchain",
        project_root / "lake-manifest.json",
        project_root / "lakefile.toml",
        project_root / "lakefile.lean",
        benchmark_root / "agent_prompt.md",
        Path(__file__).resolve(),
        Path(paper_registry.__file__).resolve(),
        tool_root / "common.py",
        tool_root / "hashes.py",
        tool_root / "task_tags.py",
        tool_root / "validator.py",
    ]
    records: list[tuple[str, str, int]] = []
    for path in candidates:
        if path.name in ("lakefile.toml", "lakefile.lean") and not path.exists():
            continue
        _regular_file(path, "frozen toolchain input")
        try:
            relative = path.relative_to(project_root).as_posix()
        except ValueError:
            relative = str(path)
        records.append((relative, sha256_file(path), path.stat().st_size))
    return tuple(sorted(records))


def _bundle_paths(benchmark_root: Path, paper_id: str) -> BundlePaths:
    scratch = benchmark_root.parent / "scratch_pad" / "highambench_environment"
    current_root = scratch / "shared_olean" / paper_id
    return BundlePaths(
        source=(
            benchmark_root
            / "shared"
            / "HighamBench"
            / f"{paper_id}Definitions.lean"
        ),
        current_root=current_root,
        current_olean=(
            current_root / "HighamBench" / f"{paper_id}Definitions.olean"
        ),
        retired_root=scratch / "retired_shared_olean" / paper_id,
        receipt=benchmark_root / "metadata" / "papers" / paper_id / "bundle.json",
        lock=scratch / "finalizer_locks" / paper_id / "lock",
    )


def _default_compiler_runner(
    command: Sequence[str], cwd: Path, env: Mapping[str, str]
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            list(command),
            cwd=cwd,
            env=dict(env),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=600,
        )
    except FileNotFoundError as error:
        raise BenchmarkToolError(f"cannot run pinned Lean compiler: {error}") from error
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        raise BenchmarkToolError(
            "P0XDefinitions compilation exceeded 600 seconds"
            + (f":\n{output[-4000:]}" if output else "")
        ) from error


def _compiler_environment() -> dict[str, str]:
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(name, None)
    env["LC_ALL"] = "C.UTF-8"
    env["LANG"] = "C.UTF-8"
    return env


def _compile_definitions(
    *,
    project_root: Path,
    paths: BundlePaths,
    paper_id: str,
    temporary_root: Path,
    compiler_runner: CompilerRunner,
) -> Path:
    output = temporary_root / "HighamBench" / f"{paper_id}Definitions.olean"
    output.parent.mkdir(parents=True)
    command = [
        "lake",
        "env",
        "lean",
        "-o",
        str(output),
        str(paths.source),
    ]
    try:
        result = compiler_runner(command, project_root, _compiler_environment())
    except BenchmarkToolError:
        raise
    except (OSError, subprocess.SubprocessError) as error:
        raise BenchmarkToolError(f"P0XDefinitions compiler failed: {error}") from error
    if result.returncode != 0:
        raw_output = result.stdout or ""
        if isinstance(raw_output, bytes):
            raw_output = raw_output.decode("utf-8", errors="replace")
        suffix = f":\n{raw_output[-4000:]}" if raw_output else ""
        raise BenchmarkToolError(
            f"{paper_id}Definitions failed to compile (exit {result.returncode}){suffix}"
        )
    _regular_file(output, f"compiled {paper_id} definitions")
    generated = sorted(
        path.relative_to(temporary_root).as_posix()
        for path in temporary_root.rglob("*")
        if path.is_file() or path.is_symlink()
    )
    expected = [f"HighamBench/{paper_id}Definitions.olean"]
    if generated != expected:
        raise BenchmarkToolError(
            f"compiler produced files outside the one-file {paper_id} bundle: {generated}"
        )
    return output


def _make_bundle_receipt(
    *, paper_id: str, source: Path, compiled_olean: Path
) -> dict[str, Any]:
    source_record = _file_record(
        source, f"shared/HighamBench/{paper_id}Definitions.lean"
    )
    olean_record = _file_record(
        compiled_olean, f"HighamBench/{paper_id}Definitions.olean"
    )
    basis = {
        "paper_id": paper_id,
        "definition_source": source_record,
        "olean_files": [olean_record],
    }
    return {
        "schema_version": BUNDLE_SCHEMA,
        "kind": BUNDLE_KIND,
        "paper_id": paper_id,
        "pass": True,
        "definition_source": source_record,
        "olean_files": [olean_record],
        "bundle_sha256": _canonical_digest(basis),
    }


def _tree_manifest(root: Path) -> list[dict[str, Any]]:
    if root.is_symlink() or not root.is_dir():
        raise BenchmarkToolError(f"bundle root must be a non-symlink directory: {root}")
    records: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise BenchmarkToolError(f"bundle tree contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(f"bundle tree contains a special file: {path}")
        records.append(
            {
                "path": path.relative_to(root).as_posix(),
                "sha256": sha256_file(path),
                "bytes": path.stat().st_size,
            }
        )
    return records


def _tree_digest(root: Path) -> str:
    return _canonical_digest({"files": _tree_manifest(root)})


def _bundle_state(paths: BundlePaths, receipt: Mapping[str, Any]) -> str:
    if paths.current_root.is_symlink():
        raise BenchmarkToolError(
            f"bundle root may not be a symlink: {paths.current_root}"
        )
    if not paths.current_root.exists():
        return "missing"
    files = _tree_manifest(paths.current_root)
    expected = list(receipt["olean_files"])
    return "unchanged" if files == expected else "replace"


def _receipt_state(path: Path, payload: bytes) -> str:
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise BenchmarkToolError(f"bundle receipt output is unsafe: {path}")
    if not path.exists():
        return "missing"
    return "unchanged" if path.read_bytes() == payload else "replace"


def _project_relative(project_root: Path, path: Path) -> str:
    try:
        return path.relative_to(project_root).as_posix()
    except ValueError as error:
        raise BenchmarkToolError(f"paper-local output escapes project root: {path}") from error


def _atomic_write(path: Path, payload: bytes) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.parent.is_symlink():
        raise BenchmarkToolError(f"output parent may not be a symlink: {path.parent}")
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise BenchmarkToolError(f"output is unsafe: {path}")
    if path.is_file() and path.read_bytes() == payload:
        return False
    with tempfile.NamedTemporaryFile(
        prefix=f".{path.name}.finalizer-", dir=path.parent, delete=False
    ) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    try:
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
        descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)
    return True


def _publish_bundle(
    *,
    paths: BundlePaths,
    paper_id: str,
    compiled_olean: Path,
    receipt: Mapping[str, Any],
) -> tuple[bool, Path | None]:
    state = _bundle_state(paths, receipt)
    if state == "unchanged":
        return False, None

    bundle_parent = paths.current_root.parent
    bundle_parent.mkdir(parents=True, exist_ok=True)
    if bundle_parent.is_symlink():
        raise BenchmarkToolError(f"bundle parent may not be a symlink: {bundle_parent}")
    staging = Path(
        tempfile.mkdtemp(prefix=f".{paper_id}.bundle-stage-", dir=bundle_parent)
    )
    staged_olean = staging / "HighamBench" / f"{paper_id}Definitions.olean"
    staged_olean.parent.mkdir(parents=True)
    shutil.copyfile(compiled_olean, staged_olean)
    os.chmod(staged_olean, 0o644)
    with staged_olean.open("rb") as stream:
        os.fsync(stream.fileno())
    if _tree_manifest(staging) != list(receipt["olean_files"]):
        shutil.rmtree(staging)
        raise BenchmarkToolError(f"staged {paper_id} bundle disagrees with its receipt")

    archived: Path | None = None
    archive_created = False
    previous_location: Path | None = None
    duplicate_previous = False
    published = False
    try:
        if paths.current_root.exists():
            digest = _tree_digest(paths.current_root)
            archived = paths.retired_root / digest
            paths.retired_root.mkdir(parents=True, exist_ok=True)
            if paths.retired_root.is_symlink():
                raise BenchmarkToolError(
                    f"retired bundle root may not be a symlink: {paths.retired_root}"
                )
            if archived.is_symlink():
                raise BenchmarkToolError(
                    f"retired bundle may not be a symlink: {archived}"
                )
            if archived.exists():
                if _tree_digest(archived) != digest:
                    raise BenchmarkToolError(
                        f"content-addressed retired bundle is inconsistent: {archived}"
                    )
                previous_location = bundle_parent / (
                    f".{paper_id}.previous-{uuid.uuid4().hex}"
                )
                os.replace(paths.current_root, previous_location)
                duplicate_previous = True
            else:
                os.replace(paths.current_root, archived)
                previous_location = archived
                archive_created = True
        os.replace(staging, paths.current_root)
        published = True
        descriptor = os.open(bundle_parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    except Exception:
        if published and paths.current_root.exists():
            failed = bundle_parent / f".{paper_id}.failed-{uuid.uuid4().hex}"
            os.replace(paths.current_root, failed)
            shutil.rmtree(failed)
        if previous_location is not None and previous_location.exists():
            os.replace(previous_location, paths.current_root)
            if not duplicate_previous:
                archived = None
                archive_created = False
        raise
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    if duplicate_previous and previous_location is not None:
        shutil.rmtree(previous_location)
    return True, archived if archive_created else None


def _copy_regular_file(source: Path, destination: Path) -> None:
    _regular_file(source, "shadow preflight input")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source.read_bytes())


def _copy_regular_tree(source: Path, destination: Path) -> None:
    if source.is_symlink() or not source.is_dir():
        raise BenchmarkToolError(f"shadow preflight source is unsafe: {source}")
    for path in sorted(source.rglob("*")):
        if path.is_symlink():
            raise BenchmarkToolError(f"shadow preflight source contains a symlink: {path}")
        relative = path.relative_to(source)
        if path.is_dir():
            (destination / relative).mkdir(parents=True, exist_ok=True)
        elif path.is_file():
            _copy_regular_file(path, destination / relative)
        else:
            raise BenchmarkToolError(
                f"shadow preflight source contains a special file: {path}"
            )


def _prospective_registration_plan(
    *,
    benchmark_root: Path,
    paper_id: str,
    receipt_payload: bytes,
    compiled_olean: Path,
    temporary_parent: Path,
) -> Any:
    shadow = temporary_parent / "shadow" / "highambench"
    _copy_regular_file(benchmark_root / "agent_prompt.md", shadow / "agent_prompt.md")
    _copy_regular_file(
        benchmark_root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean",
        shadow / "shared" / "HighamBench" / f"{paper_id}Definitions.lean",
    )
    _copy_regular_tree(
        benchmark_root / "tasks" / paper_id, shadow / "tasks" / paper_id
    )

    paper_metadata = benchmark_root / "metadata" / "papers" / paper_id
    if paper_metadata.exists():
        if paper_metadata.is_symlink() or not paper_metadata.is_dir():
            raise BenchmarkToolError(f"paper metadata root is unsafe: {paper_metadata}")
        for path in sorted(paper_metadata.rglob("*")):
            if path.is_symlink():
                raise BenchmarkToolError(f"paper metadata contains a symlink: {path}")
            if path.is_dir():
                continue
            if not path.is_file():
                raise BenchmarkToolError(f"paper metadata contains a special file: {path}")
            relative = path.relative_to(paper_metadata)
            if relative.as_posix() in ("bundle.json", "registration.json"):
                continue
            _copy_regular_file(path, shadow / "metadata" / "papers" / paper_id / relative)

    shadow_receipt = shadow / "metadata" / "papers" / paper_id / "bundle.json"
    shadow_receipt.parent.mkdir(parents=True, exist_ok=True)
    shadow_receipt.write_bytes(receipt_payload)
    shadow_olean = (
        shadow.parent
        / "scratch_pad"
        / "highambench_environment"
        / "shared_olean"
        / paper_id
        / "HighamBench"
        / f"{paper_id}Definitions.olean"
    )
    shadow_olean.parent.mkdir(parents=True, exist_ok=True)
    shadow_olean.write_bytes(compiled_olean.read_bytes())

    plan = paper_registry.plan_paper_registration(shadow, paper_id)
    allowed_prefix = f"metadata/papers/{paper_id}/"
    out_of_scope = [
        relative
        for relative, _payload in plan.documents
        if not relative.startswith(allowed_prefix)
    ]
    if out_of_scope:
        raise BenchmarkToolError(
            "paper registry proposed corpus-wide or cross-paper writes: "
            + ", ".join(out_of_scope)
        )
    return plan


def _phase(benchmark_root: Path, paper_id: str) -> str:
    paper_path = benchmark_root / "tasks" / paper_id / "paper.json"
    paper = read_json(_regular_file(paper_path, f"{paper_id} paper record"))
    if not isinstance(paper, dict) or paper.get("paper_id") != paper_id:
        raise BenchmarkToolError(f"{paper_id} paper record identity is invalid")
    frozen = paper.get("classification_frozen_before_runs")
    if not isinstance(frozen, bool):
        raise BenchmarkToolError(
            f"{paper_id} classification_frozen_before_runs must be boolean"
        )
    return "measurement-ready" if frozen else "construction"


def _planned_registry_write_set(
    benchmark_root: Path, plan: Any
) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for relative, payload in plan.documents:
        path = benchmark_root / relative
        if path.is_symlink() or (path.exists() and not path.is_file()):
            raise BenchmarkToolError(f"registration output is unsafe: {path}")
        state = "missing"
        if path.is_file():
            state = "unchanged" if path.read_bytes() == payload else "replace"
        result.append(
            {
                "path": relative,
                "sha256": hashlib.sha256(payload).hexdigest(),
                "bytes": len(payload),
                "state": state,
            }
        )
    return result


@contextlib.contextmanager
def _paper_lock(path: Path) -> Iterator[None]:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.parent.is_symlink():
        raise BenchmarkToolError(f"paper lock parent may not be a symlink: {path.parent}")
    with path.open("a+b") as stream:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def finalize_paper(
    benchmark_root: Path,
    paper_id: str,
    *,
    phase: str,
    project_root: Path | None = None,
    mode: str = "write",
    compiler_runner: CompilerRunner | None = None,
) -> dict[str, Any]:
    """Compile, check, or publish one paper's bundle and registration."""

    _validate_paper_id(paper_id)
    if phase not in PHASES:
        raise BenchmarkToolError(f"invalid paper phase: {phase!r}")
    if mode not in MODES:
        raise BenchmarkToolError(f"invalid finalizer mode: {mode!r}")
    raw_root = Path(benchmark_root)
    if raw_root.is_symlink() or not raw_root.is_dir():
        raise BenchmarkToolError(
            f"benchmark root must be a non-symlink directory: {raw_root}"
        )
    root = raw_root.resolve()
    project = _resolve_project_root(root, project_root)
    paths = _bundle_paths(root, paper_id)
    _regular_file(paths.source, f"{paper_id} definitions")
    actual_phase = _phase(root, paper_id)
    if phase != actual_phase:
        raise BenchmarkToolError(
            f"requested phase {phase!r} disagrees with {paper_id} paper phase "
            f"{actual_phase!r}"
        )

    toolchain_before = _toolchain_snapshot(project, root)
    source_before = _file_record(
        paths.source, f"shared/HighamBench/{paper_id}Definitions.lean"
    )
    runner = compiler_runner or _default_compiler_runner
    with tempfile.TemporaryDirectory(prefix=f"highambench-{paper_id}-finalize-") as raw:
        temporary = Path(raw)
        compiled = _compile_definitions(
            project_root=project,
            paths=paths,
            paper_id=paper_id,
            temporary_root=temporary / "compiled",
            compiler_runner=runner,
        )
        source_after = _file_record(
            paths.source, f"shared/HighamBench/{paper_id}Definitions.lean"
        )
        if source_after != source_before:
            raise BenchmarkToolError(
                f"{paper_id}Definitions changed while its bundle was compiling"
            )
        if _toolchain_snapshot(project, root) != toolchain_before:
            raise BenchmarkToolError("pinned Lean or finalizer inputs changed during compilation")

        receipt = _make_bundle_receipt(
            paper_id=paper_id, source=paths.source, compiled_olean=compiled
        )
        receipt_payload = _canonical_json_bytes(receipt)
        registration_plan = _prospective_registration_plan(
            benchmark_root=root,
            paper_id=paper_id,
            receipt_payload=receipt_payload,
            compiled_olean=compiled,
            temporary_parent=temporary,
        )
        if registration_plan.registration.get("phase") != phase:
            raise BenchmarkToolError(
                f"paper registry phase disagrees with requested phase {phase}"
            )

        bundle_state = _bundle_state(paths, receipt)
        receipt_state = _receipt_state(paths.receipt, receipt_payload)
        bundle_record = {
            **receipt["olean_files"][0],
            "path": _project_relative(project, paths.current_olean),
            "state": bundle_state,
        }
        receipt_record = {
            "path": paths.receipt.relative_to(root).as_posix(),
            "sha256": hashlib.sha256(receipt_payload).hexdigest(),
            "bytes": len(receipt_payload),
            "state": receipt_state,
        }
        registry_write_set = _planned_registry_write_set(root, registration_plan)
        write_set: list[dict[str, Any]] = [bundle_record, receipt_record]
        archive_preview: Path | None = None
        if bundle_state == "replace":
            archive_preview = paths.retired_root / _tree_digest(paths.current_root)
            write_set.append(
                {
                    "path": _project_relative(project, archive_preview),
                    "tree_sha256": archive_preview.name,
                    "state": "unchanged" if archive_preview.exists() else "archive",
                }
            )
        write_set.extend(registry_write_set)

        if mode in ("dry-run", "write-set"):
            return {
                "ok": True,
                "mode": mode,
                "paper_id": paper_id,
                "phase": phase,
                "bundle_sha256": receipt["bundle_sha256"],
                "paper_snapshot_sha256": registration_plan.registration[
                    "paper_snapshot_sha256"
                ],
                "write_set": write_set,
                "written": [],
            }

        if mode == "check":
            stale = [
                item
                for item in (bundle_record, receipt_record)
                if item["state"] != "unchanged"
            ]
            if stale:
                raise BenchmarkToolError(
                    f"{paper_id} bundle is missing or stale: "
                    + ", ".join(str(item["path"]) for item in stale)
                )
            result = paper_registry.finalize_paper(root, paper_id, mode="check")
            return {
                "ok": True,
                "mode": mode,
                "paper_id": paper_id,
                "phase": phase,
                "bundle_sha256": receipt["bundle_sha256"],
                "paper_snapshot_sha256": result["paper_snapshot_sha256"],
                "write_set": write_set,
                "written": [],
            }

        with _paper_lock(paths.lock):
            if _file_record(
                paths.source, f"shared/HighamBench/{paper_id}Definitions.lean"
            ) != source_before:
                raise BenchmarkToolError(
                    f"{paper_id}Definitions changed before bundle publication"
                )
            if _toolchain_snapshot(project, root) != toolchain_before:
                raise BenchmarkToolError(
                    "pinned Lean or finalizer inputs changed before publication"
                )
            bundle_changed, archived = _publish_bundle(
                paths=paths,
                paper_id=paper_id,
                compiled_olean=compiled,
                receipt=receipt,
            )
            receipt_changed = _atomic_write(paths.receipt, receipt_payload)
            registration_result = paper_registry.finalize_paper(
                root, paper_id, mode="write"
            )

        written: list[str] = []
        if bundle_changed:
            written.append(_project_relative(project, paths.current_olean))
        if archived is not None:
            written.append(_project_relative(project, archived))
        if receipt_changed:
            written.append(paths.receipt.relative_to(root).as_posix())
        for relative in registration_result.get("written", []):
            if not str(relative).startswith(f"metadata/papers/{paper_id}/"):
                raise BenchmarkToolError(
                    f"paper registry reported an out-of-scope write: {relative}"
                )
            written.append(str(relative))
        return {
            "ok": True,
            "mode": mode,
            "paper_id": paper_id,
            "phase": phase,
            "bundle_sha256": receipt["bundle_sha256"],
            "paper_snapshot_sha256": registration_result["paper_snapshot_sha256"],
            "write_set": write_set,
            "written": written,
        }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--project-root", type=Path)
    parser.add_argument("--paper-id", required=True)
    parser.add_argument("--phase", choices=PHASES, required=True)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true")
    modes.add_argument(
        "--dry-run",
        action="store_true",
        help=(
            "compile and shadow-plan in an automatically removed system temporary "
            "directory; do not create or change any benchmark or scratch-pad output"
        ),
    )
    modes.add_argument(
        "--write-set",
        action="store_true",
        help="compile and print the exact paper-local prospective write set",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    mode = (
        "check"
        if args.check
        else "dry-run"
        if args.dry_run
        else "write-set"
        if args.write_set
        else "write"
    )
    try:
        result = finalize_paper(
            args.benchmark_root,
            args.paper_id,
            phase=args.phase,
            project_root=args.project_root,
            mode=mode,
        )
    except (BenchmarkToolError, OSError, ValueError) as error:
        print(f"paper-finalizer error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
