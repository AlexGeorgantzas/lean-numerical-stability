#!/usr/bin/env python3
"""Finalize and discover independent HighamBench paper registrations.

Unlike ``refresh_snapshot.py``, this tool has no corpus-wide write path.  A
paper finalization may write only that paper's controlled manifests and its
single registration commit marker under ``metadata/papers/P0X``.  The
registration is deterministic, so corpus consumers can compose registrations
at read time without a later manifest merge.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from pathlib import PurePosixPath
import re
import sys
import tempfile
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json, sha256_file
    from .hashes import create_manifest
    from .task_tags import validate_t4_file_bindings, validate_task_source_tags
    from .validator import extract_imports, sanitize_lean
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file  # type: ignore
    from hashes import create_manifest  # type: ignore
    from task_tags import (  # type: ignore
        validate_t4_file_bindings,
        validate_task_source_tags,
    )
    from validator import extract_imports, sanitize_lean  # type: ignore


REGISTRATION_SCHEMA = "highambench-paper-registration-0.1"
CATALOG_SCHEMA = "highambench-paper-registration-catalog-0.1"
BUNDLE_SCHEMA = "highambench-paper-bundle-0.1"
CONSTRUCTION_EVIDENCE_SCHEMA = "highambench-paper-construction-evidence-0.1"
REVIEW_EVIDENCE_SCHEMA = "highambench-paper-review-evidence-0.1"
REGISTRATION_KIND = "highambench-paper-registration"
CATALOG_KIND = "highambench-paper-registration-catalog"
BUNDLE_KIND = "highambench-paper-bundle"
CONSTRUCTION_EVIDENCE_KIND = "highambench-paper-construction-evidence"
REVIEW_EVIDENCE_KIND = "highambench-paper-review-evidence"
PROJECT_BENCHMARK_PREFIX = PurePosixPath("paper_bencmark/highambench")

PAPER_ID_RE = re.compile(r"^P[0-9]+$")
TIER_RE = re.compile(r"^T[0-9]+$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
IMPORT_COMMAND_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\b[^\r\n]*$"
)
ALLOWED_DEFINITION_IMPORT_ROOTS = ("Mathlib", "Std", "Lean", "Batteries")
FORBIDDEN_LOCAL_IMPORT_ROOTS = ("HighamBench", "NumStability")


@dataclass(frozen=True)
class PaperRegistrationPlan:
    """One validated paper transaction, with repository-relative payloads."""

    paper_id: str
    registration: dict[str, Any]
    documents: tuple[tuple[str, bytes], ...]


def _canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _canonical_digest(value: Any) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _paper_sort_key(paper_id: str) -> tuple[int, str]:
    if PAPER_ID_RE.fullmatch(paper_id) is None:
        raise BenchmarkToolError(f"invalid paper id: {paper_id!r}")
    return (int(paper_id[1:]), paper_id)


def _tier_sort_key(tier: str) -> tuple[int, str]:
    if TIER_RE.fullmatch(tier) is None:
        raise BenchmarkToolError(f"invalid task tier: {tier!r}")
    return (int(tier[1:]), tier)


def _mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _regular_file(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"{label} must be a regular non-symlink file: {path}")
    return path


def _file_record(root: Path, path: Path) -> dict[str, Any]:
    path = _regular_file(path, "registered file")
    try:
        relative = path.resolve().relative_to(root).as_posix()
    except ValueError as error:
        raise BenchmarkToolError(f"registered file escapes benchmark root: {path}") from error
    return {
        "path": relative,
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
    }


def _payload_record(relative: str, payload: bytes) -> dict[str, Any]:
    return {
        "path": relative,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def _receipt_file_record(value: Any, label: str) -> dict[str, Any]:
    record = _mapping(value, label)
    path = record.get("path")
    digest = record.get("sha256")
    byte_count = record.get("bytes")
    if not isinstance(path, str) or not path:
        raise BenchmarkToolError(f"{label}.path must be a nonempty relative path")
    parsed = PurePosixPath(path)
    if parsed.is_absolute() or ".." in parsed.parts or parsed.as_posix() != path:
        raise BenchmarkToolError(f"{label}.path must be a canonical safe relative path")
    if not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None:
        raise BenchmarkToolError(f"{label}.sha256 must be a lowercase SHA-256 digest")
    if not isinstance(byte_count, int) or isinstance(byte_count, bool) or byte_count < 0:
        raise BenchmarkToolError(f"{label}.bytes must be a nonnegative integer")
    return {"path": path, "sha256": digest, "bytes": byte_count}


def _pending_artifact(path: str) -> dict[str, Any]:
    return {"status": "pending", "path": path}


def _validate_bundle_receipt(
    root: Path,
    *,
    paper_id: str,
    definition_source: Mapping[str, Any],
) -> dict[str, Any]:
    relative = f"metadata/papers/{paper_id}/bundle.json"
    path = root / relative
    if path.is_symlink():
        raise BenchmarkToolError(f"{paper_id} bundle receipt may not be a symlink")
    if not path.exists():
        return _pending_artifact(relative)
    path = _regular_file(path, f"{paper_id} bundle receipt")
    bundle = _mapping(read_json(path), f"{paper_id} bundle receipt")
    if (
        bundle.get("schema_version") != BUNDLE_SCHEMA
        or bundle.get("kind") != BUNDLE_KIND
        or bundle.get("paper_id") != paper_id
        or bundle.get("pass") is not True
    ):
        raise BenchmarkToolError(f"{paper_id} bundle receipt identity/pass is invalid")

    recorded_source = _receipt_file_record(
        bundle.get("definition_source"), f"{paper_id} bundle definition_source"
    )
    if recorded_source != dict(definition_source):
        raise BenchmarkToolError(
            f"{paper_id} bundle definition source hash/path/size disagrees with "
            f"{paper_id}Definitions.lean"
        )

    raw_oleans = bundle.get("olean_files")
    if not isinstance(raw_oleans, list) or len(raw_oleans) != 1:
        raise BenchmarkToolError(
            f"{paper_id} bundle must contain only {paper_id}Definitions.olean"
        )
    olean = _receipt_file_record(raw_oleans[0], f"{paper_id} bundle olean_files[0]")
    expected_olean = f"HighamBench/{paper_id}Definitions.olean"
    if olean["path"] != expected_olean:
        raise BenchmarkToolError(
            f"{paper_id} bundle must contain only {expected_olean}; "
            f"found {olean['path']}"
        )

    basis = {
        "paper_id": paper_id,
        "definition_source": recorded_source,
        "olean_files": [olean],
    }
    digest = bundle.get("bundle_sha256")
    if digest != _canonical_digest(basis):
        raise BenchmarkToolError(f"{paper_id} bundle_sha256 is stale or invalid")
    return {
        "status": "authenticated",
        "receipt": _file_record(root, path),
        "bundle_sha256": digest,
        "definition_source": recorded_source,
        "olean_files": [olean],
    }


def _validate_evidence_receipt(
    root: Path,
    *,
    paper_id: str,
    name: str,
    schema: str,
    kind: str,
    task_ids: Sequence[str],
    definition_source_sha256: str,
    paper_record_sha256: str,
    task_record_sha256: Mapping[str, str],
    controlled_manifest_sha256: Mapping[str, str],
    stale_bindings_are_pending: bool = False,
) -> dict[str, Any]:
    relative = f"metadata/papers/{paper_id}/{name}.json"
    path = root / relative
    if path.is_symlink():
        raise BenchmarkToolError(f"{paper_id} {name} evidence may not be a symlink")
    if not path.exists():
        return _pending_artifact(relative)
    path = _regular_file(path, f"{paper_id} {name} evidence")
    evidence = _mapping(read_json(path), f"{paper_id} {name} evidence")
    if (
        evidence.get("schema_version") != schema
        or evidence.get("kind") != kind
        or evidence.get("paper_id") != paper_id
        or evidence.get("pass") is not True
    ):
        raise BenchmarkToolError(f"{paper_id} {name} evidence identity/pass is invalid")

    recorded_task_ids = evidence.get("task_ids")
    if (
        not isinstance(recorded_task_ids, list)
        or any(not isinstance(task_id, str) or not task_id for task_id in recorded_task_ids)
        or len(recorded_task_ids) != len(set(recorded_task_ids))
    ):
        raise BenchmarkToolError(f"{paper_id} {name} evidence task_ids are invalid")
    recorded_definition_sha256 = evidence.get("definition_source_sha256")
    if (
        not isinstance(recorded_definition_sha256, str)
        or SHA256_RE.fullmatch(recorded_definition_sha256) is None
    ):
        raise BenchmarkToolError(
            f"{paper_id} {name} evidence definitions hash is invalid"
        )
    recorded_paper_sha256 = evidence.get("paper_record_sha256")
    if (
        not isinstance(recorded_paper_sha256, str)
        or SHA256_RE.fullmatch(recorded_paper_sha256) is None
    ):
        raise BenchmarkToolError(f"{paper_id} {name} evidence paper record is invalid")

    def recorded_digest_map(field: str) -> dict[str, str]:
        value = _mapping(
            evidence.get(field), f"{paper_id} {name} evidence {field}"
        )
        if set(value) != set(recorded_task_ids) or any(
            not isinstance(digest, str) or SHA256_RE.fullmatch(digest) is None
            for digest in value.values()
        ):
            raise BenchmarkToolError(
                f"{paper_id} {name} evidence {field} is invalid"
            )
        return {task_id: str(value[task_id]) for task_id in recorded_task_ids}

    recorded_task_sha256 = recorded_digest_map("task_record_sha256")
    recorded_manifest_sha256 = recorded_digest_map("controlled_manifest_sha256")

    artifact = {
        "status": "authenticated",
        "receipt": _file_record(root, path),
    }
    if name == "construction":
        certificate = _mapping(
            evidence.get("certificate"), f"{paper_id} construction certificate"
        )
        certificate_sha256 = evidence.get("certificate_sha256")
        if (
            not isinstance(certificate_sha256, str)
            or SHA256_RE.fullmatch(certificate_sha256) is None
            or certificate_sha256 != _canonical_digest(certificate)
        ):
            raise BenchmarkToolError(
                f"{paper_id} construction certificate digest is stale or invalid"
            )
        scope = _mapping(
            certificate.get("scope"), f"{paper_id} construction certificate scope"
        )
        if (
            certificate.get("schema_version") != 4
            or certificate.get("kind") != "highambench-private-construction-check"
            or certificate.get("pass") is not True
            or certificate.get("record_status") != "paper_current_final"
            or scope.get("scope_kind") != "paper-local"
            or scope.get("paper_id") != paper_id
            or scope.get("paper_record_sha256") != recorded_paper_sha256
            or scope.get("task_ids") != recorded_task_ids
            or scope.get("complete_paper_scope") is not True
        ):
            raise BenchmarkToolError(
                f"{paper_id} construction certificate is not a complete paper-local pass"
            )
        validation = _mapping(
            evidence.get("validation"), f"{paper_id} construction validation"
        )
        if (
            validation.get("paper_record_sha256") != recorded_paper_sha256
            or validation.get("controlled_manifest_sha256")
            != recorded_manifest_sha256
        ):
            raise BenchmarkToolError(
                f"{paper_id} construction validation bindings are stale"
            )
        artifact["certificate_sha256"] = certificate_sha256

    if recorded_task_ids != list(task_ids):
        if stale_bindings_are_pending:
            return _pending_artifact(relative)
        raise BenchmarkToolError(f"{paper_id} {name} evidence task_ids are stale")
    if recorded_definition_sha256 != definition_source_sha256:
        if stale_bindings_are_pending:
            return _pending_artifact(relative)
        raise BenchmarkToolError(
            f"{paper_id} {name} evidence definitions hash is stale"
        )
    if recorded_paper_sha256 != paper_record_sha256:
        if stale_bindings_are_pending:
            return _pending_artifact(relative)
        raise BenchmarkToolError(f"{paper_id} {name} evidence paper record is stale")
    if recorded_task_sha256 != dict(task_record_sha256):
        if stale_bindings_are_pending:
            return _pending_artifact(relative)
        raise BenchmarkToolError(f"{paper_id} {name} evidence task records are stale")
    expected_manifests = dict(controlled_manifest_sha256)
    if recorded_manifest_sha256 != expected_manifests:
        if stale_bindings_are_pending:
            return _pending_artifact(relative)
        raise BenchmarkToolError(
            f"{paper_id} {name} evidence controlled manifest hashes are stale"
        )
    return artifact


def _project_path(relative: str) -> str:
    return (PROJECT_BENCHMARK_PREFIX / PurePosixPath(relative)).as_posix()


def _normalize_benchmark_path(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise BenchmarkToolError(f"{label} must be a nonempty path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts:
        raise BenchmarkToolError(f"{label} must be a safe benchmark path")
    try:
        path = path.relative_to(PROJECT_BENCHMARK_PREFIX)
    except ValueError:
        pass
    return path.as_posix()


def _strict_imports(path: Path, *, label: str) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise BenchmarkToolError(f"cannot read {label}: {error}") from error
    sanitized = sanitize_lean(text, erase_strings=True)
    commands = IMPORT_COMMAND_RE.findall(sanitized)
    imports = extract_imports(text)
    if len(commands) != len(imports):
        raise BenchmarkToolError(f"{label} contains an unsupported import command")
    if len(imports) != len(set(imports)):
        raise BenchmarkToolError(f"{label} repeats an import")
    return imports


def _validate_definition_imports(path: Path, paper_id: str) -> list[str]:
    imports = _strict_imports(path, label=f"{paper_id} definitions")
    for module in imports:
        root = module.split(".", 1)[0]
        if root in FORBIDDEN_LOCAL_IMPORT_ROOTS:
            raise BenchmarkToolError(
                f"{paper_id}Definitions must be paper-independent; forbidden import {module}"
            )
        if root not in ALLOWED_DEFINITION_IMPORT_ROOTS:
            raise BenchmarkToolError(
                f"{paper_id}Definitions imports unsealed module {module}; "
                "only Lean/Std/Batteries/Mathlib roots are allowed"
            )
    return imports


def _task_directories(paper_root: Path) -> list[tuple[str, Path]]:
    result: list[tuple[str, Path]] = []
    for child in paper_root.iterdir():
        if child.name == "paper.json":
            continue
        if child.is_symlink():
            raise BenchmarkToolError(f"paper task entry may not be a symlink: {child}")
        if not child.is_dir() or TIER_RE.fullmatch(child.name) is None:
            raise BenchmarkToolError(
                f"paper root contains a non-task entry outside paper.json: {child.name}"
            )
        result.append((child.name, child))
    result.sort(key=lambda item: _tier_sort_key(item[0]))
    if not result:
        raise BenchmarkToolError(f"paper has no task directories: {paper_root}")
    return result


def _paper_owned_files(root: Path, paper_root: Path, definitions: Path) -> list[dict[str, Any]]:
    paths = [definitions]
    for path in paper_root.rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"paper-owned tree contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(f"paper-owned tree contains a special file: {path}")
        if path.suffix in (".olean", ".ilean") or path.name.startswith("."):
            raise BenchmarkToolError(f"paper-owned tree contains a generated/private file: {path}")
        paths.append(path)
    records = [_file_record(root, path) for path in sorted(set(paths))]
    records.sort(key=lambda item: str(item["path"]))
    return records


def _validate_t4_controlled_owners(
    task: Mapping[str, Any], *, paper_id: str, target_relative: str, definitions_relative: str
) -> None:
    if task.get("tier") != "T4":
        return
    allowed = {
        _project_path(target_relative),
        _project_path(definitions_relative),
    }
    declarations = task.get("declarations")
    if not isinstance(declarations, list):
        raise BenchmarkToolError(f"{paper_id}-T4 declarations must be a list")
    for index, raw in enumerate(declarations):
        if not isinstance(raw, Mapping):
            raise BenchmarkToolError(f"{paper_id}-T4 declaration {index} is invalid")
        owner = raw.get("controlled_source_file")
        if owner not in allowed:
            raise BenchmarkToolError(
                f"{paper_id}-T4 declaration {index} is owned by a cross-paper/shared "
                f"semantic file: {owner!r}"
            )


def _expected_output_relatives(paper_id: str, task_ids: Sequence[str]) -> set[str]:
    return {
        *(
            f"metadata/papers/{paper_id}/controlled/{task_id.removeprefix(f'{paper_id}-')}.json"
            for task_id in task_ids
        ),
        f"metadata/papers/{paper_id}/registration.json",
    }


def _reject_extra_controlled_manifests(
    root: Path, *, paper_id: str, expected_task_ids: Sequence[str]
) -> None:
    controlled = root / "metadata" / "papers" / paper_id / "controlled"
    if not controlled.exists():
        return
    if controlled.is_symlink() or not controlled.is_dir():
        raise BenchmarkToolError(
            f"{paper_id} controlled metadata must be a non-symlink directory"
        )
    expected = {
        f"{task_id.removeprefix(f'{paper_id}-')}.json"
        for task_id in expected_task_ids
    }
    actual: set[str] = set()
    for path in controlled.iterdir():
        if path.is_symlink() or not path.is_file():
            raise BenchmarkToolError(
                f"{paper_id} controlled metadata contains an unsafe entry: {path.name}"
            )
        actual.add(path.name)
    extras = sorted(actual - expected)
    if extras:
        raise BenchmarkToolError(
            f"{paper_id} has controlled manifests for unowned tasks: {', '.join(extras)}"
        )


def plan_paper_registration(
    benchmark_root: Path, paper_id: str
) -> PaperRegistrationPlan:
    """Validate one paper and return its deterministic, disjoint write plan."""

    _paper_sort_key(paper_id)
    root = Path(benchmark_root).resolve()
    if not root.is_dir():
        raise BenchmarkToolError(f"benchmark root is not a directory: {root}")

    agent_prompt = _regular_file(root / "agent_prompt.md", "agent prompt")
    paper_root = root / "tasks" / paper_id
    if paper_root.is_symlink() or not paper_root.is_dir():
        raise BenchmarkToolError(f"paper task root is missing or unsafe: {paper_root}")
    paper_path = _regular_file(paper_root / "paper.json", f"{paper_id} paper record")
    definitions_relative = f"shared/HighamBench/{paper_id}Definitions.lean"
    definitions_path = _regular_file(
        root / definitions_relative, f"{paper_id} definitions"
    )
    definition_imports = _validate_definition_imports(definitions_path, paper_id)
    definition_source = _file_record(root, definitions_path)

    paper = _mapping(read_json(paper_path), f"{paper_id} paper record")
    paper_record = _file_record(root, paper_path)
    if paper.get("paper_id") != paper_id:
        raise BenchmarkToolError(f"{paper_id} paper record has the wrong paper_id")
    paper_phase = paper.get("classification_frozen_before_runs")
    if not isinstance(paper_phase, bool):
        raise BenchmarkToolError(
            f"{paper_id} paper classification_frozen_before_runs must be boolean"
        )
    paper_metadata_root = root / "metadata" / "papers" / paper_id
    if paper_metadata_root.is_symlink() or (
        paper_metadata_root.exists() and not paper_metadata_root.is_dir()
    ):
        raise BenchmarkToolError(
            f"{paper_id} metadata root must be a non-symlink directory"
        )

    task_entries: list[dict[str, Any]] = []
    controlled_documents: list[tuple[str, bytes]] = []
    task_ids: list[str] = []
    expected_definition_module = f"HighamBench.{paper_id}Definitions"
    for tier, task_root in _task_directories(paper_root):
        task_id = f"{paper_id}-{tier}"
        target_relative = f"tasks/{paper_id}/{tier}/Target.lean"
        context_relative = f"tasks/{paper_id}/{tier}/context.md"
        task_relative = f"tasks/{paper_id}/{tier}/task.json"
        target_path = _regular_file(root / target_relative, f"{task_id} target")
        context_path = _regular_file(root / context_relative, f"{task_id} context")
        task_path = _regular_file(root / task_relative, f"{task_id} task record")
        task = _mapping(read_json(task_path), f"{task_id} task record")
        if (
            task.get("task_id") != task_id
            or task.get("paper_id") != paper_id
            or task.get("tier") != tier
        ):
            raise BenchmarkToolError(f"{task_id} identity disagrees with its path")
        validate_task_source_tags(task, label=task_id)
        if tier == "T4":
            validate_t4_file_bindings(root, task, task_id=task_id)
        if task.get("classification_frozen_before_runs") is not paper_phase:
            raise BenchmarkToolError(
                f"{task_id} readiness disagrees with {paper_id} paper.json"
            )
        if _normalize_benchmark_path(
            task.get("context_file"), f"{task_id}.context_file"
        ) != context_relative:
            raise BenchmarkToolError(f"{task_id} context_file disagrees with its path")

        target_imports = _strict_imports(target_path, label=f"{task_id} target")
        if target_imports != [expected_definition_module]:
            raise BenchmarkToolError(
                f"{task_id} must import exactly {expected_definition_module}; "
                f"found {target_imports}"
            )
        _validate_t4_controlled_owners(
            task,
            paper_id=paper_id,
            target_relative=target_relative,
            definitions_relative=definitions_relative,
        )

        controlled = create_manifest(
            root,
            requested=[
                "agent_prompt.md",
                definitions_relative,
                target_relative,
                context_relative,
            ],
            label=f"{task_id}-controlled",
        )
        controlled_relative = f"metadata/papers/{paper_id}/controlled/{tier}.json"
        controlled_payload = _canonical_json_bytes(controlled)
        controlled_documents.append((controlled_relative, controlled_payload))
        task_entries.append(
            {
                "task_id": task_id,
                "tier": tier,
                "target_imports": target_imports,
                "target": _file_record(root, target_path),
                "context": _file_record(root, context_path),
                "task_record": _file_record(root, task_path),
                "controlled_manifest": _payload_record(
                    controlled_relative, controlled_payload
                ),
            }
        )
        task_ids.append(task_id)

    if paper.get("included_tasks") != task_ids:
        raise BenchmarkToolError(
            f"{paper_id} paper.json included_tasks must exactly equal {task_ids}"
        )
    _reject_extra_controlled_manifests(
        root, paper_id=paper_id, expected_task_ids=task_ids
    )

    controlled_manifest_sha256 = {
        str(entry["task_id"]): str(entry["controlled_manifest"]["sha256"])
        for entry in task_entries
    }
    task_record_sha256 = {
        str(entry["task_id"]): str(entry["task_record"]["sha256"])
        for entry in task_entries
    }
    t4_task_ids = [
        str(entry["task_id"])
        for entry in task_entries
        if entry["tier"] == "T4"
    ]
    required_artifacts = ["bundle", "construction"]
    if t4_task_ids:
        required_artifacts.append("review")
    review_task_record_sha256 = {
        task_id: task_record_sha256[task_id] for task_id in t4_task_ids
    }
    review_manifest_sha256 = {
        task_id: controlled_manifest_sha256[task_id] for task_id in t4_task_ids
    }
    readiness_artifacts = {
        "bundle": _validate_bundle_receipt(
            root,
            paper_id=paper_id,
            definition_source=definition_source,
        ),
        "construction": _validate_evidence_receipt(
            root,
            paper_id=paper_id,
            name="construction",
            schema=CONSTRUCTION_EVIDENCE_SCHEMA,
            kind=CONSTRUCTION_EVIDENCE_KIND,
            task_ids=task_ids,
            definition_source_sha256=str(definition_source["sha256"]),
            paper_record_sha256=str(paper_record["sha256"]),
            task_record_sha256=task_record_sha256,
            controlled_manifest_sha256=controlled_manifest_sha256,
            stale_bindings_are_pending=not paper_phase,
        ),
        "review": (
            _validate_evidence_receipt(
                root,
                paper_id=paper_id,
                name="review",
                schema=REVIEW_EVIDENCE_SCHEMA,
                kind=REVIEW_EVIDENCE_KIND,
                task_ids=t4_task_ids,
                definition_source_sha256=str(definition_source["sha256"]),
                paper_record_sha256=str(paper_record["sha256"]),
                task_record_sha256=review_task_record_sha256,
                controlled_manifest_sha256=review_manifest_sha256,
                stale_bindings_are_pending=not paper_phase,
            )
            if t4_task_ids
            else {
                "status": "not-applicable",
                "reason": "faithfulness review evidence is required only for T4",
                "task_ids": [],
            }
        ),
    }
    readiness_policy = {
        "required_artifacts": required_artifacts,
        "review_required_for_tiers": ["T4"],
        "review_task_ids": t4_task_ids,
    }
    if paper_phase:
        pending = [
            name
            for name in required_artifacts
            if readiness_artifacts[name]["status"] != "authenticated"
        ]
        if pending:
            raise BenchmarkToolError(
                f"{paper_id} is marked measurement-ready but lacks authenticated "
                f"paper-local artifacts: {', '.join(pending)}"
            )

    paper_owned_files = _paper_owned_files(root, paper_root, definitions_path)
    shared_inputs = [_file_record(root, agent_prompt)]
    content_basis = {
        "paper_id": paper_id,
        "phase": "measurement-ready" if paper_phase else "construction",
        "definition_module": expected_definition_module,
        "definition_imports": definition_imports,
        "paper_owned_files": paper_owned_files,
        "shared_inputs": shared_inputs,
        "readiness_policy": readiness_policy,
        "readiness_artifacts": readiness_artifacts,
        "controlled_manifests": [
            entry["controlled_manifest"] for entry in task_entries
        ],
    }
    registration_relative = f"metadata/papers/{paper_id}/registration.json"
    registration = {
        "schema_version": REGISTRATION_SCHEMA,
        "kind": REGISTRATION_KIND,
        "paper_id": paper_id,
        "phase": content_basis["phase"],
        "registration_path": registration_relative,
        "publication_contract": {
            "scope": "paper-local",
            "registration_replaced_last": True,
            "corpus_aggregate_required": False,
        },
        "ownership": {
            "task_root": f"tasks/{paper_id}",
            "definition_module": expected_definition_module,
            "definition_source": definitions_relative,
            "custom_import_closure": [expected_definition_module],
            "cross_paper_imports_allowed": False,
            "core_or_semantic_core_imports_allowed": False,
        },
        "definition_imports": definition_imports,
        "definition_source": definition_source,
        "paper_record": paper_record,
        "paper_owned_files": paper_owned_files,
        "shared_inputs": shared_inputs,
        "readiness_policy": readiness_policy,
        "readiness_artifacts": readiness_artifacts,
        "tasks": task_entries,
        "task_ids": task_ids,
        "paper_snapshot_sha256": _canonical_digest(content_basis),
    }
    registration_payload = _canonical_json_bytes(registration)
    documents = tuple(
        sorted(controlled_documents, key=lambda item: item[0])
        + [(registration_relative, registration_payload)]
    )
    expected_outputs = _expected_output_relatives(paper_id, task_ids)
    if {relative for relative, _payload in documents} != expected_outputs:
        raise BenchmarkToolError("internal paper registration write-scope mismatch")
    return PaperRegistrationPlan(
        paper_id=paper_id,
        registration=registration,
        documents=documents,
    )


def _write_set(root: Path, plan: PaperRegistrationPlan) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for relative, payload in plan.documents:
        path = root / relative
        if path.is_symlink() or (path.exists() and not path.is_file()):
            raise BenchmarkToolError(f"registration output is unsafe: {path}")
        state = "missing"
        if path.is_file():
            state = "unchanged" if path.read_bytes() == payload else "replace"
        result.append({**_payload_record(relative, payload), "state": state})
    return result


def _stage_payload(destination: Path, payload: bytes) -> Path:
    with tempfile.NamedTemporaryFile(
        prefix=f".{destination.name}.paper-registry-",
        dir=destination.parent,
        delete=False,
    ) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    os.chmod(temporary, 0o644)
    return temporary


def _publish(root: Path, plan: PaperRegistrationPlan) -> list[str]:
    expected = _expected_output_relatives(
        plan.paper_id, plan.registration["task_ids"]
    )
    if {relative for relative, _payload in plan.documents} != expected:
        raise BenchmarkToolError("refusing an out-of-scope paper registration write")

    changed = [
        (relative, payload)
        for relative, payload in plan.documents
        if not (root / relative).is_file() or (root / relative).read_bytes() != payload
    ]
    if not changed:
        return []

    registration_relative = str(plan.registration["registration_path"])
    changed.sort(key=lambda item: (item[0] == registration_relative, item[0]))
    staged: dict[str, Path] = {}
    backups: dict[str, bytes | None] = {}
    replaced: list[str] = []
    try:
        for relative, payload in changed:
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            if destination.parent.is_symlink():
                raise BenchmarkToolError(
                    f"registration output parent may not be a symlink: {destination.parent}"
                )
            if destination.is_symlink() or (
                destination.exists() and not destination.is_file()
            ):
                raise BenchmarkToolError(f"registration output is unsafe: {destination}")
            backups[relative] = destination.read_bytes() if destination.is_file() else None
            staged[relative] = _stage_payload(destination, payload)

        for relative, _payload in changed:
            destination = root / relative
            os.replace(staged[relative], destination)
            replaced.append(relative)
        for parent in {str((root / relative).parent) for relative in replaced}:
            descriptor = os.open(parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
    except Exception as error:
        rollback_errors: list[str] = []
        for relative in reversed(replaced):
            destination = root / relative
            try:
                backup = backups[relative]
                if backup is None:
                    destination.unlink(missing_ok=True)
                else:
                    temporary = _stage_payload(destination, backup)
                    os.replace(temporary, destination)
            except OSError as rollback_error:
                rollback_errors.append(f"{relative}: {rollback_error}")
        if rollback_errors:
            raise BenchmarkToolError(
                "paper registration failed and rollback was incomplete: "
                + "; ".join(rollback_errors)
            ) from error
        if isinstance(error, BenchmarkToolError):
            raise
        raise BenchmarkToolError(f"paper registration failed: {error}") from error
    finally:
        for temporary in staged.values():
            temporary.unlink(missing_ok=True)
    return replaced


def finalize_paper(
    benchmark_root: Path, paper_id: str, *, mode: str = "write"
) -> dict[str, Any]:
    """Plan, check, or publish one paper without touching corpus-global files."""

    if mode not in ("write", "check", "dry-run", "write-set"):
        raise BenchmarkToolError(f"unknown paper finalization mode: {mode}")
    root = Path(benchmark_root).resolve()
    plan = plan_paper_registration(root, paper_id)
    write_set = _write_set(root, plan)
    if mode == "check":
        stale = [item for item in write_set if item["state"] != "unchanged"]
        if stale:
            raise BenchmarkToolError(
                f"{paper_id} registration is missing or stale: "
                + ", ".join(str(item["path"]) for item in stale)
            )
        written: list[str] = []
    elif mode in ("dry-run", "write-set"):
        written = []
    else:
        written = _publish(root, plan)
        # The registration is the commit marker.  Re-plan after publication so
        # a source edit racing finalization cannot be reported as successful.
        checked = plan_paper_registration(root, paper_id)
        if checked.documents != plan.documents:
            raise BenchmarkToolError(
                f"{paper_id} source changed while its registration was published"
            )
        post = _write_set(root, checked)
        if any(item["state"] != "unchanged" for item in post):
            raise BenchmarkToolError(f"{paper_id} registration did not publish exactly")
    return {
        "ok": True,
        "mode": mode,
        "paper_id": paper_id,
        "paper_snapshot_sha256": plan.registration["paper_snapshot_sha256"],
        "task_ids": list(plan.registration["task_ids"]),
        "write_set": write_set,
        "written": written,
    }


def _load_registration(root: Path, path: Path, *, verify: bool) -> dict[str, Any]:
    registration = _mapping(read_json(path), f"paper registration {path}")
    paper_id = path.parent.name
    _paper_sort_key(paper_id)
    if (
        registration.get("schema_version") != REGISTRATION_SCHEMA
        or registration.get("kind") != REGISTRATION_KIND
        or registration.get("paper_id") != paper_id
        or registration.get("registration_path")
        != f"metadata/papers/{paper_id}/registration.json"
    ):
        raise BenchmarkToolError(f"invalid paper registration identity: {path}")
    if verify:
        plan = plan_paper_registration(root, paper_id)
        expected = dict(plan.documents)[registration["registration_path"]]
        if path.read_bytes() != expected:
            raise BenchmarkToolError(f"paper registration is stale: {path}")
        for relative, payload in plan.documents:
            output = root / relative
            if output.is_symlink() or not output.is_file() or output.read_bytes() != payload:
                raise BenchmarkToolError(
                    f"paper registration output is missing or stale: {relative}"
                )
    return registration


def discover_paper_registrations(
    benchmark_root: Path, *, verify: bool = True
) -> list[dict[str, Any]]:
    """Discover valid paper shards in stable numeric paper order."""

    root = Path(benchmark_root).resolve()
    papers_root = root / "metadata" / "papers"
    if not papers_root.exists():
        return []
    if papers_root.is_symlink() or not papers_root.is_dir():
        raise BenchmarkToolError("metadata/papers must be a non-symlink directory")
    paths = list(papers_root.glob("P*/registration.json"))
    paths.sort(key=lambda path: _paper_sort_key(path.parent.name))
    seen: set[str] = set()
    registrations: list[dict[str, Any]] = []
    for path in paths:
        paper_id = path.parent.name
        if paper_id in seen:
            raise BenchmarkToolError(f"duplicate paper registration: {paper_id}")
        seen.add(paper_id)
        registrations.append(_load_registration(root, path, verify=verify))
    return registrations


def compose_registration_catalog(
    benchmark_root: Path, *, verify: bool = True
) -> dict[str, Any]:
    """Compose a deterministic virtual corpus without writing an aggregate."""

    root = Path(benchmark_root).resolve()
    registrations = discover_paper_registrations(root, verify=verify)
    members: list[dict[str, Any]] = []
    task_ids: list[str] = []
    for registration in registrations:
        paper_id = str(registration["paper_id"])
        relative = f"metadata/papers/{paper_id}/registration.json"
        path = _regular_file(root / relative, f"{paper_id} registration")
        member_tasks = registration.get("task_ids")
        if not isinstance(member_tasks, list) or not all(
            isinstance(task_id, str) for task_id in member_tasks
        ):
            raise BenchmarkToolError(f"{paper_id} registration task_ids are invalid")
        members.append(
            {
                "paper_id": paper_id,
                "registration": _file_record(root, path),
                "paper_snapshot_sha256": registration["paper_snapshot_sha256"],
                "phase": registration["phase"],
                "task_ids": list(member_tasks),
            }
        )
        task_ids.extend(member_tasks)
    basis = {
        "schema_version": CATALOG_SCHEMA,
        "kind": CATALOG_KIND,
        "members": members,
    }
    return {
        **basis,
        "paper_ids": [member["paper_id"] for member in members],
        "task_ids": task_ids,
        "paper_count": len(members),
        "task_count": len(task_ids),
        "all_measurement_ready": bool(members)
        and all(member["phase"] == "measurement-ready" for member in members),
        "catalog_sha256": _canonical_digest(basis),
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--paper-id")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true")
    modes.add_argument("--dry-run", action="store_true")
    modes.add_argument(
        "--write-set",
        action="store_true",
        help="validate and print the exact paper-local write set without writing",
    )
    modes.add_argument(
        "--discover",
        action="store_true",
        help="compose all current registrations at read time without writing",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        if args.discover:
            if args.paper_id is not None:
                raise BenchmarkToolError("--discover does not accept --paper-id")
            result = compose_registration_catalog(args.benchmark_root)
        else:
            if args.paper_id is None:
                raise BenchmarkToolError("--paper-id is required")
            mode = (
                "check"
                if args.check
                else "dry-run"
                if args.dry_run
                else "write-set"
                if args.write_set
                else "write"
            )
            result = finalize_paper(args.benchmark_root, args.paper_id, mode=mode)
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"paper-registry error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
