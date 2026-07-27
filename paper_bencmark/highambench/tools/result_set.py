#!/usr/bin/env python3
"""Validate a complete HighamBench result matrix before final analysis.

The runner deliberately handles one run at a time.  This module performs the
cross-run checks that a one-run validator cannot perform: the planned matrix is
complete, N/L order is respected, paired metadata agrees, system-error reruns
are resolved, and every final record matches the frozen benchmark metadata.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import platform
import sys
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, FAILURE_CODES, SCHEMA_VERSION, read_json, sha256_file, write_json
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        FAILURE_CODES,
        SCHEMA_VERSION,
        read_json,
        sha256_file,
        write_json,
    )


AgentKey = tuple[str, str, str]
AssignmentKey = tuple[str, str, str]

PROTOCOL_CLAIMS = (
    "fresh_conversation",
    "filesystem_isolated",
    "network_disabled",
    "backend_seed_supplied",
    "seed_enforced_by_agent",
    "token_limit_enforced_by_agent",
    "condition_l_library_available",
)
PROTOCOL_VERIFICATIONS = (
    "fresh_workspace_copy",
    "condition_n_preflight",
    "condition_n_import_probe_complete",
    "network_violation_marker_integrity",
)
# These controls depend on features supplied by the chosen model backend or
# adapter.  A complete pilot may be reported as observational when they are not
# available.  Isolation and condition-separation failures are never relaxed.
OBSERVATIONAL_CONTROL_CLAIMS = {
    "backend_seed_supplied",
    "seed_enforced_by_agent",
    "token_limit_enforced_by_agent",
}
ENVIRONMENT_BUNDLE_DEFINITION = (
    "SHA-256 of UTF-8 canonical JSON with sorted keys and compact separators over an "
    "object containing the complete config and environment records, after removing "
    "environment_id and environment_bundle_sha256 from their top-level/frozen locations."
)
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)


def _package_runtime_file_kind(relative: str) -> str | None:
    if relative == "mathlib/Mathlib.lean" or (
        relative.startswith("mathlib/Mathlib/") and relative.endswith(".lean")
    ):
        return "source"
    if "/.lake/build/lib/lean/" not in relative:
        return None
    if relative.endswith(".olean"):
        return "olean"
    if relative.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES):
        return "compiled_support"
    return None


def _agent_key(run: Mapping[str, Any]) -> AgentKey:
    agent = run.get("agent")
    if not isinstance(agent, Mapping):
        return ("unknown", "unknown", "unknown")
    return (
        str(agent.get("id", "unknown")),
        str(agent.get("version", "unknown")),
        str(agent.get("model", "unknown")),
    )


def _assignment_key(run: Mapping[str, Any]) -> AssignmentKey | None:
    task = run.get("task_id")
    repetition = run.get("repetition_id")
    condition = run.get("condition")
    if not isinstance(task, str) or not isinstance(repetition, str) or condition not in ("N", "L"):
        return None
    return task, repetition, condition


def _hex_digest(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(
        character in "0123456789abcdef" for character in value
    )


def _iso_time(value: Any) -> dt.datetime | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=dt.timezone.utc)
    return parsed


def _document_digest(value: Mapping[str, Any]) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _environment_bundle_digest(
    config: Mapping[str, Any], environment: Mapping[str, Any]
) -> str:
    config_copy = json.loads(json.dumps(config))
    environment_copy = json.loads(json.dumps(environment))
    frozen = config_copy.get("frozen_environment")
    if isinstance(frozen, dict):
        frozen.pop("environment_id", None)
        frozen.pop("environment_bundle_sha256", None)
    environment_copy.pop("environment_id", None)
    environment_copy.pop("environment_bundle_sha256", None)
    return _document_digest({"config": config_copy, "environment": environment_copy})


def _contains_text(value: Any, needle: str) -> bool:
    if isinstance(value, str):
        return needle.lower() in value.lower()
    if isinstance(value, Mapping):
        return any(
            _contains_text(key, needle) or _contains_text(item, needle)
            for key, item in value.items()
        )
    if isinstance(value, list):
        return any(_contains_text(item, needle) for item in value)
    return False


def _metadata_tasks(manifest: Mapping[str, Any], errors: list[str]) -> dict[str, dict[str, Any]]:
    tasks: dict[str, dict[str, Any]] = {}
    papers = manifest.get("papers")
    if not isinstance(papers, list) or not papers:
        errors.append("manifest has no papers")
        return tasks
    for paper in papers:
        if not isinstance(paper, Mapping):
            errors.append("manifest contains a non-object paper entry")
            continue
        paper_id = paper.get("paper_id")
        source = paper.get("source")
        paper_digest = source.get("sha256") if isinstance(source, Mapping) else None
        if not isinstance(paper_id, str) or not _hex_digest(paper_digest):
            errors.append(f"manifest paper has invalid id or source hash: {paper_id!r}")
            continue
        targets = paper.get("targets")
        if not isinstance(targets, list) or not targets:
            errors.append(f"manifest paper {paper_id} has no targets")
            continue
        for target in targets:
            if not isinstance(target, Mapping):
                errors.append(f"manifest paper {paper_id} contains a non-object target")
                continue
            task_id = target.get("task_id")
            tier = target.get("tier")
            if not isinstance(task_id, str) or tier not in ("T1", "T2", "T3"):
                errors.append(f"manifest contains invalid task id or tier: {task_id!r}/{tier!r}")
                continue
            if task_id in tasks:
                errors.append(f"manifest repeats task {task_id}")
                continue
            tasks[task_id] = {
                "paper_id": paper_id,
                "paper_sha256": paper_digest,
                "tier": tier,
            }
    return tasks


def _repetitions(config: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    repetitions = config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        errors.append("config has no repetitions")
        return result
    for repetition in repetitions:
        if not isinstance(repetition, Mapping) or not isinstance(repetition.get("id"), str):
            errors.append("config contains an invalid repetition entry")
            continue
        repetition_id = repetition["id"]
        if repetition_id in result:
            errors.append(f"config repeats repetition {repetition_id}")
            continue
        result[repetition_id] = repetition.get("backend_seed")
    return result


def _expected_assignments(
    run_order: Mapping[str, Any],
    tasks: Mapping[str, Mapping[str, Any]],
    repetitions: Mapping[str, Any],
    errors: list[str],
) -> tuple[dict[AssignmentKey, dict[str, Any]], dict[str, dict[str, Any]]]:
    expected: dict[AssignmentKey, dict[str, Any]] = {}
    pairs_by_id: dict[str, dict[str, Any]] = {}
    planned_run_ids: set[str] = set()
    pairs = run_order.get("pairs")
    if not isinstance(pairs, list):
        errors.append("run-order document has no pairs list")
        return expected, pairs_by_id
    method = run_order.get("method")
    salt = method.get("salt") if isinstance(method, Mapping) else None
    method_name = method.get("name") if isinstance(method, Mapping) else None
    if method_name != "sha256_first_byte_parity" or not isinstance(salt, str) or not salt:
        errors.append(
            "run-order method must be sha256_first_byte_parity with a nonempty salt"
        )
    for pair in pairs:
        if not isinstance(pair, Mapping):
            errors.append("run-order contains a non-object pair")
            continue
        pair_id = pair.get("pair_id")
        task_id = pair.get("task_id")
        repetition_id = pair.get("repetition_id")
        order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if not all(isinstance(value, str) for value in (pair_id, task_id, repetition_id)):
            errors.append(f"run-order contains an invalid pair identity: {pair!r}")
            continue
        if pair_id in pairs_by_id:
            errors.append(f"run-order repeats pair {pair_id}")
            continue
        identity_is_known = True
        if task_id not in tasks:
            errors.append(f"run-order pair {pair_id} names unknown task {task_id}")
            identity_is_known = False
        if repetition_id not in repetitions:
            errors.append(f"run-order pair {pair_id} names unknown repetition {repetition_id}")
            identity_is_known = False
        if order not in (["N", "L"], ["L", "N"]):
            errors.append(f"run-order pair {pair_id} does not contain one N and one L in order")
            continue
        if not isinstance(run_ids, list) or len(run_ids) != 2 or not all(
            isinstance(run_id, str) and run_id for run_id in run_ids
        ):
            errors.append(f"run-order pair {pair_id} has invalid run_ids")
            continue
        if len(set(run_ids)) != 2:
            errors.append(f"run-order pair {pair_id} repeats a run id")
        for run_id in run_ids:
            if run_id in planned_run_ids:
                errors.append(f"run-order repeats planned run id {run_id}")
            planned_run_ids.add(run_id)
        digest = pair.get("sha256")
        if method_name == "sha256_first_byte_parity" and isinstance(salt, str):
            key = f"{salt}|{task_id}|{repetition_id}"
            actual_digest = hashlib.sha256(key.encode("utf-8")).hexdigest()
            actual_order = ["N", "L"] if int(actual_digest[:2], 16) % 2 == 0 else ["L", "N"]
            if digest != actual_digest:
                errors.append(f"run-order pair {pair_id} has the wrong SHA-256")
            if order != actual_order:
                errors.append(f"run-order pair {pair_id} does not follow its SHA-256 order rule")
        pair_order = "N-first" if order[0] == "N" else "L-first"
        pair_record = {
            "pair_id": pair_id,
            "task_id": task_id,
            "repetition_id": repetition_id,
            "condition_order": list(order),
            "run_ids": list(run_ids),
            "pair_order": pair_order,
        }
        pairs_by_id[pair_id] = pair_record
        if not identity_is_known:
            continue
        for index, condition in enumerate(order):
            assignment = (task_id, repetition_id, condition)
            if assignment in expected:
                errors.append(
                    f"run-order repeats assignment {task_id}/{repetition_id}/{condition}"
                )
                continue
            expected[assignment] = {
                **pair_record,
                "condition": condition,
                "run_id": run_ids[index],
                "order_index": index + 1,
                "backend_seed": repetitions.get(repetition_id),
            }
    matrix = {
        (task_id, repetition_id, condition)
        for task_id in tasks
        for repetition_id in repetitions
        for condition in ("N", "L")
    }
    missing = sorted(matrix - set(expected))
    extra = sorted(set(expected) - matrix)
    for assignment in missing:
        errors.append("run-order misses assignment " + "/".join(assignment))
    for assignment in extra:
        errors.append("run-order has extra assignment " + "/".join(assignment))
    return expected, pairs_by_id


def _metadata_readiness(
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
    *,
    repository_root: Path | None,
    allow_observational_unscored: bool,
) -> tuple[list[str], list[str], list[dict[str, Any]], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    verified_hashes: list[dict[str, Any]] = []
    nonreference_reasons: list[str] = []
    frozen = config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        errors.append("config has no frozen_environment object")
        frozen = {}
    for field in (
        "lean_toolchain",
        "lean_commit",
        "lean_binary_sha256",
        "mathlib_commit",
        "numstability_commit",
        "agent_id",
        "agent_version",
        "agent_binary_sha256",
        "model_version",
        "model_reasoning_effort",
        "prompt_sha256",
        "allowed_tools",
        "hardware_class",
        "operating_system",
        "environment_id",
        "environment_bundle_sha256",
        "bubblewrap_binary_sha256",
        "bubblewrap_version",
        "numstability_source_manifest",
        "numstability_source_manifest_sha256",
        "numstability_compiled_manifest",
        "numstability_compiled_manifest_sha256",
        "compiled_environment_summary",
        "compiled_environment_summary_sha256",
        "packages_runtime_manifest",
        "packages_runtime_manifest_sha256",
        "python_version",
        "python_binary_sha256",
        "release_manifest",
        "release_manifest_sha256",
    ):
        value = frozen.get(field)
        if value is None or value == "" or value == []:
            errors.append(f"frozen environment field {field} is not fixed")
    container_digest = frozen.get("container_image_digest")
    bubblewrap_recorded = _contains_text(config.get("isolation"), "bubblewrap")
    if container_digest is None or container_digest == "":
        if bubblewrap_recorded:
            reason = (
                "no frozen OCI/container image digest; runs use recorded bubblewrap namespace "
                "isolation (the model shell is offline while the Codex control process keeps "
                "its provider connection)"
            )
            nonreference_reasons.append(reason)
            if not allow_observational_unscored:
                errors.append(reason)
        else:
            errors.append(
                "frozen environment has neither a container image digest nor an explicit "
                "bubblewrap isolation record"
            )
    for field in (
        "prompt_sha256",
        "agent_binary_sha256",
        "environment_bundle_sha256",
        "lean_binary_sha256",
        "bubblewrap_binary_sha256",
        "numstability_source_manifest_sha256",
        "numstability_compiled_manifest_sha256",
        "compiled_environment_summary_sha256",
        "packages_runtime_manifest_sha256",
        "python_binary_sha256",
        "release_manifest_sha256",
    ):
        digest = frozen.get(field)
        if digest is not None and not _hex_digest(digest):
            errors.append(f"frozen {field} is not a lowercase SHA-256")
    environment_id = frozen.get("environment_id")
    bundle_digest = frozen.get("environment_bundle_sha256")
    if (
        isinstance(environment_id, str)
        and _hex_digest(bundle_digest)
        and environment_id != f"highambench-p01-{bundle_digest[:16]}"
    ):
        errors.append("frozen environment_id is not derived from environment_bundle_sha256")
    for field in ("mathlib_commit", "numstability_commit"):
        commit = frozen.get(field)
        if commit is not None and (
            not isinstance(commit, str)
            or len(commit) != 40
            or any(character not in "0123456789abcdef" for character in commit)
        ):
            errors.append(f"frozen {field} is not a full lowercase Git commit hash")

    current_python_version = platform.python_version()
    frozen_python_version = frozen.get("python_version")
    if frozen_python_version != current_python_version:
        errors.append(
            f"current Python version {current_python_version!r} does not match "
            f"frozen {frozen_python_version!r}"
        )
    python_path = Path(sys.executable).resolve()
    python_record: dict[str, Any] = {
        "label": "current Python executable",
        "path": "<current sys.executable>",
        "expected_sha256": frozen.get("python_binary_sha256"),
    }
    if not python_path.is_file():
        errors.append("current sys.executable is not a readable regular file")
        python_record["match"] = False
    else:
        actual_python_digest = sha256_file(python_path)
        python_record["actual_sha256"] = actual_python_digest
        python_record["match"] = actual_python_digest == frozen.get(
            "python_binary_sha256"
        )
        if python_record["match"] is not True:
            errors.append("current Python executable does not match its frozen SHA-256")
    verified_hashes.append(python_record)

    hash_records: list[tuple[str, Any, Any]] = []
    hash_records.extend(
        [
            (
                "NumStability source manifest",
                frozen.get("numstability_source_manifest"),
                frozen.get("numstability_source_manifest_sha256"),
            ),
            (
                "NumStability compiled manifest",
                frozen.get("numstability_compiled_manifest"),
                frozen.get("numstability_compiled_manifest_sha256"),
            ),
            (
                "compiled environment summary",
                frozen.get("compiled_environment_summary"),
                frozen.get("compiled_environment_summary_sha256"),
            ),
            (
                "packages runtime manifest",
                frozen.get("packages_runtime_manifest"),
                frozen.get("packages_runtime_manifest_sha256"),
            ),
            (
                "evaluation release manifest",
                frozen.get("release_manifest"),
                frozen.get("release_manifest_sha256"),
            ),
        ]
    )
    specification = manifest.get("specification")
    if isinstance(specification, Mapping):
        hash_records.append(
            ("specification", specification.get("local_path"), specification.get("sha256"))
        )
    else:
        errors.append("manifest has no specification object")
    target_count = 0
    for paper in manifest.get("papers", []) if isinstance(manifest.get("papers"), list) else []:
        if not isinstance(paper, Mapping):
            continue
        source = paper.get("source")
        if isinstance(source, Mapping):
            hash_records.append(
                (f"paper {paper.get('paper_id')}", source.get("local_path"), source.get("sha256"))
            )
        for target in paper.get("targets", []) if isinstance(paper.get("targets"), list) else []:
            if not isinstance(target, Mapping):
                continue
            target_count += 1
            lean_target = target.get("lean_target")
            if isinstance(lean_target, Mapping):
                hash_records.append(
                    (
                        f"target {target.get('task_id')}",
                        lean_target.get("file"),
                        lean_target.get("controlled_file_sha256"),
                    )
                )
            else:
                errors.append(f"target {target.get('task_id')} has no lean_target object")
    shared = manifest.get("controlled_shared_files")
    if isinstance(shared, list) and shared:
        for entry in shared:
            if isinstance(entry, Mapping):
                hash_records.append(
                    (f"shared file {entry.get('path')}", entry.get("path"), entry.get("sha256"))
                )
            else:
                errors.append("manifest contains a non-object controlled shared file")
    else:
        errors.append("manifest has no controlled_shared_files entries")
    if target_count == 0:
        errors.append("manifest has no controlled target files")
    for label, raw_path, digest in hash_records:
        if not isinstance(raw_path, str) or not raw_path:
            errors.append(f"{label} has no fixed file path")
        if not _hex_digest(digest):
            errors.append(f"{label} has no fixed lowercase SHA-256")
            continue
        record = {"label": label, "path": raw_path, "expected_sha256": digest}
        if repository_root is not None and isinstance(raw_path, str):
            path = (repository_root / raw_path).resolve()
            try:
                path.relative_to(repository_root.resolve())
            except ValueError:
                errors.append(f"{label} path escapes repository root: {raw_path}")
                continue
            if not path.is_file():
                errors.append(f"{label} file is missing: {raw_path}")
                continue
            actual = sha256_file(path)
            record["actual_sha256"] = actual
            record["match"] = actual == digest
            if actual != digest:
                errors.append(f"{label} does not match its recorded SHA-256")
        else:
            record["match"] = None
            if repository_root is None:
                warnings.append(f"{label} hash syntax checked but file content was not re-read")
        verified_hashes.append(record)
    return errors, warnings, verified_hashes, nonreference_reasons


def _check_planned_metadata(
    run: Mapping[str, Any],
    expected: Mapping[str, Any],
    task: Mapping[str, Any],
    errors: list[str],
    *,
    require_planned_run_id: bool,
) -> None:
    label = str(run.get("run_id") or expected["run_id"])
    exact = {
        "pair_id": expected["pair_id"],
        "task_id": expected["task_id"],
        "paper_id": task["paper_id"],
        "paper_sha256": task["paper_sha256"],
        "tier": task["tier"],
        "condition": expected["condition"],
        "repetition_id": expected["repetition_id"],
        "backend_seed": expected["backend_seed"],
        "pair_order": expected["pair_order"],
        "order_index": expected["order_index"],
    }
    if require_planned_run_id:
        exact["run_id"] = expected["run_id"]
    for field, wanted in exact.items():
        if run.get(field) != wanted:
            errors.append(
                f"run {label} has {field}={run.get(field)!r}; expected {wanted!r}"
            )


def _check_frozen_run_evidence(
    runs: Sequence[Mapping[str, Any]],
    *,
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
    run_order: Mapping[str, Any],
    repository_root: Path | None,
    errors: list[str],
    warnings: list[str],
) -> str | None:
    frozen = config.get("frozen_environment")
    frozen = frozen if isinstance(frozen, Mapping) else {}
    expected_metadata = {
        "config": _document_digest(config),
        "manifest": _document_digest(manifest),
        "run_order": _document_digest(run_order),
    }
    environment: Mapping[str, Any] | None = None
    expected_release_file_count: int | None = None
    expected_source_file_count: int | None = None
    expected_compiled_file_count: int | None = None
    expected_runtime_file_count: int | None = None
    expected_runtime_counts: dict[str, int] | None = None
    expected_compiled_counts: dict[str, int] | None = None
    if repository_root is not None:
        environment_path = (
            repository_root.resolve()
            / "paper_bencmark"
            / "highambench"
            / "metadata"
            / "environment.json"
        )
        if not environment_path.is_file():
            errors.append(f"frozen environment record is missing: {environment_path}")
        else:
            try:
                raw_environment = read_json(environment_path)
            except BenchmarkToolError as error:
                errors.append(str(error))
                raw_environment = None
            if not isinstance(raw_environment, Mapping):
                errors.append("frozen environment record is not a JSON object")
            else:
                environment = raw_environment
                expected_metadata["environment"] = _document_digest(environment)
                if environment.get("environment_bundle_definition") != ENVIRONMENT_BUNDLE_DEFINITION:
                    errors.append("environment record names the wrong canonical bundle algorithm")
                bundle = _environment_bundle_digest(config, environment)
                if bundle != frozen.get("environment_bundle_sha256"):
                    errors.append("current config/environment canonical bundle digest is stale")
                if environment.get("environment_bundle_sha256") != bundle:
                    errors.append("environment record stores the wrong canonical bundle digest")
                if environment.get("environment_id") != frozen.get("environment_id"):
                    errors.append("environment_id disagrees between config and environment record")
                if environment.get("release_manifest_sha256") != frozen.get(
                    "release_manifest_sha256"
                ):
                    errors.append("release manifest SHA-256 disagrees across frozen metadata")
                runtime_record = environment.get("runtime")
                python_record = (
                    runtime_record.get("python")
                    if isinstance(runtime_record, Mapping)
                    else None
                )
                if not isinstance(python_record, Mapping) or (
                    python_record.get("version") != frozen.get("python_version")
                    or python_record.get("binary_sha256")
                    != frozen.get("python_binary_sha256")
                ):
                    errors.append("Python identity disagrees across frozen metadata")
                if not isinstance(runtime_record, Mapping) or (
                    runtime_record.get("packages_runtime_manifest")
                    != frozen.get("packages_runtime_manifest")
                    or runtime_record.get("packages_runtime_manifest_sha256")
                    != frozen.get("packages_runtime_manifest_sha256")
                ):
                    errors.append(
                        "packages runtime manifest disagrees across frozen metadata"
                    )
        for field, count_name in (
            ("release_manifest", "release"),
            ("numstability_source_manifest", "source"),
            ("numstability_compiled_manifest", "compiled"),
            ("packages_runtime_manifest", "runtime"),
        ):
            raw_path = frozen.get(field)
            if not isinstance(raw_path, str):
                continue
            path = (repository_root.resolve() / raw_path).resolve()
            try:
                path.relative_to(repository_root.resolve())
            except ValueError:
                continue
            if not path.is_file():
                continue
            try:
                value = read_json(path)
            except BenchmarkToolError as error:
                errors.append(str(error))
                continue
            files = value.get("files") if isinstance(value, Mapping) else None
            if not isinstance(files, list):
                continue
            if count_name == "release":
                expected_release_file_count = len(files)
            elif count_name == "source":
                expected_source_file_count = len(files)
            elif count_name == "compiled":
                expected_compiled_file_count = len(files)
            else:
                expected_runtime_file_count = len(files)
                counts = {"source": 0, "olean": 0, "compiled_support": 0}
                invalid_paths: list[str] = []
                for entry in files:
                    relative = entry.get("path") if isinstance(entry, Mapping) else None
                    kind = (
                        _package_runtime_file_kind(relative)
                        if isinstance(relative, str)
                        else None
                    )
                    if kind is None:
                        invalid_paths.append(str(relative))
                    else:
                        counts[kind] += 1
                if invalid_paths:
                    errors.append(
                        "packages runtime manifest contains files outside its exact "
                        "source/compiled projection: " + ", ".join(invalid_paths[:8])
                    )
                else:
                    expected_runtime_counts = counts
        compiled_path_raw = frozen.get("compiled_environment_summary")
        if isinstance(compiled_path_raw, str):
            compiled_path = (repository_root.resolve() / compiled_path_raw).resolve()
            if compiled_path.is_file():
                try:
                    compiled_value = read_json(compiled_path)
                except BenchmarkToolError as error:
                    errors.append(str(error))
                    compiled_value = None
                toolchain = (
                    compiled_value.get("toolchain")
                    if isinstance(compiled_value, Mapping)
                    else None
                )
                packages = (
                    compiled_value.get("packages")
                    if isinstance(compiled_value, Mapping)
                    else None
                )
                if (
                    isinstance(toolchain, Mapping)
                    and isinstance(toolchain.get("file_count"), int)
                    and isinstance(packages, list)
                    and all(
                        isinstance(item, Mapping)
                        and isinstance(item.get("file_count"), int)
                        for item in packages
                    )
                ):
                    expected_compiled_counts = {
                        "toolchain_file_count": toolchain.get("file_count"),
                        "package_count": len(packages),
                        "package_file_count": sum(
                            item.get("file_count", 0) for item in packages
                        ),
                    }
    else:
        warnings.append(
            "freeze evidence syntax was checked, but environment.json was not re-read "
            "because no repository root was supplied"
        )

    evidence_digests: set[str] = set()
    for index, run in enumerate(runs):
        label = str(run.get("run_id") or f"input record {index}")
        wrapper = run.get("frozen_run_verification")
        if not isinstance(wrapper, Mapping):
            errors.append(f"run {label} lacks mandatory frozen-run verification evidence")
            continue
        check = wrapper.get("freeze_check")
        recorded_digest = wrapper.get("freeze_check_sha256")
        if not isinstance(check, Mapping):
            errors.append(f"run {label} has no embedded freeze_check object")
            continue
        actual_digest = _document_digest(check)
        if recorded_digest != actual_digest:
            errors.append(f"run {label} has a stale or altered freeze_check digest")
        else:
            evidence_digests.add(actual_digest)
        if (
            check.get("schema_version") != SCHEMA_VERSION
            or check.get("kind") != "highambench-frozen-run-verification"
            or check.get("ok") is not True
        ):
            errors.append(f"run {label} does not cite a successful supported freeze check")
        for field, wanted in (
            ("benchmark_id", config.get("benchmark_id")),
            ("environment_id", frozen.get("environment_id")),
            ("environment_bundle_sha256", frozen.get("environment_bundle_sha256")),
        ):
            if check.get(field) != wanted:
                errors.append(f"run {label} freeze check has the wrong {field}")
        release = check.get("release_manifest")
        if not isinstance(release, Mapping) or release.get("sha256") != frozen.get(
            "release_manifest_sha256"
        ):
            errors.append(f"run {label} freeze check has the wrong release manifest identity")
        elif (
            not isinstance(release.get("file_count"), int)
            or release.get("file_count") <= 0
            or not isinstance(release.get("verification"), Mapping)
            or release["verification"].get("ok") is not True
            or release["verification"].get("verified")
            != release["verification"].get("expected")
            or release["verification"].get("missing") != []
            or release["verification"].get("changed") != []
        ):
            errors.append(f"run {label} freeze check lacks a complete release verification")
        elif (
            expected_release_file_count is not None
            and (
                release.get("file_count") != expected_release_file_count
                or release["verification"].get("expected") != expected_release_file_count
            )
        ):
            errors.append(f"run {label} freeze check has the wrong release file count")

        agent = check.get("agent")
        expected_agent = {
            "id": frozen.get("agent_id"),
            "version": frozen.get("agent_version"),
            "binary_sha256": frozen.get("agent_binary_sha256"),
            "model": frozen.get("model_version"),
            "reasoning_effort": frozen.get("model_reasoning_effort"),
        }
        if not isinstance(agent, Mapping) or any(
            agent.get(field) != wanted for field, wanted in expected_agent.items()
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong agent identity")

        python_check = check.get("python")
        if not isinstance(python_check, Mapping) or (
            python_check.get("version") != frozen.get("python_version")
            or python_check.get("binary_sha256")
            != frozen.get("python_binary_sha256")
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong Python identity")

        limits_record = config.get("limits")
        token_control = check.get("token_control")
        expected_token_limit = (
            limits_record.get("total_model_tokens")
            if isinstance(limits_record, Mapping)
            else None
        )
        if not isinstance(token_control, Mapping) or (
            token_control.get("feature") != "rollout_budget"
            or not isinstance(token_control.get("feature_row"), str)
            or not token_control.get("feature_row", "").startswith("rollout_budget ")
            or token_control.get("strict_config") is not True
            or token_control.get("limit_tokens") != expected_token_limit
            or token_control.get("prefill_token_weight") != 1
            or token_control.get("sampling_token_weight") != 1
        ):
            errors.append(f"run {label} freeze check has invalid token-control evidence")

        lean_check = check.get("lean")
        expected_lean_version = (
            str(frozen.get("lean_toolchain")).rsplit(":v", 1)[-1]
            if isinstance(frozen.get("lean_toolchain"), str)
            else None
        )
        expected_lean = {
            "version": expected_lean_version,
            "commit": frozen.get("lean_commit"),
            "binary_sha256": frozen.get("lean_binary_sha256"),
            "mathlib_commit": frozen.get("mathlib_commit"),
            "numstability_commit": frozen.get("numstability_commit"),
        }
        if not isinstance(lean_check, Mapping) or any(
            lean_check.get(field) != wanted for field, wanted in expected_lean.items()
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong Lean identity")
        elif any(
            not isinstance(lean_check.get(field), int)
            or isinstance(lean_check.get(field), bool)
            or lean_check.get(field) <= 0
            for field in ("compiled_files_verified", "source_files_verified")
        ):
            errors.append(f"run {label} freeze check has invalid library file counts")
        elif (
            expected_source_file_count is not None
            and lean_check.get("source_files_verified") != expected_source_file_count
        ) or (
            expected_compiled_file_count is not None
            and lean_check.get("compiled_files_verified") != expected_compiled_file_count
        ):
            errors.append(f"run {label} freeze check has stale library file counts")

        limits = config.get("limits")
        expected_limits = {
            "wall_clock_seconds": (
                limits.get("wall_clock_seconds") if isinstance(limits, Mapping) else None
            ),
            "total_model_tokens": (
                limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
            ),
        }
        if not isinstance(check.get("limits"), Mapping) or any(
            check["limits"].get(field) != wanted
            for field, wanted in expected_limits.items()
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong limits")

        bubblewrap = check.get("bubblewrap")
        if not isinstance(bubblewrap, Mapping) or (
            bubblewrap.get("version") != frozen.get("bubblewrap_version")
            or bubblewrap.get("binary_sha256") != frozen.get("bubblewrap_binary_sha256")
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong bubblewrap identity")

        compiled = check.get("compiled_environment_summary")
        if not isinstance(compiled, Mapping) or (
            compiled.get("sha256") != frozen.get("compiled_environment_summary_sha256")
            or any(
                not isinstance(compiled.get(field), int)
                or isinstance(compiled.get(field), bool)
                or compiled.get(field) <= 0
                for field in (
                    "toolchain_file_count",
                    "package_count",
                    "package_file_count",
                )
            )
        ):
            errors.append(f"run {label} freeze check has invalid compiled-tree evidence")
        elif expected_compiled_counts is not None and any(
            compiled.get(field) != wanted
            for field, wanted in expected_compiled_counts.items()
        ):
            errors.append(f"run {label} freeze check has stale compiled-tree counts")

        packages_runtime = check.get("packages_runtime")
        if not isinstance(packages_runtime, Mapping) or (
            packages_runtime.get("path") != frozen.get("packages_runtime_manifest")
            or packages_runtime.get("sha256")
            != frozen.get("packages_runtime_manifest_sha256")
            or not isinstance(packages_runtime.get("file_count"), int)
            or isinstance(packages_runtime.get("file_count"), bool)
            or packages_runtime.get("file_count") <= 0
            or not isinstance(packages_runtime.get("source_file_count"), int)
            or isinstance(packages_runtime.get("source_file_count"), bool)
            or packages_runtime.get("source_file_count") <= 0
            or not isinstance(packages_runtime.get("olean_file_count"), int)
            or isinstance(packages_runtime.get("olean_file_count"), bool)
            or packages_runtime.get("olean_file_count") <= 0
            or not isinstance(
                packages_runtime.get("compiled_support_file_count"), int
            )
            or isinstance(
                packages_runtime.get("compiled_support_file_count"), bool
            )
            or packages_runtime.get("compiled_support_file_count") <= 0
            or packages_runtime.get("source_file_count")
            + packages_runtime.get("olean_file_count")
            + packages_runtime.get("compiled_support_file_count")
            != packages_runtime.get("file_count")
            or not isinstance(packages_runtime.get("verification"), Mapping)
            or packages_runtime["verification"].get("ok") is not True
            or packages_runtime["verification"].get("verified")
            != packages_runtime["verification"].get("expected")
            or packages_runtime["verification"].get("missing") != []
            or packages_runtime["verification"].get("changed") != []
        ):
            errors.append(f"run {label} freeze check has invalid packages-runtime evidence")
        elif expected_runtime_file_count is not None and (
            packages_runtime.get("file_count") != expected_runtime_file_count
            or packages_runtime["verification"].get("expected")
            != expected_runtime_file_count
            or (
                expected_runtime_counts is not None
                and (
                    packages_runtime.get("source_file_count")
                    != expected_runtime_counts["source"]
                    or packages_runtime.get("olean_file_count")
                    != expected_runtime_counts["olean"]
                    or packages_runtime.get("compiled_support_file_count")
                    != expected_runtime_counts["compiled_support"]
                )
            )
        ):
            errors.append(f"run {label} freeze check has stale packages-runtime counts")

        host = check.get("host_class")
        required_host_fields = (
            "kernel",
            "virtualization",
            "processor",
            "online_logical_cpus",
            "visible_memory_bytes",
        )
        if not isinstance(host, Mapping) or any(
            host.get(field) in (None, "") for field in required_host_fields
        ):
            errors.append(f"run {label} freeze check has incomplete host evidence")
        elif environment is not None:
            recorded_host = environment.get("host_class")
            if not isinstance(recorded_host, Mapping) or any(
                host.get(field) != recorded_host.get(field) for field in required_host_fields
            ):
                errors.append(f"run {label} freeze check host disagrees with environment.json")
        metadata_digests = check.get("metadata_document_sha256")
        if not isinstance(metadata_digests, Mapping):
            errors.append(f"run {label} freeze check has no metadata document digests")
        else:
            for name, wanted in expected_metadata.items():
                if metadata_digests.get(name) != wanted:
                    errors.append(f"run {label} freeze check is stale for {name}")
    if len(evidence_digests) > 1:
        errors.append("runs cite more than one frozen-run verification artifact")
    return next(iter(evidence_digests)) if len(evidence_digests) == 1 else None


def _check_limits(
    run: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
    *,
    final_record: bool,
) -> None:
    label = str(run.get("run_id"))
    limits = config.get("limits")
    run_limits = run.get("limits")
    if not isinstance(limits, Mapping) or not isinstance(run_limits, Mapping):
        errors.append(f"run {label} or config lacks limits")
        return
    wall_limit = limits.get("wall_clock_seconds")
    token_limit = limits.get("total_model_tokens")
    if run_limits.get("time_seconds") != wall_limit:
        errors.append(f"run {label} has the wrong wall-clock limit")
    if run_limits.get("model_tokens") != token_limit:
        errors.append(f"run {label} has the wrong model-token limit")
    elapsed = run.get("scored_elapsed_seconds")
    if not isinstance(elapsed, (int, float)) or isinstance(elapsed, bool) or elapsed < 0:
        errors.append(f"run {label} has invalid scored elapsed time")
    elif isinstance(wall_limit, (int, float)) and elapsed > wall_limit:
        errors.append(f"run {label} has scored elapsed time above the fixed limit")
    if final_record and not bool(run.get("pass")) and elapsed != limits.get(
        "failure_scored_time_seconds"
    ):
        errors.append(f"failed run {label} was not charged the full fixed time")


def _check_protocol(
    run: Mapping[str, Any],
    errors: list[str],
    *,
    allow_observational_unscored: bool,
) -> bool:
    """Validate protocol evidence and return whether this is an official run."""

    label = str(run.get("run_id"))
    protocol = run.get("protocol")
    if not isinstance(protocol, Mapping):
        errors.append(f"final run {label} lacks a protocol record")
        return False
    claims = protocol.get("claims")
    verified = protocol.get("verified")
    if not isinstance(claims, Mapping):
        errors.append(f"final run {label} lacks protocol claims")
        claims = {}
    if not isinstance(verified, Mapping):
        errors.append(f"final run {label} lacks protocol verification evidence")
        verified = {}
    for name in PROTOCOL_CLAIMS:
        if not isinstance(claims.get(name), bool):
            errors.append(f"final run {label} has no Boolean protocol claim {name}")
    for name in PROTOCOL_VERIFICATIONS:
        if not isinstance(verified.get(name), bool):
            errors.append(f"final run {label} has no Boolean protocol verification {name}")
    seed_was_supplied = run.get("backend_seed") is not None
    if claims.get("backend_seed_supplied") is not seed_was_supplied:
        errors.append(
            f"final run {label} protocol disagrees with whether a backend seed was supplied"
        )
    if claims.get("seed_enforced_by_agent") is True and not seed_was_supplied:
        errors.append(f"final run {label} claims to enforce a missing backend seed")

    complete = protocol.get("complete") is True
    officially_scored = run.get("scored") is True and complete
    if officially_scored:
        for name in PROTOCOL_CLAIMS:
            if claims.get(name) is not True:
                errors.append(
                    f"official run {label} marks protocol complete while claim {name} is unmet"
                )
        for name in PROTOCOL_VERIFICATIONS:
            if verified.get(name) is not True:
                errors.append(
                    f"official run {label} marks protocol complete while verification {name} failed"
                )
        return True

    if not allow_observational_unscored:
        if not complete:
            errors.append(f"final run {label} does not have a complete protocol record")
        if run.get("scored") is not True:
            errors.append(f"final run {label} is not marked scored")
        return False

    if run.get("scored") is not False:
        errors.append(f"observational run {label} must be explicitly marked scored=false")
    if complete:
        errors.append(
            f"observational run {label} is unscored even though its protocol is marked complete"
        )
    unmet_claims = {
        name for name in PROTOCOL_CLAIMS if claims.get(name) is not True
    }
    unsafe_unmet = unmet_claims - OBSERVATIONAL_CONTROL_CLAIMS
    if unsafe_unmet:
        errors.append(
            f"observational run {label} failed non-relaxable controls: "
            + ", ".join(sorted(unsafe_unmet))
        )
    if not unmet_claims:
        errors.append(
            f"observational run {label} gives no unavailable backend/reference control reason"
        )
    failed_verifications = {
        name for name in PROTOCOL_VERIFICATIONS if verified.get(name) is not True
    }
    if failed_verifications:
        errors.append(
            f"observational run {label} failed required verification: "
            + ", ".join(sorted(failed_verifications))
        )
    notes = protocol.get("notes")
    if not isinstance(notes, list) or not notes or not all(
        isinstance(note, str) and note for note in notes
    ):
        errors.append(
            f"observational run {label} must explain its unavailable controls in protocol notes"
        )
    return False


def _check_network_evidence(run: Mapping[str, Any], errors: list[str]) -> None:
    label = str(run.get("run_id"))
    evidence = run.get("network_violation")
    if not isinstance(evidence, Mapping):
        errors.append(f"final run {label} lacks structured network-violation evidence")
        return
    for field in ("detected", "saturated", "integrity_ok"):
        if not isinstance(evidence.get(field), bool):
            errors.append(f"final run {label} has non-Boolean network field {field}")
    for field in ("event_count", "kernel_event_count"):
        value = evidence.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            errors.append(f"final run {label} has invalid network field {field}")
    note = evidence.get("note")
    if not isinstance(note, str) or not note:
        errors.append(f"final run {label} has no network evidence note")
    marker = evidence.get("saved_marker_log")
    marker_digest = evidence.get("marker_sha256")
    if marker is not None and (not isinstance(marker, str) or not marker):
        errors.append(f"final run {label} has an invalid saved network marker path")
    if marker_digest is not None and not _hex_digest(marker_digest):
        errors.append(f"final run {label} has an invalid saved network marker SHA-256")
    if (marker is None) != (marker_digest is None):
        errors.append(f"final run {label} has incomplete saved network marker evidence")

    detected = evidence.get("detected")
    integrity_ok = evidence.get("integrity_ok")
    event_count = evidence.get("event_count")
    if detected is False:
        if event_count != 0 or evidence.get("saturated") is not False:
            errors.append(f"final run {label} says no network event but records event data")
        if integrity_ok is not True:
            errors.append(f"final run {label} says no network event with failed marker integrity")
    if integrity_ok is False and detected is not True:
        errors.append(f"final run {label} has failed network integrity without a violation")
    if run.get("pass") is True and (detected is not False or integrity_ok is not True):
        errors.append(f"passing run {label} has unsafe network evidence")
    if detected is True and run.get("failure_code") not in {
        "TIME_LIMIT",
        "TOKEN_LIMIT",
        "NO_SUBMISSION",
        "RULE_VIOLATION",
    }:
        errors.append(
            f"run {label} detected a network attempt but has incoherent failure code "
            f"{run.get('failure_code')!r}"
        )
    protocol = run.get("protocol")
    verified = protocol.get("verified") if isinstance(protocol, Mapping) else None
    if isinstance(verified, Mapping) and verified.get(
        "network_violation_marker_integrity"
    ) is not integrity_ok:
        errors.append(f"final run {label} protocol disagrees with network marker integrity")


def _check_n_preflight_evidence(
    run: Mapping[str, Any],
    errors: list[str],
    *,
    controlled_manifest_sha256: str | None,
) -> None:
    if run.get("condition") != "N":
        return
    label = str(run.get("run_id"))
    preflight = run.get("n_preflight")
    if not isinstance(preflight, Mapping):
        errors.append(f"condition-N run {label} lacks structured preflight evidence")
        return
    if preflight.get("ok") is not True or preflight.get("complete") is not True:
        errors.append(f"condition-N run {label} did not complete its isolation preflight")
    staging = preflight.get("controlled_task_staging")
    if not isinstance(staging, Mapping):
        errors.append(f"condition-N run {label} has no controlled-task staging evidence")
    else:
        verified = staging.get("verified_files")
        expected = staging.get("expected_files")
        if (
            staging.get("complete") is not True
            or not isinstance(verified, int)
            or isinstance(verified, bool)
            or verified <= 0
            or verified != expected
            or not _hex_digest(staging.get("manifest_sha256"))
        ):
            errors.append(f"condition-N run {label} has incomplete controlled-task staging")
        if (
            controlled_manifest_sha256 is not None
            and staging.get("manifest_sha256") != controlled_manifest_sha256
        ):
            errors.append(f"condition-N run {label} staged the wrong controlled manifest")
    scan = preflight.get("filesystem_scan")
    if not isinstance(scan, Mapping):
        errors.append(f"condition-N run {label} has no complete filesystem-scan evidence")
    else:
        markers = scan.get("markers")
        file_count = scan.get("regular_file_count")
        expected = staging.get("expected_files") if isinstance(staging, Mapping) else None
        if (
            scan.get("root") != "."
            or not isinstance(markers, list)
            or "NumStability" not in markers
            or not isinstance(file_count, int)
            or isinstance(file_count, bool)
            or not isinstance(expected, int)
            or file_count < expected
            or scan.get("symlink_count") != 0
        ):
            errors.append(f"condition-N run {label} filesystem scan did not cover the staged task")
    probe = preflight.get("import_probe")
    if not isinstance(probe, Mapping) or (
        probe.get("reliable") is not True or probe.get("importable") is not False
    ):
        errors.append(f"condition-N run {label} did not prove the library import absent")


def _check_final_record(
    run: Mapping[str, Any],
    expected: Mapping[str, Any],
    task: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
    *,
    allow_observational_unscored: bool,
    controlled_manifest_sha256: str | None,
) -> bool:
    run_id = run.get("run_id")
    label = str(run_id or expected["run_id"])
    _check_planned_metadata(
        run, expected, task, errors, require_planned_run_id=True
    )
    _check_limits(run, config, errors, final_record=True)
    _check_network_evidence(run, errors)
    _check_n_preflight_evidence(
        run, errors, controlled_manifest_sha256=controlled_manifest_sha256
    )
    officially_scored = _check_protocol(
        run,
        errors,
        allow_observational_unscored=allow_observational_unscored,
    )
    passed = run.get("pass")
    failure = run.get("failure_code")
    useful_work_started = run.get("useful_work_started")
    if not isinstance(useful_work_started, bool):
        errors.append(f"final run {label} has no Boolean useful_work_started marker")
    if not isinstance(passed, bool):
        errors.append(f"final run {label} has no Boolean pass result")
    if passed is True and failure is not None:
        errors.append(f"passing run {label} has failure code {failure!r}")
    if passed is True and useful_work_started is not True:
        errors.append(f"passing run {label} says useful work never started")
    if passed is not True and failure not in FAILURE_CODES:
        errors.append(f"failed final run {label} has invalid failure code {failure!r}")
    if failure == "SYSTEM_ERROR" and useful_work_started is not True:
        errors.append(
            f"final system-error run {label} did not start useful work and belongs in incident handling"
        )
    actual_stop = run.get("actual_stop_seconds")
    if (
        not isinstance(actual_stop, (int, float))
        or isinstance(actual_stop, bool)
        or actual_stop < 0
    ):
        errors.append(f"final run {label} has invalid actual stop time")
    usage = run.get("token_usage")
    token_fields = ("input_tokens", "cached_input_tokens", "output_tokens", "model_tokens")
    if not isinstance(usage, Mapping) or any(
        not isinstance(usage.get(field), int)
        or isinstance(usage.get(field), bool)
        or usage.get(field) < 0
        for field in token_fields
    ):
        errors.append(f"final run {label} lacks exact model-token usage")
    else:
        if usage["cached_input_tokens"] > usage["input_tokens"]:
            errors.append(f"final run {label} has cached input above total input")
        if usage["model_tokens"] != usage["input_tokens"] + usage["output_tokens"]:
            errors.append(f"final run {label} has inconsistent total model-token usage")
        limits = config.get("limits")
        token_limit = limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
        if isinstance(token_limit, int) and usage["model_tokens"] > token_limit:
            errors.append(f"final run {label} exceeded the fixed model-token limit")
    if run.get("condition") == "N" and run.get("library_use") is not False:
        errors.append(f"condition-N run {label} does not record library_use=false")
    if run.get("condition") == "L" and passed is True and not isinstance(
        run.get("library_use"), bool
    ):
        errors.append(f"passing condition-L run {label} lacks library-use classification")
    declarations = run.get("library_declarations")
    if not isinstance(declarations, list) or not all(
        isinstance(name, str) and name for name in declarations
    ):
        errors.append(f"final run {label} has invalid library declaration evidence")
    elif run.get("library_use") is True and not declarations:
        errors.append(
            f"final run {label} claims library use without a library declaration"
        )
    elif run.get("library_use") is False and declarations:
        errors.append(
            f"final run {label} records library declarations while library_use=false"
        )
    if run.get("condition") == "N" and declarations:
        errors.append(f"condition-N run {label} records forbidden library declarations")
    if passed is True and not _hex_digest(run.get("submission_sha256")):
        errors.append(f"passing run {label} has no fixed submission SHA-256")
    return officially_scored


def check_result_set(
    runs: Sequence[Mapping[str, Any]],
    *,
    run_order: Mapping[str, Any],
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
    repository_root: Path | None = None,
    allow_observational_unscored: bool = False,
) -> dict[str, Any]:
    """Return a detailed matrix check; callers must require ``ok`` for final analysis."""

    errors: list[str] = []
    warnings: list[str] = []
    benchmark_id_values = (
        run_order.get("benchmark_id"),
        config.get("benchmark_id"),
        manifest.get("benchmark_id"),
    )
    benchmark_ids = {value for value in benchmark_id_values if isinstance(value, str)}
    if (
        len(benchmark_ids) != 1
        or any(not isinstance(value, str) or not value for value in benchmark_id_values)
    ):
        errors.append(f"benchmark_id disagrees across metadata: {sorted(map(str, benchmark_ids))}")
    tasks = _metadata_tasks(manifest, errors)
    controlled_manifest_hashes: dict[str, str] = {}
    if repository_root is not None:
        for task_id in tasks:
            path = (
                repository_root.resolve()
                / "paper_bencmark"
                / "highambench"
                / "metadata"
                / "controlled"
                / f"{task_id}.json"
            )
            if not path.is_file():
                errors.append(f"controlled manifest is missing for {task_id}: {path}")
            else:
                controlled_manifest_hashes[task_id] = sha256_file(path)
    repetitions = _repetitions(config, errors)
    expected, planned_pairs = _expected_assignments(
        run_order, tasks, repetitions, errors
    )
    (
        metadata_errors,
        metadata_warnings,
        verified_hashes,
        metadata_nonreference_reasons,
    ) = _metadata_readiness(
        config,
        manifest,
        repository_root=repository_root,
        allow_observational_unscored=allow_observational_unscored,
    )
    errors.extend(metadata_errors)
    warnings.extend(metadata_warnings)
    freeze_check_sha256 = _check_frozen_run_evidence(
        runs,
        config=config,
        manifest=manifest,
        run_order=run_order,
        repository_root=repository_root,
        errors=errors,
        warnings=warnings,
    )
    nonreference_reasons: set[str] = set(metadata_nonreference_reasons)
    repetitions_without_seed = sorted(
        repetition_id for repetition_id, seed in repetitions.items() if seed is None
    )
    if repetitions_without_seed:
        reason = (
            "backend seeds are unavailable for repetitions: "
            + ", ".join(repetitions_without_seed)
        )
        nonreference_reasons.add(reason)
        if not allow_observational_unscored:
            errors.append(reason)

    counts = config.get("planned_counts_per_agent")
    if isinstance(counts, Mapping):
        expected_counts = {
            "papers": len({task["paper_id"] for task in tasks.values()}),
            "tasks": len(tasks),
            "repetitions_per_task": len(repetitions),
            "conditions": 2,
            "paired_assignments": len(expected) // 2,
            "runs": len(expected),
        }
        for field, wanted in expected_counts.items():
            if counts.get(field) != wanted:
                errors.append(
                    f"config planned count {field}={counts.get(field)!r}; expected {wanted}"
                )
    else:
        errors.append("config has no planned_counts_per_agent object")

    frozen = config.get("frozen_environment")
    frozen = frozen if isinstance(frozen, Mapping) else {}
    expected_agent_fields = {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
    }
    expected_environment_id = frozen.get("environment_id")

    run_ids: set[str] = set()
    groups: dict[tuple[AgentKey, AssignmentKey], list[Mapping[str, Any]]] = {}
    agent_keys: set[AgentKey] = set()
    for index, run in enumerate(runs):
        if run.get("schema_version") != SCHEMA_VERSION:
            errors.append(
                f"input record {index} has schema_version={run.get('schema_version')!r}; "
                f"expected {SCHEMA_VERSION!r}"
            )
        if run.get("kind") != "highambench-run":
            errors.append(f"input record {index} is not a highambench-run")
            continue
        run_id = run.get("run_id")
        if not isinstance(run_id, str) or not run_id:
            errors.append(f"input record {index} has no run_id")
        elif run_id in run_ids:
            errors.append(f"run_id {run_id} is repeated; incident logs would not be distinct")
        else:
            run_ids.add(run_id)
        agent_record = run.get("agent")
        if not isinstance(agent_record, Mapping):
            errors.append(f"run {run_id!r} lacks frozen agent metadata")
        else:
            for field, wanted in expected_agent_fields.items():
                if agent_record.get(field) != wanted:
                    errors.append(
                        f"run {run_id!r} has agent.{field}={agent_record.get(field)!r}; "
                        f"expected frozen {wanted!r}"
                    )
        if run.get("environment_id") != expected_environment_id:
            errors.append(
                f"run {run_id!r} has environment_id={run.get('environment_id')!r}; "
                f"expected frozen {expected_environment_id!r}"
            )
        started = _iso_time(run.get("started_at_utc"))
        finished = _iso_time(run.get("finished_at_utc"))
        if started is None or finished is None:
            errors.append(f"run {run_id!r} lacks usable UTC timestamps")
        elif started > finished:
            errors.append(f"run {run_id!r} finishes before it starts")
        assignment = _assignment_key(run)
        if assignment is None:
            errors.append(f"run {run_id!r} has an invalid assignment identity")
            continue
        key = _agent_key(run)
        agent_keys.add(key)
        groups.setdefault((key, assignment), []).append(run)

    if not agent_keys:
        errors.append("result set contains no evaluated agent")
    final_records: list[Mapping[str, Any]] = []
    system_incidents: list[dict[str, Any]] = []
    selected_run_ids: list[str] = []
    official_final_count = 0
    system_error_issues: list[str] = []
    expected_agent_version = frozen.get("agent_version")
    expected_model_version = frozen.get("model_version")
    for agent in sorted(agent_keys):
        if agent[1] != expected_agent_version:
            errors.append(
                f"agent {agent[0]} uses version {agent[1]!r}; expected {expected_agent_version!r}"
            )
        if agent[2] != expected_model_version:
            errors.append(
                f"agent {agent[0]} uses model {agent[2]!r}; expected {expected_model_version!r}"
            )
        actual_assignments = {
            assignment for key, assignment in groups if key == agent
        }
        for assignment in sorted(set(expected) - actual_assignments):
            errors.append(
                f"agent {agent} is missing assignment {'/'.join(assignment)}"
            )
        for assignment in sorted(actual_assignments - set(expected)):
            errors.append(
                f"agent {agent} has unplanned assignment {'/'.join(assignment)}"
            )
        for assignment in sorted(set(expected) & actual_assignments):
            records = groups[(agent, assignment)]
            incidents = [
                record
                for record in records
                if record.get("failure_code") == "SYSTEM_ERROR"
                and record.get("useful_work_started") is False
            ]
            candidates = [record for record in records if record not in incidents]
            if len(incidents) > 1:
                issue = (
                    f"agent {agent} assignment {'/'.join(assignment)} has {len(incidents)} "
                    "system errors; the one allowed rerun is exhausted"
                )
                errors.append(issue)
                system_error_issues.append(issue)
            for incident in incidents:
                planned_run_id = expected[assignment]["run_id"]
                incident_run_id = incident.get("run_id")
                if incident.get("planned_run_id") != planned_run_id:
                    issue = (
                        f"system-error run {incident_run_id} does not name planned run "
                        f"{planned_run_id}"
                    )
                    errors.append(issue)
                    system_error_issues.append(issue)
                if (
                    not isinstance(incident_run_id, str)
                    or not incident_run_id.startswith(f"{planned_run_id}-system-attempt-")
                ):
                    issue = f"system-error incident has no stable unique retry ID: {incident_run_id!r}"
                    errors.append(issue)
                    system_error_issues.append(issue)
                if incident.get("scored") is not False:
                    issue = f"system-error run {incident.get('run_id')} is incorrectly scored"
                    errors.append(issue)
                    system_error_issues.append(issue)
                if incident.get("pass") is not False:
                    issue = f"system-error run {incident.get('run_id')} must record pass=false"
                    errors.append(issue)
                    system_error_issues.append(issue)
                if not isinstance(incident.get("failure_note"), str) or not incident.get(
                    "failure_note"
                ):
                    issue = f"system-error run {incident.get('run_id')} lacks an incident note"
                    errors.append(issue)
                    system_error_issues.append(issue)
                incident_check_start = len(errors)
                _check_planned_metadata(
                    incident,
                    expected[assignment],
                    tasks[assignment[0]],
                    errors,
                    require_planned_run_id=False,
                )
                _check_limits(incident, config, errors, final_record=False)
                system_error_issues.extend(errors[incident_check_start:])
            if len(candidates) != 1:
                issue = (
                    f"agent {agent} assignment {'/'.join(assignment)} has {len(candidates)} "
                    "non-system final records; expected exactly one"
                )
                errors.append(issue)
                if incidents:
                    system_error_issues.append(issue)
                continue
            final = candidates[0]
            if incidents:
                incident = incidents[0]
                incident_finished = _iso_time(incident.get("finished_at_utc"))
                final_started = _iso_time(final.get("started_at_utc"))
                if incident_finished is None or final_started is None:
                    issue = (
                        f"system-error retry for {final.get('run_id')} lacks usable UTC timestamps"
                    )
                    errors.append(issue)
                    system_error_issues.append(issue)
                elif incident_finished > final_started:
                    issue = (
                        f"system-error retry for {final.get('run_id')} started before the incident ended"
                    )
                    errors.append(issue)
                    system_error_issues.append(issue)
                system_incidents.append(
                    {
                        "agent_id": agent[0],
                        "agent_version": agent[1],
                        "model": agent[2],
                        "assignment": "/".join(assignment),
                        "incident_run_id": incident.get("run_id"),
                        "replacement_run_id": final.get("run_id"),
                        "status": "resolved_by_one_rerun",
                        "note": incident.get("failure_note"),
                    }
                )
            officially_scored = _check_final_record(
                final,
                expected[assignment],
                tasks[assignment[0]],
                config,
                errors,
                allow_observational_unscored=allow_observational_unscored,
                controlled_manifest_sha256=controlled_manifest_hashes.get(assignment[0]),
            )
            if officially_scored:
                official_final_count += 1
            else:
                protocol = final.get("protocol")
                if isinstance(protocol, Mapping):
                    notes = protocol.get("notes")
                    if isinstance(notes, list):
                        nonreference_reasons.update(str(note) for note in notes)
                    claims = protocol.get("claims")
                    if isinstance(claims, Mapping):
                        nonreference_reasons.update(
                            f"protocol claim not met: {name}"
                            for name, value in claims.items()
                            if value is not True
                        )
            final_records.append(final)
            if isinstance(final.get("run_id"), str):
                selected_run_ids.append(final["run_id"])

        environments = {
            record.get("environment_id")
            for record in final_records
            if _agent_key(record) == agent
        }
        if None in environments or "" in environments:
            errors.append(f"agent {agent} has a final run without environment_id")
        if len(environments) > 1:
            errors.append(f"agent {agent} uses multiple environment_id values: {environments}")

        for pair_id, planned in sorted(planned_pairs.items()):
            first_key = (planned["task_id"], planned["repetition_id"], planned["condition_order"][0])
            second_key = (planned["task_id"], planned["repetition_id"], planned["condition_order"][1])
            first_records = groups.get((agent, first_key), [])
            second_records = groups.get((agent, second_key), [])
            if not first_records or not second_records:
                continue
            first_finish = max(
                (_iso_time(record.get("finished_at_utc")) for record in first_records),
                default=None,
                key=lambda value: value or dt.datetime.min.replace(tzinfo=dt.timezone.utc),
            )
            second_start = min(
                (_iso_time(record.get("started_at_utc")) for record in second_records),
                default=None,
                key=lambda value: value or dt.datetime.max.replace(tzinfo=dt.timezone.utc),
            )
            if first_finish is None or second_start is None:
                errors.append(f"pair {pair_id} for agent {agent} lacks usable order timestamps")
            elif first_finish > second_start:
                errors.append(f"pair {pair_id} for agent {agent} ran out of planned N/L order")

        seeds_by_pair: dict[str, set[Any]] = {}
        for record in final_records:
            if _agent_key(record) == agent:
                seeds_by_pair.setdefault(str(record.get("pair_id")), set()).add(
                    record.get("backend_seed")
                )
        for pair_id, seeds in seeds_by_pair.items():
            if len(seeds) != 1:
                errors.append(f"pair {pair_id} for agent {agent} does not use one matching seed")

    expected_final_count = len(expected) * len(agent_keys)
    if len(final_records) != expected_final_count:
        errors.append(
            f"selected {len(final_records)} final records; expected {expected_final_count}"
        )
    if (
        allow_observational_unscored
        and (repetitions_without_seed or metadata_nonreference_reasons)
        and official_final_count
    ):
        errors.append(
            "a non-reference observational configuration requires every final run to be "
            "explicitly marked scored=false"
        )
    reference_compliant = (
        not errors
        and not repetitions_without_seed
        and not metadata_nonreference_reasons
        and official_final_count == expected_final_count
    )
    check_ok = not errors
    analysis_profile = (
        "reference"
        if reference_compliant
        else "observational_pilot"
        if check_ok and allow_observational_unscored
        else "invalid"
    )
    network_violation_run_count = sum(
        1
        for record in final_records
        if isinstance(record.get("network_violation"), Mapping)
        and record["network_violation"].get("detected") is True
    )
    network_integrity_failure_count = sum(
        1
        for record in final_records
        if isinstance(record.get("network_violation"), Mapping)
        and record["network_violation"].get("integrity_ok") is False
    )
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-result-set-check",
        "ok": check_ok,
        "benchmark_id": next(iter(benchmark_ids)) if len(benchmark_ids) == 1 else None,
        "metadata_document_sha256": {
            "config": _document_digest(config),
            "manifest": _document_digest(manifest),
            "run_order": _document_digest(run_order),
        },
        "freeze_check_sha256": freeze_check_sha256,
        "network_violation_run_count": network_violation_run_count,
        "network_integrity_failure_count": network_integrity_failure_count,
        "expected_agents": len(agent_keys),
        "expected_pairs_per_agent": len(expected) // 2,
        "expected_final_runs_per_agent": len(expected),
        "input_record_count": len(runs),
        "selected_final_record_count": len(final_records),
        "official_final_record_count": official_final_count,
        "selected_final_run_ids": sorted(selected_run_ids),
        "analysis_profile": analysis_profile,
        "reference_compliant": reference_compliant,
        "official_scores_valid": reference_compliant,
        "observational_results_allowed": allow_observational_unscored,
        "nonreference_reasons": sorted(nonreference_reasons),
        "system_error_incident_count": len(system_incidents),
        "system_error_incidents": system_incidents,
        "system_error_issue_count": len(system_error_issues),
        "system_error_issues": system_error_issues,
        "system_error_handling_complete": not system_error_issues,
        "verified_hashes": verified_hashes,
        "errors": errors,
        "warnings": warnings,
    }


def require_complete_result_set(check: Mapping[str, Any]) -> None:
    if check.get("ok") is True:
        return
    errors = check.get("errors")
    details = "; ".join(str(error) for error in errors[:8]) if isinstance(errors, list) else ""
    if isinstance(errors, list) and len(errors) > 8:
        details += f"; ... and {len(errors) - 8} more"
    raise BenchmarkToolError("result set is not complete or frozen: " + details)


def _load_jsonl(paths: Sequence[Path]) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []
    for path in paths:
        try:
            stream = path.open(encoding="utf-8")
        except OSError as error:
            raise BenchmarkToolError(f"cannot open raw results {path}: {error}") from error
        with stream:
            for line_number, line in enumerate(stream, start=1):
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except json.JSONDecodeError as error:
                    raise BenchmarkToolError(f"invalid JSON at {path}:{line_number}: {error}") from error
                if not isinstance(value, dict):
                    raise BenchmarkToolError(f"non-object result at {path}:{line_number}")
                runs.append(value)
    return runs


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw_jsonl", type=Path, nargs="+")
    parser.add_argument("--run-order", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--repository-root", type=Path, required=True)
    parser.add_argument(
        "--allow-observational-unscored",
        action="store_true",
        help=(
            "accept a complete matrix whose final runs are explicitly unscored; "
            "the check remains non-reference and official scores stay invalid"
        ),
    )
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        runs = _load_jsonl(args.raw_jsonl)
        run_order = read_json(args.run_order)
        config = read_json(args.config)
        manifest = read_json(args.manifest)
        if not all(isinstance(value, dict) for value in (run_order, config, manifest)):
            raise BenchmarkToolError("run order, config, and manifest must be JSON objects")
        check = check_result_set(
            runs,
            run_order=run_order,
            config=config,
            manifest=manifest,
            repository_root=args.repository_root,
            allow_observational_unscored=args.allow_observational_unscored,
        )
        if args.output:
            write_json(args.output, check)
        else:
            print(json.dumps(check, indent=2, sort_keys=True))
        return 0 if check["ok"] else 1
    except BenchmarkToolError as error:
        print(f"error: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
