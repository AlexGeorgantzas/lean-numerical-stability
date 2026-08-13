#!/usr/bin/env python3
"""Validate prepared or completed HighamBench faithfulness-audit artifacts."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

try:
    from .common import (
        ACCEPTED_CLASSIFICATIONS,
        AUDIT_SCHEMA_VERSION,
        CLASSIFICATIONS,
        SEMANTIC_CHECKS,
        SUPPORTED_AUDIT_SCHEMA_VERSIONS,
        TASK_ID_PATTERN,
        implication_classification,
        sha256_file,
        sha256_text,
    )
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        ACCEPTED_CLASSIFICATIONS,
        AUDIT_SCHEMA_VERSION,
        CLASSIFICATIONS,
        SEMANTIC_CHECKS,
        SUPPORTED_AUDIT_SCHEMA_VERSIONS,
        TASK_ID_PATTERN,
        implication_classification,
        sha256_file,
        sha256_text,
    )


SCRIPT_DIR = Path(__file__).resolve().parent
REPOSITORY_ROOT = SCRIPT_DIR.parents[2]
HIGHAMBENCH_ROOT = REPOSITORY_ROOT / "paper_bencmark" / "highambench"


class AuditValidationError(RuntimeError):
    """Raised when one or more audit invariants fail."""


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise AuditValidationError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise AuditValidationError(f"expected a JSON object in {path}")
    return value


def task_paths(task_id: str) -> tuple[Path, Path]:
    normalized = task_id.upper()
    if re.fullmatch(TASK_ID_PATTERN, normalized) is None:
        raise AuditValidationError(f"invalid task ID {task_id!r}")
    paper, tier = normalized.split("-", 1)
    task_dir = HIGHAMBENCH_ROOT / "tasks" / paper / tier
    return task_dir, task_dir / "faithfulness"


def repository_path(relative: str) -> Path:
    candidate = (REPOSITORY_ROOT / relative).resolve()
    try:
        candidate.relative_to(REPOSITORY_ROOT.resolve())
    except ValueError as error:
        raise AuditValidationError(f"path escapes repository: {relative}") from error
    return candidate


def require(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def check_recorded_file(record: Any, label: str, errors: list[str]) -> Path | None:
    if not isinstance(record, dict):
        errors.append(f"{label}: expected file record")
        return None
    path_text = record.get("path")
    expected_hash = record.get("sha256")
    if not isinstance(path_text, str) or not isinstance(expected_hash, str):
        errors.append(f"{label}: incomplete path/hash record")
        return None
    try:
        path = repository_path(path_text)
    except AuditValidationError as error:
        errors.append(str(error))
        return None
    if not path.is_file():
        errors.append(f"{label}: missing file {path_text}")
        return None
    actual = sha256_file(path)
    require(actual == expected_hash, f"{label}: SHA-256 mismatch for {path_text}", errors)
    return path


def dependency_ids(manifest: dict[str, Any], errors: list[str]) -> list[str]:
    dependencies = manifest.get("dependencies")
    if not isinstance(dependencies, list) or not dependencies:
        errors.append("manifest: dependencies must be a nonempty list")
        return []
    ids: list[str] = []
    for index, dependency in enumerate(dependencies, start=1):
        if not isinstance(dependency, dict):
            errors.append(f"manifest: dependency {index} is not an object")
            continue
        expected = f"D{index:03d}"
        actual = dependency.get("id")
        require(actual == expected, f"manifest: expected dependency ID {expected}, got {actual}", errors)
        ids.append(str(actual))
        require(dependency.get("role") in {"local", "external-frontier"}, f"{expected}: invalid role", errors)
        for key in ("name", "owner_module", "kind"):
            require(isinstance(dependency.get(key), str) and bool(dependency.get(key)), f"{expected}: missing {key}", errors)
        if manifest.get("schema_version") == AUDIT_SCHEMA_VERSION:
            fingerprint = dependency.get("semantic_sha256")
            require(
                isinstance(fingerprint, str)
                and re.fullmatch(r"[0-9a-f]{64}", fingerprint) is not None,
                f"{expected}: missing semantic SHA-256",
                errors,
            )
    return ids


def check_historical_setup_record(record: Any, label: str, errors: list[str]) -> None:
    """Validate v0.1 setup provenance without requiring obsolete files to stay unchanged."""
    if not isinstance(record, dict):
        errors.append(f"{label}: expected file record")
        return
    path_text = record.get("path")
    expected_hash = record.get("sha256")
    require(isinstance(path_text, str) and bool(path_text), f"{label}: missing path", errors)
    require(
        isinstance(expected_hash, str)
        and re.fullmatch(r"[0-9a-f]{64}", expected_hash) is not None,
        f"{label}: invalid historical SHA-256",
        errors,
    )


def validate_dependency_reuse(
    manifest: dict[str, Any], input_paths: dict[str, Path], errors: list[str]
) -> None:
    reuse = manifest.get("dependency_reuse")
    if reuse is None:
        return
    require(isinstance(reuse, dict), "manifest: dependency_reuse must be an object", errors)
    if not isinstance(reuse, dict):
        return
    dependency_by_id = {
        item.get("id"): item
        for item in manifest.get("dependencies", [])
        if isinstance(item, dict)
    }
    source_task_ids = reuse.get("source_task_ids")
    require(
        isinstance(source_task_ids, list)
        and all(
            isinstance(item, str) and re.fullmatch(TASK_ID_PATTERN, item) is not None
            for item in source_task_ids
        ),
        "manifest: dependency reuse source_task_ids are invalid",
        errors,
    )
    source_output_hashes: dict[str, set[str]] = {"direct": set(), "blind": set()}
    source_manifests: dict[str, dict[str, Any]] = {}
    if isinstance(source_task_ids, list):
        for source_task_id in source_task_ids:
            if not isinstance(source_task_id, str) or re.fullmatch(
                TASK_ID_PATTERN, source_task_id
            ) is None:
                continue
            _, source_audit_dir = task_paths(source_task_id)
            source_manifest_path = source_audit_dir / "manifest.json"
            if source_manifest_path.is_file():
                source_manifests[source_task_id] = load_json(source_manifest_path)
            for role, filename in (
                ("direct", "direct_judge.json"),
                ("blind", "blind_translation.json"),
            ):
                output_path = source_audit_dir / "agent_outputs" / filename
                if output_path.is_file():
                    source_output_hashes[role].add(sha256_file(output_path))
    for role in ("direct", "blind"):
        expected_count = reuse.get(f"{role}_count")
        require(
            isinstance(expected_count, int) and expected_count >= 0,
            f"manifest: invalid {role} reuse count",
            errors,
        )
        path = input_paths.get(f"dependency_reuse_{role}")
        if expected_count == 0 and path is None:
            continue
        if path is None:
            errors.append(f"manifest: missing dependency_reuse_{role} input")
            continue
        cache = load_json(path)
        require(cache.get("schema_version") == AUDIT_SCHEMA_VERSION, f"{role} reuse: wrong schema", errors)
        require(cache.get("role") == f"{role}-dependency-reuse", f"{role} reuse: wrong role", errors)
        entries = cache.get("entries")
        require(isinstance(entries, list), f"{role} reuse: entries must be a list", errors)
        if not isinstance(entries, list):
            continue
        require(len(entries) == expected_count, f"{role} reuse: count mismatch", errors)
        seen: set[str] = set()
        for entry in entries:
            if not isinstance(entry, dict):
                errors.append(f"{role} reuse: non-object entry")
                continue
            item_id = entry.get("id")
            require(item_id not in seen, f"{role} reuse: duplicate {item_id}", errors)
            seen.add(str(item_id))
            dependency = dependency_by_id.get(item_id)
            require(dependency is not None, f"{role} reuse: unknown dependency {item_id}", errors)
            if dependency is not None:
                expected_name = dependency.get("name" if role == "direct" else "blind_name")
                require(entry.get("name") == expected_name, f"{role} reuse: {item_id} name mismatch", errors)
                require(
                    entry.get("semantic_sha256") == dependency.get("semantic_sha256"),
                    f"{role} reuse: {item_id} semantic hash mismatch",
                    errors,
                )
            require(
                isinstance(entry.get("reuse_sha256"), str)
                and re.fullmatch(r"[0-9a-f]{64}", entry["reuse_sha256"]) is not None,
                f"{role} reuse: {item_id} invalid reuse hash",
                errors,
            )
            if role == "direct":
                expected_fields = {
                    "id",
                    "name",
                    "semantic_sha256",
                    "interpretation",
                    "source_task_id",
                    "source_dependency_id",
                    "source_direct_output_sha256",
                    "reuse_sha256",
                }
                payload = {
                    "semantic_sha256": entry.get("semantic_sha256"),
                    "interpretation": entry.get("interpretation"),
                    "source_direct_output_sha256": entry.get(
                        "source_direct_output_sha256"
                    ),
                }
                require(
                    entry.get("source_task_id") in (source_task_ids or []),
                    f"direct reuse: {item_id} has an unlisted source task",
                    errors,
                )
                require(
                    entry.get("source_direct_output_sha256")
                    in source_output_hashes["direct"],
                    f"direct reuse: {item_id} source output hash is unavailable",
                    errors,
                )
                source_manifest = source_manifests.get(
                    str(entry.get("source_task_id")), {}
                )
                source_dependencies = {
                    item.get("id"): item
                    for item in source_manifest.get("dependencies", [])
                    if isinstance(item, dict)
                }
                source_dependency = source_dependencies.get(
                    entry.get("source_dependency_id")
                )
                require(
                    source_dependency is not None,
                    f"direct reuse: {item_id} source dependency is unavailable",
                    errors,
                )
                if source_dependency is not None:
                    require(
                        source_dependency.get("semantic_sha256")
                        == entry.get("semantic_sha256"),
                        f"direct reuse: {item_id} source dependency hash mismatch",
                        errors,
                    )
            else:
                expected_fields = {
                    "id",
                    "name",
                    "semantic_sha256",
                    "meaning",
                    "source_blind_output_sha256",
                    "reuse_sha256",
                }
                payload = {
                    "semantic_sha256": entry.get("semantic_sha256"),
                    "meaning": entry.get("meaning"),
                    "source_blind_output_sha256": entry.get(
                        "source_blind_output_sha256"
                    ),
                }
                require(
                    entry.get("source_blind_output_sha256")
                    in source_output_hashes["blind"],
                    f"blind reuse: {item_id} source output hash is unavailable",
                    errors,
                )
            require(
                set(entry) == expected_fields,
                f"{role} reuse: {item_id} fields are incomplete or unexpected",
                errors,
            )
            expected_reuse_hash = sha256_text(
                json.dumps(
                    payload,
                    sort_keys=True,
                    ensure_ascii=True,
                    separators=(",", ":"),
                )
            )
            require(
                entry.get("reuse_sha256") == expected_reuse_hash,
                f"{role} reuse: {item_id} payload hash mismatch",
                errors,
            )
            packet_path = input_paths.get(f"{role}_review_packet")
            if packet_path is not None:
                packet = packet_path.read_text(encoding="utf-8")
                require(
                    packet.count(f"Reuse SHA-256: `{entry.get('reuse_sha256')}`")
                    == 1,
                    f"{role} reuse: {item_id} is not bound once in its review packet",
                    errors,
                )


def validate_prepared(task_id: str) -> tuple[dict[str, Any], list[str]]:
    task_dir, audit_dir = task_paths(task_id)
    errors: list[str] = []
    manifest_path = audit_dir / "manifest.json"
    if not manifest_path.is_file():
        raise AuditValidationError(f"missing manifest: {manifest_path}")
    manifest = load_json(manifest_path)
    schema_version = manifest.get("schema_version")
    require(
        schema_version in SUPPORTED_AUDIT_SCHEMA_VERSIONS,
        "manifest: unsupported schema version",
        errors,
    )
    require(manifest.get("task_id") == task_id.upper(), "manifest: task ID mismatch", errors)
    require(manifest.get("status") in {"prepared", "completed"}, "manifest: invalid status", errors)

    for key in ("target", "task_metadata", "context", "paper"):
        check_recorded_file(manifest.get(key), f"manifest.{key}", errors)
    inputs = manifest.get("inputs")
    require(isinstance(inputs, dict), "manifest: missing inputs object", errors)
    input_paths: dict[str, Path] = {}
    if isinstance(inputs, dict):
        required_inputs = ["declaration_dossier", "blind_dossier", "source_locator"]
        if schema_version == AUDIT_SCHEMA_VERSION:
            required_inputs.extend(
                [
                    "direct_review_packet",
                    "blind_review_packet",
                    "dependency_inventory",
                    "blind_dependency_inventory",
                ]
            )
        optional_inputs = [
            "paper_source_locator",
            "dependency_reuse_direct",
            "dependency_reuse_blind",
        ]
        for key in [*required_inputs, *optional_inputs]:
            if key not in inputs and key in optional_inputs:
                continue
            path = check_recorded_file(inputs.get(key), f"manifest.inputs.{key}", errors)
            if path is not None:
                input_paths[key] = path

    local_sources = manifest.get("local_import_sources")
    require(isinstance(local_sources, list) and bool(local_sources), "manifest: no local import sources", errors)
    if isinstance(local_sources, list):
        for index, source in enumerate(local_sources):
            check_recorded_file(source, f"manifest.local_import_sources[{index}]", errors)

    audit_setup = manifest.get("audit_setup")
    require(isinstance(audit_setup, list) and bool(audit_setup), "manifest: no audit setup fingerprints", errors)
    if isinstance(audit_setup, list):
        for index, setup_file in enumerate(audit_setup):
            if schema_version == "highambench-faithfulness-0.1" and manifest.get("status") == "completed":
                check_historical_setup_record(
                    setup_file, f"manifest.audit_setup[{index}]", errors
                )
            else:
                check_recorded_file(setup_file, f"manifest.audit_setup[{index}]", errors)
    lean_environment = manifest.get("lean_environment")
    require(isinstance(lean_environment, dict), "manifest: no Lean environment fingerprint", errors)
    if isinstance(lean_environment, dict):
        check_recorded_file(lean_environment.get("toolchain"), "manifest.lean_environment.toolchain", errors)
        check_recorded_file(lean_environment.get("lake_manifest"), "manifest.lean_environment.lake_manifest", errors)

    ids = dependency_ids(manifest, errors)
    dossier_keys = ["declaration_dossier", "blind_dossier"]
    if schema_version == AUDIT_SCHEMA_VERSION:
        dossier_keys.extend(["direct_review_packet", "blind_review_packet"])
    for dossier_key in dossier_keys:
        path = input_paths.get(dossier_key)
        if path is None:
            continue
        text = path.read_text(encoding="utf-8")
        for dependency_id in ids:
            count = text.count(f"### {dependency_id}:")
            require(count == 1, f"{dossier_key}: expected one section for {dependency_id}, got {count}", errors)

    checks = manifest.get("semantic_checks")
    expected_checks = [item[0] for item in SEMANTIC_CHECKS]
    actual_checks = [item.get("id") for item in checks if isinstance(item, dict)] if isinstance(checks, list) else []
    require(actual_checks == expected_checks, "manifest: semantic checks are incomplete or out of order", errors)

    source_locator_path = input_paths.get("source_locator")
    if source_locator_path is not None:
        locator = load_json(source_locator_path)
        paper = manifest.get("paper", {})
        require(locator.get("paper_sha256") == paper.get("sha256"), "source locator: paper hash mismatch", errors)
        require(locator.get("task_id") == task_id.upper(), "source locator: task ID mismatch", errors)

    paper_batch = manifest.get("paper_batch")
    if paper_batch is not None:
        require(isinstance(paper_batch, dict), "manifest: paper_batch must be an object", errors)
        batch_locator_path = input_paths.get("paper_source_locator")
        require(batch_locator_path is not None, "manifest: paper batch locator is missing", errors)
        if isinstance(paper_batch, dict) and batch_locator_path is not None:
            locator = load_json(batch_locator_path)
            require(
                set(paper_batch) == {"paper_id", "task_ids", "source_locator"},
                "manifest: paper_batch fields are incomplete or unexpected",
                errors,
            )
            require(
                paper_batch.get("source_locator")
                == manifest.get("inputs", {}).get("paper_source_locator"),
                "paper batch: source locator record mismatch",
                errors,
            )
            require(
                locator.get("schema_version") == AUDIT_SCHEMA_VERSION,
                "paper batch: wrong locator schema",
                errors,
            )
            require(locator.get("role") == "paper-source-locator", "paper batch: wrong locator role", errors)
            require(locator.get("paper_id") == task_id.upper().split("-", 1)[0], "paper batch: paper ID mismatch", errors)
            task_ids = paper_batch.get("task_ids")
            expected_task_ids = [
                f"{task_id.upper().split('-', 1)[0]}-T{tier}"
                for tier in range(1, 4)
            ]
            require(
                task_ids == expected_task_ids,
                "paper batch: task IDs must be T1, T2, and T3 in order",
                errors,
            )
            require(
                [item.get("task_id") for item in locator.get("tasks", []) if isinstance(item, dict)]
                == task_ids,
                "paper batch: task inventory mismatch",
                errors,
            )
            for item in locator.get("tasks", []):
                if not isinstance(item, dict):
                    continue
                require(
                    set(item) == {"task_id", "source_locations"}
                    and isinstance(item.get("source_locations"), list)
                    and bool(item.get("source_locations")),
                    "paper batch: malformed task source locator",
                    errors,
                )
            require(locator.get("paper_sha256") == manifest.get("paper", {}).get("sha256"), "paper batch: paper hash mismatch", errors)

    validate_dependency_reuse(manifest, input_paths, errors)

    require(task_dir.is_dir(), f"missing task directory: {task_dir}", errors)
    return manifest, errors


def coverage_ids(output: dict[str, Any], field: str, label: str, expected: list[str], errors: list[str]) -> None:
    records = output.get(field)
    if not isinstance(records, list):
        errors.append(f"{label}: {field} must be a list")
        return
    actual = [record.get("id") for record in records if isinstance(record, dict)]
    require(actual == expected, f"{label}: {field} IDs are missing, duplicated, or out of order", errors)


def validate_classification(output: dict[str, Any], label: str, first_key: str, second_key: str, errors: list[str]) -> None:
    classification = output.get("classification")
    accepted = output.get("accepted")
    require(classification in CLASSIFICATIONS, f"{label}: invalid classification", errors)
    require(accepted == (classification in ACCEPTED_CLASSIFICATIONS), f"{label}: accepted flag contradicts classification", errors)
    implications = output.get("implications")
    if not isinstance(implications, dict):
        errors.append(f"{label}: missing implications")
        return
    first = implications.get(first_key)
    second = implications.get(second_key)
    if not isinstance(first, dict) or not isinstance(second, dict):
        errors.append(f"{label}: malformed implications")
        return
    first_verdict = first.get("verdict")
    second_verdict = second.get("verdict")
    if first_verdict not in {"yes", "no", "unclear"} or second_verdict not in {"yes", "no", "unclear"}:
        errors.append(f"{label}: invalid implication verdict")
        return
    expected = implication_classification(first_verdict, second_verdict)
    require(classification == expected, f"{label}: implication verdicts require {expected}, got {classification}", errors)


def output_requires_adjudication(
    source: dict[str, Any],
    blind: dict[str, Any],
    direct: dict[str, Any],
    roundtrip: dict[str, Any],
    *,
    schema_version: str = AUDIT_SCHEMA_VERSION,
) -> list[str]:
    reasons: list[str] = []
    if direct.get("classification") != roundtrip.get("classification"):
        reasons.append("judge classifications differ")
    if direct.get("requires_adjudication") is True:
        reasons.append("direct judge requested adjudication")
    if roundtrip.get("requires_adjudication") is True:
        reasons.append("round-trip judge requested adjudication")
    if direct.get("classification") == "undetermined":
        reasons.append("direct judge classification is undetermined")
    if roundtrip.get("classification") == "undetermined":
        reasons.append("round-trip judge classification is undetermined")
    if schema_version == "highambench-faithfulness-0.1":
        if source.get("ambiguities"):
            reasons.append("source contract contains ambiguity")
        if blind.get("ambiguities"):
            reasons.append("blind translation contains ambiguity")
    # In v0.2, source and translation ambiguities are evidence for both judges.
    # They trigger adjudication only when a judge leaves them unresolved.
    for record in blind.get("dependency_coverage", []):
        if isinstance(record, dict) and record.get("status") == "unclear":
            reasons.append(f"blind dependency {record.get('id')} is unclear")
    for label, output in (("direct", direct), ("round-trip", roundtrip)):
        for field in ("dependency_coverage", "semantic_checklist"):
            for record in output.get(field, []):
                if isinstance(record, dict) and record.get("status") == "unclear":
                    reasons.append(f"{label} {record.get('id')} is unclear")
    return list(dict.fromkeys(reasons))


def validate_complete(task_id: str) -> tuple[dict[str, Any], list[str]]:
    manifest, errors = validate_prepared(task_id)
    _, audit_dir = task_paths(task_id)
    output_dir = audit_dir / "agent_outputs"
    files = {
        "source": output_dir / "source_contract.json",
        "blind": output_dir / "blind_translation.json",
        "direct": output_dir / "direct_judge.json",
        "roundtrip": output_dir / "roundtrip_judge.json",
    }
    outputs: dict[str, dict[str, Any]] = {}
    for label, path in files.items():
        if not path.is_file():
            errors.append(f"missing {label} output: {path}")
        else:
            outputs[label] = load_json(path)
    if len(outputs) != len(files):
        return manifest, errors

    source = outputs["source"]
    blind = outputs["blind"]
    direct = outputs["direct"]
    roundtrip = outputs["roundtrip"]
    expected_roles = {
        "source": "source-contract",
        "blind": "blind-translation",
        "direct": "direct-judge",
        "roundtrip": "roundtrip-judge",
    }
    for label, output in outputs.items():
        require(output.get("schema_version") == manifest.get("schema_version"), f"{label}: wrong schema version", errors)
        require(output.get("role") == expected_roles[label], f"{label}: wrong role", errors)
    validate_role_fn = None
    try:
        try:
            from .validate_agent_output import validate_role as validate_role_fn
        except ImportError:
            from validate_agent_output import (
                validate_role as validate_role_fn,  # type: ignore
            )
        for role in expected_roles.values():
            try:
                validate_role_fn(task_id, role)
            except AuditValidationError as error:
                errors.append(f"{role}: role validation failed\n{error}")
    except ImportError as error:
        errors.append(f"cannot load role validator: {error}")
    for label in ("source", "direct", "roundtrip"):
        require(outputs[label].get("task_id") == task_id.upper(), f"{label}: task ID mismatch", errors)

    paper_hash = manifest.get("paper", {}).get("sha256")
    direct_hash = manifest.get("inputs", {}).get(
        "direct_review_packet",
        manifest.get("inputs", {}).get("declaration_dossier", {}),
    ).get("sha256")
    blind_hash = manifest.get("inputs", {}).get(
        "blind_review_packet",
        manifest.get("inputs", {}).get("blind_dossier", {}),
    ).get("sha256")
    require(source.get("paper_sha256") == paper_hash, "source: paper hash mismatch", errors)
    require(direct.get("paper_sha256") == paper_hash, "direct: paper hash mismatch", errors)
    require(roundtrip.get("paper_sha256") == paper_hash, "round-trip: paper hash mismatch", errors)
    require(blind.get("dossier_sha256") == blind_hash, "blind: dossier hash mismatch", errors)
    require(direct.get("dossier_sha256") == direct_hash, "direct: dossier hash mismatch", errors)
    require(
        roundtrip.get("blind_translation_sha256") == sha256_file(files["blind"]),
        "round-trip: blind translation hash mismatch",
        errors,
    )

    dependencies = manifest.get("dependencies", [])
    dependency_id_list = [item.get("id") for item in dependencies if isinstance(item, dict)]
    coverage_ids(blind, "dependency_coverage", "blind", dependency_id_list, errors)
    coverage_ids(direct, "dependency_coverage", "direct", dependency_id_list, errors)
    expected_semantic = [item[0] for item in SEMANTIC_CHECKS]
    coverage_ids(direct, "semantic_checklist", "direct", expected_semantic, errors)
    coverage_ids(roundtrip, "semantic_checklist", "round-trip", expected_semantic, errors)

    validate_classification(direct, "direct", "lean_implies_paper", "paper_implies_lean", errors)
    validate_classification(
        roundtrip,
        "round-trip",
        "translation_implies_paper",
        "paper_implies_translation",
        errors,
    )

    reasons = output_requires_adjudication(
        source,
        blind,
        direct,
        roundtrip,
        schema_version=str(manifest.get("schema_version")),
    )
    adjudicator_path = output_dir / "adjudicator.json"
    adjudicator: dict[str, Any] | None = None
    if reasons:
        if not adjudicator_path.is_file():
            errors.append("adjudication required but agent_outputs/adjudicator.json is missing")
        else:
            adjudicator = load_json(adjudicator_path)
            require(adjudicator.get("role") == "adjudicator", "adjudicator: wrong role", errors)
            require(adjudicator.get("task_id") == task_id.upper(), "adjudicator: task ID mismatch", errors)
            validate_classification(adjudicator, "adjudicator", "lean_implies_paper", "paper_implies_lean", errors)
            require(
                set(adjudicator.get("trigger", [])) == set(reasons),
                "adjudicator: trigger list does not match computed reasons",
                errors,
            )
            if validate_role_fn is not None:
                try:
                    validate_role_fn(task_id, "adjudicator")
                except AuditValidationError as error:
                    errors.append(f"adjudicator: role validation failed\n{error}")
    elif adjudicator_path.exists():
        errors.append("adjudicator output exists although the recorded judgments do not trigger it")

    decision_path = audit_dir / "decision.json"
    report_path = audit_dir / "report.md"
    if not decision_path.is_file():
        errors.append("missing decision.json")
    else:
        decision = load_json(decision_path)
        require(decision.get("schema_version") == manifest.get("schema_version"), "decision: wrong schema version", errors)
        require(decision.get("role") == "final-decision", "decision: wrong role", errors)
        require(decision.get("task_id") == task_id.upper(), "decision: task ID mismatch", errors)
        expected_classification = (
            adjudicator.get("classification") if adjudicator is not None else direct.get("classification")
        )
        require(decision.get("classification") == expected_classification, "decision: final classification mismatch", errors)
        require(decision.get("adjudicated") == bool(reasons), "decision: adjudicated flag mismatch", errors)
        require(
            decision.get("adjudication_reasons") == reasons,
            "decision: adjudication reasons mismatch",
            errors,
        )
        require(
            decision.get("judge_classifications")
            == {
                "direct": direct.get("classification"),
                "roundtrip": roundtrip.get("classification"),
            },
            "decision: judge classification record mismatch",
            errors,
        )
        require(
            decision.get("accepted") == (decision.get("classification") in ACCEPTED_CLASSIFICATIONS),
            "decision: accepted flag mismatch",
            errors,
        )
    require(report_path.is_file() and report_path.stat().st_size > 0, "missing or empty report.md", errors)
    require(manifest.get("status") == "completed", "manifest: complete audit must have completed status", errors)
    outputs_record = manifest.get("outputs")
    require(isinstance(outputs_record, dict), "manifest: complete audit has no output hashes", errors)
    if isinstance(outputs_record, dict):
        expected_output_labels = {
            "source_contract",
            "blind_translation",
            "direct_judge",
            "roundtrip_judge",
            "decision",
            "report",
        }
        if reasons:
            expected_output_labels.add("adjudicator")
        batch_output_path = output_dir / "paper_source_contract.json"
        if manifest.get("paper_batch") is not None:
            require(
                batch_output_path.is_file(),
                "paper batch audit is missing agent_outputs/paper_source_contract.json",
                errors,
            )
            expected_output_labels.add("paper_source_contract")
        else:
            require(
                not batch_output_path.exists(),
                "non-batch audit contains an unexpected paper source contract",
                errors,
            )
        require(
            set(outputs_record) == expected_output_labels,
            "manifest: output hash inventory is incomplete or contains unexpected entries",
            errors,
        )
        for label, record in outputs_record.items():
            check_recorded_file(record, f"manifest.outputs.{label}", errors)
    return manifest, errors


def validate(task_id: str, phase: str) -> dict[str, Any]:
    manifest, errors = (
        validate_prepared(task_id) if phase == "prepared" else validate_complete(task_id)
    )
    if errors:
        raise AuditValidationError("\n".join(f"- {error}" for error in errors))
    return manifest


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task_id", help="task ID such as P11-T1")
    parser.add_argument("--phase", choices=("prepared", "complete"), default="prepared")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        manifest = validate(args.task_id, args.phase)
    except (OSError, AuditValidationError, ValueError) as error:
        print(f"faithfulness validation error:\n{error}", file=sys.stderr)
        return 2
    print(f"{manifest['task_id']}: {args.phase} audit artifacts valid")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
