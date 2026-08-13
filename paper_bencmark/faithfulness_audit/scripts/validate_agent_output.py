#!/usr/bin/env python3
"""Validate one agent's JSON before the next audit phase consumes it."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

try:
    from .common import AUDIT_SCHEMA_VERSION, SEMANTIC_CHECKS, sha256_file
    from .validate_audit import (
        AuditValidationError,
        coverage_ids,
        load_json,
        task_paths,
        validate_classification,
        validate_prepared,
    )
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        AUDIT_SCHEMA_VERSION,
        SEMANTIC_CHECKS,
        sha256_file,
    )
    from validate_audit import (  # type: ignore
        AuditValidationError,
        coverage_ids,
        load_json,
        task_paths,
        validate_classification,
        validate_prepared,
    )


ROLE_FILES = {
    "source-contract": "source_contract.json",
    "blind-translation": "blind_translation.json",
    "direct-judge": "direct_judge.json",
    "roundtrip-judge": "roundtrip_judge.json",
    "adjudicator": "adjudicator.json",
}

TOP_LEVEL_REQUIRED = {
    "source-contract": {
        "schema_version", "role", "task_id", "paper_sha256", "source_evidence",
        "statement", "undebatable_constraints", "ambiguities", "contract_plain_english",
    },
    "blind-translation": {
        "schema_version", "role", "dossier_sha256", "dependency_coverage",
        "translation", "restrictions_and_vacuity_risks", "ambiguities",
    },
    "direct-judge": {
        "schema_version", "role", "task_id", "paper_sha256", "dossier_sha256",
        "dependency_coverage", "semantic_checklist", "implications", "classification",
        "accepted", "requires_adjudication", "findings", "rationale",
    },
    "roundtrip-judge": {
        "schema_version", "role", "task_id", "paper_sha256",
        "blind_translation_sha256", "semantic_checklist", "implications",
        "classification", "accepted", "requires_adjudication", "findings", "rationale",
    },
    "adjudicator": {
        "schema_version", "role", "task_id", "trigger", "resolved_items",
        "implications", "classification", "accepted", "remaining_uncertainties",
        "findings", "rationale",
    },
}


def require(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def require_string(value: dict[str, Any], key: str, label: str, errors: list[str]) -> None:
    require(isinstance(value.get(key), str) and bool(value.get(key)), f"{label}: {key} must be a nonempty string", errors)


def require_string_list(
    value: dict[str, Any],
    key: str,
    label: str,
    errors: list[str],
    *,
    nonempty: bool = False,
) -> None:
    items = value.get(key)
    valid = isinstance(items, list) and (bool(items) or not nonempty)
    if isinstance(items, list):
        valid = valid and all(isinstance(item, str) and bool(item) for item in items)
    require(valid, f"{label}: {key} must be {'a nonempty ' if nonempty else 'a '}list of nonempty strings", errors)


def validate_implication_reasons(output: dict[str, Any], keys: tuple[str, str], role: str, errors: list[str]) -> None:
    implications = output.get("implications")
    if not isinstance(implications, dict):
        return
    require(set(implications) == set(keys), f"{role}: implication keys are incomplete or unexpected", errors)
    for key in keys:
        record = implications.get(key)
        require(isinstance(record, dict), f"{role}: {key} must be an object", errors)
        if isinstance(record, dict):
            require(set(record) == {"verdict", "reasoning"}, f"{role}: {key} fields are incomplete or unexpected", errors)
            require_string(record, "reasoning", f"{role} {key}", errors)


def validate_dependency_names(
    output: dict[str, Any],
    dependencies: list[dict[str, Any]],
    label: str,
    errors: list[str],
) -> None:
    records = output.get("dependency_coverage")
    if not isinstance(records, list) or len(records) != len(dependencies):
        return
    for expected, actual in zip(dependencies, records, strict=True):
        if not isinstance(actual, dict):
            errors.append(f"{label}: dependency record {expected['id']} is not an object")
            continue
        if label == "blind-translation":
            expected_name = expected.get("blind_name")
            required = ("meaning", "effect_on_target")
            statuses = {"understood", "unclear"}
            expected_fields = {
                "id",
                "name",
                "meaning",
                "effect_on_target",
                "status",
            }
        else:
            expected_name = expected.get("name")
            required = ("interpretation", "effect_on_target", "paper_match")
            statuses = {"pass", "fail", "unclear", "not-applicable"}
            expected_fields = {
                "id",
                "name",
                "interpretation",
                "effect_on_target",
                "paper_match",
                "status",
            }
        require(
            set(actual) == expected_fields,
            f"{label}: {expected['id']} fields are incomplete or unexpected",
            errors,
        )
        require(actual.get("name") == expected_name, f"{label}: {expected['id']} name mismatch", errors)
        for key in required:
            require_string(actual, key, f"{label} {expected['id']}", errors)
        require(actual.get("status") in statuses, f"{label}: {expected['id']} invalid status", errors)


def validate_semantic_records(
    output: dict[str, Any], role: str, errors: list[str]
) -> None:
    records = output.get("semantic_checklist")
    if not isinstance(records, list):
        return
    evidence_key = "lean_evidence" if role == "direct-judge" else "translation_evidence"
    expected_fields = {
        "id",
        "status",
        "paper_evidence",
        evidence_key,
        "reasoning",
    }
    for record in records:
        if not isinstance(record, dict):
            errors.append(f"{role}: semantic checklist contains a non-object")
            continue
        item_id = record.get("id", "unknown")
        require(
            set(record) == expected_fields,
            f"{role}: {item_id} fields are incomplete or unexpected",
            errors,
        )
        require(record.get("status") in {"pass", "fail", "unclear", "not-applicable"}, f"{role}: {item_id} invalid status", errors)
        for key in ("paper_evidence", evidence_key, "reasoning"):
            require_string(record, key, f"{role} {item_id}", errors)


def validate_source(output: dict[str, Any], manifest: dict[str, Any], errors: list[str]) -> None:
    require(output.get("task_id") == manifest.get("task_id"), "source-contract: task ID mismatch", errors)
    require(output.get("paper_sha256") == manifest.get("paper", {}).get("sha256"), "source-contract: paper hash mismatch", errors)
    evidence = output.get("source_evidence")
    require(isinstance(evidence, list) and bool(evidence), "source-contract: source_evidence must be nonempty", errors)
    if isinstance(evidence, list):
        for index, record in enumerate(evidence):
            label = f"source-contract source_evidence[{index}]"
            require(isinstance(record, dict), f"{label}: must be an object", errors)
            if not isinstance(record, dict):
                continue
            require(
                set(record).issubset({"pdf_page", "printed_page", "anchor", "observation"})
                and {"pdf_page", "anchor", "observation"}.issubset(record),
                f"{label}: fields are incomplete or unexpected",
                errors,
            )
            require(isinstance(record.get("pdf_page"), int) and record.get("pdf_page", 0) > 0, f"{label}: invalid PDF page", errors)
            require_string(record, "anchor", label, errors)
            require_string(record, "observation", label, errors)
    statement = output.get("statement")
    required = {
        "binders", "hypotheses", "conclusions", "definitions_and_conventions",
        "implicit_context", "algorithm_linkage", "numerical_model", "error_notions",
        "norms", "constants_and_indexing", "higher_order_terms", "exceptional_values",
    }
    require(isinstance(statement, dict), "source-contract: statement must be an object", errors)
    if isinstance(statement, dict):
        require(set(statement) == required, "source-contract: statement sections are incomplete or unexpected", errors)
        for key in required - {"algorithm_linkage"}:
            require_string_list(statement, key, "source-contract statement", errors, nonempty=(key == "conclusions"))
        require_string(statement, "algorithm_linkage", "source-contract statement", errors)
    require_string_list(output, "undebatable_constraints", "source-contract", errors, nonempty=True)
    require(isinstance(output.get("ambiguities"), list), "source-contract: ambiguities must be a list", errors)


def validate_blind(output: dict[str, Any], manifest: dict[str, Any], errors: list[str]) -> None:
    require(output.get("dossier_sha256") == manifest.get("inputs", {}).get("blind_dossier", {}).get("sha256"), "blind-translation: dossier hash mismatch", errors)
    translation = output.get("translation")
    required = {"binders", "hypotheses", "conclusions", "mathematical_definitions", "proposition_plain_english"}
    require(isinstance(translation, dict), "blind-translation: translation must be an object", errors)
    if isinstance(translation, dict):
        require(set(translation) == required, "blind-translation: translation sections are incomplete or unexpected", errors)
        for key in ("binders", "hypotheses", "conclusions", "mathematical_definitions"):
            require_string_list(translation, key, "blind-translation translation", errors, nonempty=(key == "conclusions"))
        require_string(translation, "proposition_plain_english", "blind-translation translation", errors)
    require_string_list(output, "restrictions_and_vacuity_risks", "blind-translation", errors)
    require_string_list(output, "ambiguities", "blind-translation", errors)


def validate_role(task_id: str, role: str, path: Path | None = None) -> dict[str, Any]:
    manifest, prepared_errors = validate_prepared(task_id)
    errors = list(prepared_errors)
    _, audit_dir = task_paths(task_id)
    output_path = path or (audit_dir / "agent_outputs" / ROLE_FILES[role])
    if not output_path.is_file():
        raise AuditValidationError(f"missing {role} output: {output_path}")
    output = load_json(output_path)
    missing = TOP_LEVEL_REQUIRED[role] - set(output)
    require(not missing, f"{role}: missing top-level keys {sorted(missing)}", errors)
    extra = set(output) - TOP_LEVEL_REQUIRED[role]
    require(not extra, f"{role}: unexpected top-level keys {sorted(extra)}", errors)
    require(output.get("schema_version") == AUDIT_SCHEMA_VERSION, f"{role}: schema version mismatch", errors)
    require(output.get("role") == role, f"{role}: role field mismatch", errors)

    dependencies = [item for item in manifest.get("dependencies", []) if isinstance(item, dict)]
    dependency_id_list = [item["id"] for item in dependencies]
    semantic_ids = [item[0] for item in SEMANTIC_CHECKS]
    if role == "source-contract":
        validate_source(output, manifest, errors)
        require_string(output, "contract_plain_english", role, errors)
    elif role == "blind-translation":
        coverage_ids(output, "dependency_coverage", role, dependency_id_list, errors)
        validate_dependency_names(output, dependencies, role, errors)
        validate_blind(output, manifest, errors)
    elif role == "direct-judge":
        require(output.get("task_id") == manifest.get("task_id"), f"{role}: task ID mismatch", errors)
        require(output.get("paper_sha256") == manifest.get("paper", {}).get("sha256"), f"{role}: paper hash mismatch", errors)
        require(output.get("dossier_sha256") == manifest.get("inputs", {}).get("declaration_dossier", {}).get("sha256"), f"{role}: dossier hash mismatch", errors)
        coverage_ids(output, "dependency_coverage", role, dependency_id_list, errors)
        validate_dependency_names(output, dependencies, role, errors)
        coverage_ids(output, "semantic_checklist", role, semantic_ids, errors)
        validate_semantic_records(output, role, errors)
        validate_classification(output, role, "lean_implies_paper", "paper_implies_lean", errors)
        validate_implication_reasons(output, ("lean_implies_paper", "paper_implies_lean"), role, errors)
        require(isinstance(output.get("requires_adjudication"), bool), f"{role}: requires_adjudication must be Boolean", errors)
    elif role == "roundtrip-judge":
        blind_path = audit_dir / "agent_outputs" / "blind_translation.json"
        require(output.get("task_id") == manifest.get("task_id"), f"{role}: task ID mismatch", errors)
        require(output.get("paper_sha256") == manifest.get("paper", {}).get("sha256"), f"{role}: paper hash mismatch", errors)
        require(blind_path.is_file(), f"{role}: blind translation file is missing", errors)
        if blind_path.is_file():
            require(output.get("blind_translation_sha256") == sha256_file(blind_path), f"{role}: blind translation hash mismatch", errors)
        coverage_ids(output, "semantic_checklist", role, semantic_ids, errors)
        validate_semantic_records(output, role, errors)
        validate_classification(output, role, "translation_implies_paper", "paper_implies_translation", errors)
        validate_implication_reasons(
            output,
            ("translation_implies_paper", "paper_implies_translation"),
            role,
            errors,
        )
        require(isinstance(output.get("requires_adjudication"), bool), f"{role}: requires_adjudication must be Boolean", errors)
    else:
        require(output.get("task_id") == manifest.get("task_id"), "adjudicator: task ID mismatch", errors)
        validate_classification(output, role, "lean_implies_paper", "paper_implies_lean", errors)
        validate_implication_reasons(output, ("lean_implies_paper", "paper_implies_lean"), role, errors)
        require(isinstance(output.get("trigger"), list) and bool(output.get("trigger")), "adjudicator: trigger must be nonempty", errors)
        require(isinstance(output.get("resolved_items"), list) and bool(output.get("resolved_items")), "adjudicator: resolved_items must be nonempty", errors)

    if role not in {"source-contract", "blind-translation"}:
        require_string(output, "rationale", role, errors)
    if errors:
        raise AuditValidationError("\n".join(f"- {error}" for error in errors))
    return output


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task_id", help="task ID such as P11-T1")
    parser.add_argument("role", choices=tuple(ROLE_FILES))
    parser.add_argument("--file", type=Path, help="validate a non-default output path")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        validate_role(args.task_id.upper(), args.role, args.file)
    except (OSError, AuditValidationError, ValueError) as error:
        print(f"agent-output validation error:\n{error}", file=sys.stderr)
        return 2
    print(f"{args.task_id.upper()} {args.role}: valid")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
