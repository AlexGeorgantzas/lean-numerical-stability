#!/usr/bin/env python3
"""Determine adjudication needs and finalize a completed faithfulness audit."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from .common import ACCEPTED_CLASSIFICATIONS, sha256_file
    from .validate_agent_output import validate_role
    from .validate_audit import (
        AuditValidationError,
        load_json,
        output_requires_adjudication,
        task_paths,
        validate,
        validate_prepared,
    )
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        ACCEPTED_CLASSIFICATIONS,
        sha256_file,
    )
    from validate_agent_output import validate_role  # type: ignore
    from validate_audit import (  # type: ignore
        AuditValidationError,
        load_json,
        output_requires_adjudication,
        task_paths,
        validate,
        validate_prepared,
    )


SCRIPT_DIR = Path(__file__).resolve().parent
REPOSITORY_ROOT = SCRIPT_DIR.parents[2]
REPORT_TEMPLATE = SCRIPT_DIR.parent / "templates" / "report.md"


class FinalizationError(RuntimeError):
    """Raised when judge outputs are insufficient for a final decision."""


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def load_core_outputs(audit_dir: Path) -> tuple[dict[str, Any], ...]:
    output_dir = audit_dir / "agent_outputs"
    paths = (
        output_dir / "source_contract.json",
        output_dir / "blind_translation.json",
        output_dir / "direct_judge.json",
        output_dir / "roundtrip_judge.json",
    )
    missing = [path for path in paths if not path.is_file()]
    if missing:
        raise FinalizationError("missing agent outputs: " + ", ".join(str(path) for path in missing))
    return tuple(load_json(path) for path in paths)


def adjudication_state(task_id: str) -> tuple[list[str], Path, tuple[dict[str, Any], ...]]:
    manifest, errors = validate_prepared(task_id)
    if errors:
        raise FinalizationError("prepared artifacts are invalid:\n" + "\n".join(errors))
    _, audit_dir = task_paths(task_id)
    outputs = load_core_outputs(audit_dir)
    for role in (
        "source-contract",
        "blind-translation",
        "direct-judge",
        "roundtrip-judge",
    ):
        validate_role(task_id, role)
    reasons = output_requires_adjudication(
        *outputs, schema_version=str(manifest.get("schema_version"))
    )
    return reasons, audit_dir, outputs


def finding_lines(findings: list[Any]) -> str:
    if not findings:
        return "No findings were recorded."
    lines: list[str] = []
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        severity = finding.get("severity", "note")
        category = finding.get("category", "unspecified")
        impact = finding.get("impact", finding.get("evidence", "No impact supplied."))
        lines.append(f"- **{severity} / {category}:** {impact}")
    return "\n".join(lines) if lines else "No findings were recorded."


def implication_lines(implications: dict[str, Any]) -> str:
    lines: list[str] = []
    for key, value in implications.items():
        if not isinstance(value, dict):
            continue
        label = key.replace("_", " ").capitalize()
        lines.append(f"- **{label}:** `{value.get('verdict')}`. {value.get('reasoning', '')}")
    return "\n".join(lines) if lines else "No implication decision was recorded."


def checklist_table(direct: dict[str, Any], roundtrip: dict[str, Any]) -> str:
    direct_by_id = {
        item.get("id"): item for item in direct.get("semantic_checklist", []) if isinstance(item, dict)
    }
    roundtrip_by_id = {
        item.get("id"): item for item in roundtrip.get("semantic_checklist", []) if isinstance(item, dict)
    }
    lines = ["| Check | Direct | Round-trip |", "|---|---|---|"]
    for item_id in sorted(set(direct_by_id) | set(roundtrip_by_id)):
        lines.append(
            f"| `{item_id}` | `{direct_by_id.get(item_id, {}).get('status', 'missing')}` "
            f"| `{roundtrip_by_id.get(item_id, {}).get('status', 'missing')}` |"
        )
    return "\n".join(lines)


def dependency_summary(blind: dict[str, Any], direct: dict[str, Any]) -> str:
    blind_records = blind.get("dependency_coverage", [])
    direct_records = direct.get("dependency_coverage", [])
    blind_unclear = [item.get("id") for item in blind_records if isinstance(item, dict) and item.get("status") == "unclear"]
    direct_unresolved = [
        item.get("id")
        for item in direct_records
        if isinstance(item, dict) and item.get("status") in {"fail", "unclear"}
    ]
    blind_reused = sum(
        1 for item in blind_records if isinstance(item, dict) and "reuse_sha256" in item
    )
    direct_reused = sum(
        1 for item in direct_records if isinstance(item, dict) and "reuse_sha256" in item
    )
    return (
        f"- Blind translator covered `{len(blind_records)}` dependencies "
        f"(`{blind_reused}` hash-reused meanings); unclear: "
        f"`{', '.join(blind_unclear) if blind_unclear else 'none'}`.\n"
        f"- Direct judge covered `{len(direct_records)}` dependencies "
        f"(`{direct_reused}` hash-reused interpretations); failing or unclear: "
        f"`{', '.join(direct_unresolved) if direct_unresolved else 'none'}`."
    )


def artifact_lines(audit_dir: Path) -> str:
    files = sorted(path for path in audit_dir.rglob("*") if path.is_file())
    return "\n".join(
        f"- `{path.relative_to(REPOSITORY_ROOT).as_posix()}` (`{sha256_file(path)}`)"
        for path in files
        if path.name not in {"manifest.json", "report.md"}
    )


def render_report(
    audit_dir: Path,
    manifest: dict[str, Any],
    decision: dict[str, Any],
    blind: dict[str, Any],
    direct: dict[str, Any],
    roundtrip: dict[str, Any],
) -> str:
    template = REPORT_TEMPLATE.read_text(encoding="utf-8")
    uncertainties = decision.get("remaining_uncertainties", [])
    replacements = {
        "{{TASK_ID}}": decision["task_id"],
        "{{CLASSIFICATION}}": decision["classification"],
        "{{ACCEPTED}}": str(decision["accepted"]).lower(),
        "{{ADJUDICATED}}": str(decision["adjudicated"]).lower(),
        "{{TARGET_SHA256}}": manifest["target"]["sha256"],
        "{{PAPER_SHA256}}": manifest["paper"]["sha256"],
        "{{RATIONALE}}": decision["rationale"],
        "{{IMPLICATIONS}}": implication_lines(decision["implications"]),
        "{{FINDINGS}}": finding_lines(decision["findings"]),
        "{{SEMANTIC_CHECKLIST}}": checklist_table(direct, roundtrip),
        "{{DEPENDENCY_COVERAGE}}": dependency_summary(blind, direct),
        "{{UNCERTAINTIES}}": (
            "\n".join(f"- {item}" for item in uncertainties)
            if uncertainties
            else "No remaining uncertainties were recorded."
        ),
        "{{ARTIFACTS}}": artifact_lines(audit_dir),
    }
    for marker, value in replacements.items():
        template = template.replace(marker, value)
    return template.rstrip() + "\n"


def finalize(task_id: str) -> Path:
    reasons, audit_dir, outputs = adjudication_state(task_id)
    _source, blind, direct, roundtrip = outputs
    manifest_path = audit_dir / "manifest.json"
    manifest = load_json(manifest_path)
    adjudicator_path = audit_dir / "agent_outputs" / "adjudicator.json"
    adjudicator: dict[str, Any] | None = None
    if reasons:
        if not adjudicator_path.is_file():
            raise FinalizationError(
                "adjudication required before finalization:\n"
                + "\n".join(f"- {reason}" for reason in reasons)
            )
        adjudicator = load_json(adjudicator_path)
        validate_role(task_id, "adjudicator")
        if set(adjudicator.get("trigger", [])) != set(reasons):
            raise FinalizationError(
                "adjudicator trigger list does not match the computed adjudication reasons"
            )
    elif adjudicator_path.exists():
        raise FinalizationError("unexpected adjudicator output: no adjudication trigger is recorded")

    final = adjudicator if adjudicator is not None else direct
    if adjudicator is None and direct.get("classification") != roundtrip.get("classification"):
        raise FinalizationError("judges disagree but no adjudicator output is available")
    classification = final.get("classification")
    if not isinstance(classification, str):
        raise FinalizationError("final source has no classification")
    findings = (
        final.get("findings", [])
        if adjudicator is not None
        else [*direct.get("findings", []), *roundtrip.get("findings", [])]
    )
    completed_at = datetime.now(timezone.utc).isoformat()
    decision = {
        "schema_version": manifest["schema_version"],
        "role": "final-decision",
        "task_id": task_id.upper(),
        "completed_at_utc": completed_at,
        "adjudicated": adjudicator is not None,
        "adjudication_reasons": reasons,
        "judge_classifications": {
            "direct": direct.get("classification"),
            "roundtrip": roundtrip.get("classification"),
        },
        "implications": final.get("implications", {}),
        "classification": classification,
        "accepted": classification in ACCEPTED_CLASSIFICATIONS,
        "findings": findings,
        "remaining_uncertainties": final.get("remaining_uncertainties", []),
        "rationale": final.get("rationale", ""),
    }
    decision_path = audit_dir / "decision.json"
    write_json(decision_path, decision)

    previous_manifest = dict(manifest)
    report_path = audit_dir / "report.md"
    report_path.write_text(
        render_report(audit_dir, manifest, decision, blind, direct, roundtrip),
        encoding="utf-8",
    )
    output_files = {
        "source_contract": audit_dir / "agent_outputs" / "source_contract.json",
        "blind_translation": audit_dir / "agent_outputs" / "blind_translation.json",
        "direct_judge": audit_dir / "agent_outputs" / "direct_judge.json",
        "roundtrip_judge": audit_dir / "agent_outputs" / "roundtrip_judge.json",
        "decision": decision_path,
        "report": report_path,
    }
    if adjudicator is not None:
        output_files["adjudicator"] = adjudicator_path
    if manifest.get("paper_batch") is not None:
        batch_path = audit_dir / "agent_outputs" / "paper_source_contract.json"
        if not batch_path.is_file():
            raise FinalizationError("paper-level source contract is missing")
        output_files["paper_source_contract"] = batch_path
    manifest["status"] = "completed"
    manifest["completed_at_utc"] = completed_at
    manifest["outputs"] = {
        label: {
            "path": path.relative_to(REPOSITORY_ROOT).as_posix(),
            "sha256": sha256_file(path),
        }
        for label, path in output_files.items()
    }
    write_json(manifest_path, manifest)
    try:
        validate(task_id, "complete")
    except Exception:
        write_json(manifest_path, previous_manifest)
        raise
    return report_path


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task_id", help="task ID such as P11-T1")
    parser.add_argument(
        "--check-adjudication",
        action="store_true",
        help="report whether a fresh adjudicator is required without writing final files",
    )
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        if args.check_adjudication:
            reasons, _, _ = adjudication_state(args.task_id)
            print(json.dumps({"required": bool(reasons), "reasons": reasons}, indent=2))
            return 3 if reasons else 0
        report = finalize(args.task_id)
    except (OSError, AuditValidationError, FinalizationError, ValueError) as error:
        print(f"faithfulness finalization error:\n{error}", file=sys.stderr)
        return 2
    print(report.relative_to(REPOSITORY_ROOT).as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
