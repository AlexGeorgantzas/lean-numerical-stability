#!/usr/bin/env python3
"""Hash-checked ten-task descriptive report across Pilot 29 and Pilot 31.

The two campaigns remain separate provenance. This script never edits either.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

TOOLS = Path(__file__).resolve().parents[1] / "formalization_benchmark" / "tools"
sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, canonical_json_bytes, load_json, sha256_file
from design29_report import _condition


def _sum_ratio(rows: list[dict], field: str, *, geometric: bool = True) -> dict:
    n = sum(row["N"][field] for row in rows)
    l = sum(row["L"][field] for row in rows)
    result = {"N_sum": n, "L_sum": l, "L_over_N_sum": l / n if n else None}
    if geometric:
        ratios = [row["L"][field] / row["N"][field] for row in rows
                  if row["N"][field] > 0 and row["L"][field] > 0]
        result["geometric_mean_L_over_N"] = (
            math.exp(sum(map(math.log, ratios)) / len(ratios)) if ratios else None
        )
    return result


def report(source_root: Path, recovery_root: Path, manifest_path: Path,
           admission_path: Path) -> dict:
    manifest = load_json(manifest_path)
    if manifest.get("schema_version") != "pilot-31-recovery-composite-1":
        raise BenchmarkError("wrong recovery manifest")
    if source_root.resolve() != Path(manifest["source_campaign_root"]).resolve():
        raise BenchmarkError("wrong Pilot 29 root")
    source_path = source_root / "campaign.json"
    recovery_path = recovery_root / "campaign.json"
    if sha256_file(source_path) != manifest["source_campaign_sha256"]:
        raise BenchmarkError("Pilot 29 journal changed")
    source = load_json(source_path)
    recovery = load_json(recovery_path)
    if (source.get("status") != "RUNNING_PARALLEL"
            or recovery.get("status") != "COMPLETE_RECOVERY"
            or recovery.get("schema_version") != "pilot-31-five-pair-recovery-campaign-1"
            or recovery.get("inputs", {}).get("pilot_id")
            != "pilot31-five-pair-recovery"
            or recovery.get("inputs", {}).get("recovery_manifest_sha256")
            != sha256_file(manifest_path)
            or recovery.get("inputs", {}).get("source_campaign_sha256")
            != sha256_file(source_path)
            or hashlib.sha256(canonical_json_bytes(recovery["inputs"])).hexdigest()
            != recovery.get("inputs_sha256")):
        raise BenchmarkError("recovery campaign is incomplete or has changed identity")
    schedule = source["inputs"]["schedule"]
    if schedule != recovery["inputs"]["schedule"] or len(schedule) != 10:
        raise BenchmarkError("ten-task schedule changed")
    preserved = manifest["preserved_pair_report_sha256"]
    partial = manifest["interrupted_partial_pair_report_sha256"]
    remaining = manifest["remaining_task_order"]
    source_entries = {entry["task_id"]: entry for entry in source["pairs"]}
    recovery_entries = {entry["task_id"]: entry for entry in recovery["pairs"]}
    if (set(source_entries) != set(preserved)
            or set(recovery_entries) != set(remaining)
            or set(schedule) != set(preserved) | set(remaining)
            or len(source["pairs"]) != 5 or len(recovery["pairs"]) != 5):
        raise BenchmarkError("ten-task partition is incomplete or duplicated")
    for task_id, digest in partial.items():
        if (sha256_file(source_root / task_id / "pair-report.json") != digest
                or load_json(source_root / task_id / "pair-report.json")
                .get("status") != "RUNNING"):
            raise BenchmarkError(f"interrupted source evidence changed: {task_id}")
    admission = load_json(admission_path)
    if sha256_file(admission_path) != source["inputs"]["admission_sha256"]:
        raise BenchmarkError("admission changed")
    rows: list[dict] = []
    for task_id in schedule:
        is_recovery = task_id in recovery_entries
        root = recovery_root if is_recovery else source_root
        entry = (recovery_entries if is_recovery else source_entries)[task_id]
        pair_path = root / task_id / "pair-report.json"
        if (sha256_file(pair_path) != entry["pair_report_sha256"]
                or (not is_recovery and
                    entry["pair_report_sha256"] != preserved[task_id])):
            raise BenchmarkError(f"pair report hash changed: {task_id}")
        pair = load_json(pair_path)
        if pair.get("task_id") != task_id:
            raise BenchmarkError(f"wrong pair identity: {task_id}")
        conditions = pair.get("conditions", {})
        row = {
            "task_id": task_id,
            "source_pilot": "Pilot 31 recovery" if is_recovery else "Pilot 29 sealed",
            "restarted_after_reboot": task_id in partial,
            "stratum": admission["tasks"][task_id]["model_stratum"],
            "pair_status": pair.get("status"),
            "proof_pair_status": pair.get("proof_pair_status"),
            "direct_numstability_names_in_statement":
                entry.get("treatment_uptake", {}).get("direct_reached", []),
            "N": _condition(conditions["R0"]) if "R0" in conditions else None,
            "L": _condition(conditions["R1"]) if "R1" in conditions else None,
        }
        row["paired_statement_eligible"] = (
            row["pair_status"] == "AUDITED_FAITHFUL_PAIR"
            and row["N"] is not None and row["L"] is not None
        )
        row["paired_proof_eligible"] = (
            row["paired_statement_eligible"]
            and row["proof_pair_status"] == "BOTH_PROVED_FROZEN_STATEMENTS"
        )
        rows.append(row)
    faithful = [row for row in rows if row["paired_statement_eligible"]]
    proved = [row for row in rows if row["paired_proof_eligible"]]
    summary = {
        "scheduled_tasks": len(rows),
        "source_pilot29_pairs": 5,
        "recovery_pilot31_pairs": 5,
        "restarted_after_reboot_pairs": len(partial),
        "faithful_statement_pairs": len(faithful),
        "paired_complete_proofs": len(proved),
        "L_direct_statement_reach_tasks": sum(
            bool(row["direct_numstability_names_in_statement"]) for row in rows
        ),
        "L_shorter_raw_statement_tasks": sum(
            row["L"]["statement_lines"] < row["N"]["statement_lines"]
            for row in faithful
        ),
        "L_shorter_code_statement_tasks": sum(
            row["L"]["statement_code_lines"]
            < row["N"]["statement_code_lines"] for row in faithful
        ),
        "L_shorter_raw_proof_tasks": sum(
            row["L"]["proof_raw_lines"] < row["N"]["proof_raw_lines"]
            for row in proved
        ),
        "L_shorter_code_proof_tasks": sum(
            row["L"]["proof_code_lines"] < row["N"]["proof_code_lines"]
            for row in proved
        ),
    }
    for field in ("statement_lines", "statement_code_lines"):
        summary[field] = _sum_ratio(faithful, field)
    for field in ("proof_raw_lines", "proof_code_lines",
                  "contestant_system_wall_seconds", "net_new_tokens",
                  "task_retrieval_seconds"):
        summary[field] = _sum_ratio(
            proved, field, geometric=field != "task_retrieval_seconds"
        )
    return {
        "schema_version": "pilot-31-recovery-composite-report-1",
        "scientific_status": "OUTCOME_AWARE_INTERRUPTION_RECOVERY_NOT_CONFIRMATORY",
        "source_campaign_sha256": sha256_file(source_path),
        "recovery_campaign_sha256": sha256_file(recovery_path),
        "recovery_manifest_sha256": sha256_file(manifest_path),
        "summary": summary,
        "tasks": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--recovery-root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--admission", required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(report(args.source_root, args.recovery_root,
                            args.manifest, args.admission), indent=2,
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 31 composite report error: {error}", file=sys.stderr)
        raise SystemExit(2)
