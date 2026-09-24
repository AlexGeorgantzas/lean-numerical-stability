#!/usr/bin/env python3
"""Hash-checked descriptive composite across three distinct frozen campaigns."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

TOOLS = Path(__file__).resolve().parents[1] / "formalization_benchmark" / "tools"
sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, canonical_json_bytes, load_json, sha256_file
from design29_report import _condition


def report(root29: Path, root31: Path, root32: Path,
           manifest_path: Path, admission_path: Path) -> dict:
    manifest = load_json(manifest_path)
    if manifest.get("schema_version") != "pilot-32-one-pair-recovery-1":
        raise BenchmarkError("wrong Pilot 32 manifest")
    prior = load_json(
        Path(__file__).resolve().parents[2] / manifest["pilot29_manifest"])
    if (root29.resolve() != Path(prior["source_campaign_root"]).resolve()
            or root31.resolve()
            != Path(manifest["pilot31_campaign_root"]).resolve()):
        raise BenchmarkError("source roots changed")
    if (sha256_file(root29 / "campaign.json") != prior["source_campaign_sha256"]
            or sha256_file(root31 / "campaign.json")
            != manifest["pilot31_campaign_sha256"]):
        raise BenchmarkError("source journal changed")
    j29 = load_json(root29 / "campaign.json")
    j31 = load_json(root31 / "campaign.json")
    j32 = load_json(root32 / "campaign.json")
    if (j29.get("status") != "RUNNING_PARALLEL"
            or j31.get("status") != "RUNNING_RECOVERY"
            or j32.get("status") not in
            ("COMPLETE_ONE_PAIR_RECOVERY", "COMPLETE_ONE_PAIR_WITH_INCIDENT")
            or j32.get("schema_version")
            != "pilot-32-one-pair-recovery-campaign-1"
            or j31.get("inputs_sha256")
            != manifest["pilot31_input_identity_sha256"]
            or j32.get("inputs", {}).get("recovery_manifest_sha256")
            != sha256_file(manifest_path)
            or j32.get("inputs", {}).get("pilot31_campaign_sha256")
            != manifest["pilot31_campaign_sha256"]
            or hashlib.sha256(canonical_json_bytes(j32["inputs"])).hexdigest()
            != j32.get("inputs_sha256")):
        raise BenchmarkError("campaign identity or completion check failed")
    schedule = j29["inputs"]["schedule"]
    if (len(schedule) != 10 or j31["inputs"]["schedule"] != schedule
            or j32["inputs"]["schedule"] != schedule
            or sha256_file(admission_path)
            != j29["inputs"]["admission_sha256"]):
        raise BenchmarkError("schedule or admission changed")
    admission = load_json(admission_path)
    sealed29 = prior["preserved_pair_report_sha256"]
    sealed31 = manifest["pilot31_sealed_pair_report_sha256"]
    task32 = manifest["remaining_task_id"]
    if (set(schedule) != set(sealed29) | set(sealed31) | {task32}
            or len(j29["pairs"]) != 5 or len(j31["pairs"]) != 4
            or len(j32["pairs"]) != 1
            or j32["pairs"][0]["task_id"] != task32):
        raise BenchmarkError("ten-task partition changed")
    for task, digest in prior["interrupted_partial_pair_report_sha256"].items():
        path = root29 / task / "pair-report.json"
        if sha256_file(path) != digest or load_json(path).get("status") != "RUNNING":
            raise BenchmarkError(f"Pilot 29 partial evidence changed: {task}")
    interrupted = root31 / task32 / "pair-report.json"
    if (sha256_file(interrupted)
            != manifest["pilot31_interrupted_pair_report_sha256"]
            or load_json(interrupted).get("status") != "RUNNING"):
        raise BenchmarkError("Pilot 31 partial evidence changed")
    roots = {
        **{task: (root29, "Pilot 29", digest)
           for task, digest in sealed29.items()},
        **{task: (root31, "Pilot 31", digest)
           for task, digest in sealed31.items()},
        task32: (root32, "Pilot 32",
                 j32["pairs"][0]["pair_report_sha256"]),
    }
    entries = {
        **{item["task_id"]: item for item in j29["pairs"]},
        **{item["task_id"]: item for item in j31["pairs"]},
        **{item["task_id"]: item for item in j32["pairs"]},
    }
    rows = []
    for task in schedule:
        root, provenance, digest = roots[task]
        path = root / task / "pair-report.json"
        if (sha256_file(path) != digest
                or entries[task]["pair_report_sha256"] != digest):
            raise BenchmarkError(f"sealed report changed: {task}")
        pair = load_json(path)
        if pair.get("task_id") != task or pair.get("status") == "RUNNING":
            raise BenchmarkError(f"wrong or unsealed pair: {task}")
        conditions = pair.get("conditions", {})
        row = {
            "task_id": task,
            "source_pilot": provenance,
            "stratum": admission["tasks"][task]["model_stratum"],
            "pair_status": pair.get("status"),
            "proof_pair_status": pair.get("proof_pair_status"),
            "direct_numstability_names_in_statement":
                entries[task].get("treatment_uptake", {}).get("direct_reached", []),
            "N": _condition(conditions["R0"]) if "R0" in conditions else None,
            "L": _condition(conditions["R1"]) if "R1" in conditions else None,
        }
        row["paired_statement_eligible"] = (
            row["pair_status"] == "AUDITED_FAITHFUL_PAIR"
            and row["N"] is not None and row["L"] is not None)
        row["paired_proof_eligible"] = (
            row["paired_statement_eligible"]
            and row["proof_pair_status"] == "BOTH_PROVED_FROZEN_STATEMENTS")
        rows.append(row)
    faithful = [row for row in rows if row["paired_statement_eligible"]]
    proved = [row for row in rows if row["paired_proof_eligible"]]

    def totals(items: list[dict], field: str) -> dict:
        n = sum(item["N"][field] for item in items)
        l = sum(item["L"][field] for item in items)
        return {"N_sum": n, "L_sum": l, "L_over_N": l / n if n else None}

    summary = {
        "scheduled_tasks": 10,
        "provenance_pair_counts": {"Pilot 29": 5, "Pilot 31": 4, "Pilot 32": 1},
        "faithful_statement_pairs": len(faithful),
        "paired_complete_proofs": len(proved),
        "proof_attrition_pairs": 10 - len(proved),
        "L_direct_statement_reach_tasks": sum(
            bool(row["direct_numstability_names_in_statement"]) for row in rows),
        "L_shorter_statement_code_tasks": sum(
            row["L"]["statement_code_lines"] < row["N"]["statement_code_lines"]
            for row in faithful),
        "L_shorter_proof_code_tasks": sum(
            row["L"]["proof_code_lines"] < row["N"]["proof_code_lines"]
            for row in proved),
        "L_faster_end_to_end_proved_tasks": sum(
            row["L"]["contestant_system_wall_seconds"]
            < row["N"]["contestant_system_wall_seconds"] for row in proved),
        "statement_code_lines_faithful": totals(faithful, "statement_code_lines"),
        "proof_code_lines_proved": totals(proved, "proof_code_lines"),
        "inclusive_seconds_proved": totals(
            proved, "contestant_system_wall_seconds"),
        "net_new_tokens_proved": totals(proved, "net_new_tokens"),
        "task_retrieval_seconds_proved": totals(
            proved, "task_retrieval_seconds"),
        "peak_cpu_cores_sampled": max(
            (condition["peak_cpu_cores_sampled"]
             for row in rows for condition in (row["N"], row["L"])
             if condition is not None), default=0.0),
        "peak_ram_gib_sampled": max(
            (condition["peak_ram_gib_sampled"]
             for row in rows for condition in (row["N"], row["L"])
             if condition is not None), default=0.0),
    }
    return {
        "schema_version": "pilot-32-three-campaign-ten-task-report-1",
        "scientific_status": "OUTCOME_AWARE_INTERRUPTION_RECOVERY_NOT_CONFIRMATORY",
        "interpretation": (
            "Three distinct frozen campaigns, combined descriptively. "
            "Only both-faithful, both-proved pairs enter proof-size comparisons. "
            "The direct NumStability list is elaborated statement reach, not a "
            "separate proof-body dependency audit. Sampled hardware peaks may "
            "miss brief spikes."),
        "summary": summary,
        "tasks": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("pilot29-root", "pilot31-root", "pilot32-root",
                 "recovery-manifest", "admission"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(report(
        args.pilot29_root, args.pilot31_root, args.pilot32_root,
        args.recovery_manifest, args.admission), sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, KeyError) as error:
        print(f"Pilot 32 report error: {error}", file=sys.stderr)
        raise SystemExit(2)
