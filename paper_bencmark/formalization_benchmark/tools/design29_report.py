#!/usr/bin/env python3
"""Read-only, hash-checked descriptive report for a proof-required campaign.

The reporter is predeclared before Pilot 29 measurements. It never changes a
campaign or silently excludes a task. Ratios are computed only for pairs in
which both source-faithful statements were independently proved.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

from common import BenchmarkError, canonical_json_bytes, load_json, sha256_file
from design29_admission import SCHEMA as ADMISSION_SCHEMA


def _code_lines(path: Path) -> int:
    """Count nonblank physical lines with Lean tokens (nested comments aware)."""
    source = path.read_text()
    depth = 0
    quoted = False
    escaped = False
    count = 0
    for line in source.splitlines():
        i = 0
        has_code = False
        while i < len(line):
            pair = line[i:i + 2]
            if depth:
                if pair == "/-":
                    depth += 1
                    i += 2
                elif pair == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            if quoted:
                has_code = True
                if escaped:
                    escaped = False
                elif line[i] == "\\":
                    escaped = True
                elif line[i] == '"':
                    quoted = False
                i += 1
                continue
            if pair == "--":
                break
            if pair == "/-":
                depth += 1
                i += 2
                continue
            if line[i] == '"':
                quoted = True
                has_code = True
            elif not line[i].isspace():
                has_code = True
            i += 1
        count += has_code
    if depth or quoted:
        raise BenchmarkError(f"unterminated Lean comment/string in {path}")
    return count


def _checked_candidate(candidate: dict) -> Path:
    path = Path(candidate["path"])
    if not path.is_absolute() or not path.is_file() or path.is_symlink():
        raise BenchmarkError("candidate path is missing or unsafe")
    if sha256_file(path) != candidate["sha256"]:
        raise BenchmarkError(f"candidate hash mismatch: {path}")
    if len(path.read_text().splitlines()) != candidate["lines"]:
        raise BenchmarkError(f"candidate line count mismatch: {path}")
    return path


def _condition(record: dict) -> dict:
    candidate = record.get("candidate")
    if isinstance(candidate, dict):
        _checked_candidate(candidate)
    proof = record.get("proof_stage", {})
    result = {
        "statement_status": record.get("result_status"),
        "statement_lines": record.get("candidate_lines"),
        "proof_status": proof.get("status"),
        "proof_raw_lines": None,
        "proof_code_lines": None,
        "contestant_system_wall_seconds": record.get(
            "end_to_end_contestant_system_wall_seconds"),
        "net_new_tokens": record.get("end_to_end_net_new_tokens"),
        "task_retrieval_seconds": record.get("retrieval_wall_seconds"),
        "peak_cpu_cores_sampled": 0.0,
        "peak_ram_gib_sampled": 0.0,
    }
    for attempt in record.get("attempts", []):
        resource = attempt.get("formalization_resources", {})
        result["peak_cpu_cores_sampled"] = max(
            result["peak_cpu_cores_sampled"],
            float(resource.get("peak_cpu_cores_sampled") or 0),
        )
        result["peak_ram_gib_sampled"] = max(
            result["peak_ram_gib_sampled"],
            float(resource.get("peak_memory_current_bytes_sampled") or 0) / 2**30,
        )
    for attempt in proof.get("attempts", []):
        resource = attempt.get("proof_resources", {})
        result["peak_cpu_cores_sampled"] = max(
            result["peak_cpu_cores_sampled"],
            float(resource.get("peak_cpu_cores_sampled") or 0),
        )
        result["peak_ram_gib_sampled"] = max(
            result["peak_ram_gib_sampled"],
            float(resource.get("peak_memory_current_bytes_sampled") or 0) / 2**30,
        )
    if proof.get("status") == "PROVED_FROZEN_STATEMENT":
        if not proof.get("attempts"):
            raise BenchmarkError("proved status without a proof candidate")
        final = proof["attempts"][-1]["candidate"]
        path = _checked_candidate(final)
        result["proof_raw_lines"] = final["lines"]
        result["proof_code_lines"] = _code_lines(path)
    return result


def report(campaign_root: Path, admission_path: Path) -> dict:
    campaign = load_json(campaign_root / "campaign.json")
    if (campaign.get("schema_version") != "pilot-27-proof-required-campaign-1"
            or campaign.get("status") != "COMPLETE"):
        raise BenchmarkError("proof campaign has not completed")
    inputs = campaign["inputs"]
    if hashlib.sha256(canonical_json_bytes(inputs)).hexdigest() != campaign["inputs_sha256"]:
        raise BenchmarkError("campaign input identity changed")
    if sha256_file(admission_path) != inputs["admission_sha256"]:
        raise BenchmarkError("admission changed")
    admission = load_json(admission_path)
    if admission.get("schema_version") != ADMISSION_SCHEMA:
        raise BenchmarkError("wrong admission schema")
    schedule = inputs["schedule"]
    entries = campaign["pairs"]
    if (len(schedule) != len(entries)
            or set(schedule) != {x["task_id"] for x in entries}
            or set(schedule) != set(admission["tasks"])):
        raise BenchmarkError("campaign schedule is incomplete or duplicated")
    by_task = {x["task_id"]: x for x in entries}
    rows = []
    for task_id in schedule:
        entry = by_task[task_id]
        pair_path = campaign_root / task_id / "pair-report.json"
        if sha256_file(pair_path) != entry["pair_report_sha256"]:
            raise BenchmarkError(f"pair report changed for {task_id}")
        pair = load_json(pair_path)
        if pair.get("task_id") != task_id:
            raise BenchmarkError(f"pair identity changed for {task_id}")
        conditions = pair.get("conditions", {})
        row = {
            "task_id": task_id,
            "stratum": admission["tasks"][task_id]["model_stratum"],
            "pair_status": entry["pair_status"],
            "proof_pair_status": entry.get("proof_pair_status"),
            "direct_numstability_names": entry.get("treatment_uptake", {}).get(
                "direct_reached", []),
            "N": _condition(conditions["R0"]) if "R0" in conditions else None,
            "L": _condition(conditions["R1"]) if "R1" in conditions else None,
        }
        row["paired_proof_eligible"] = (
            row["pair_status"] == "AUDITED_FAITHFUL_PAIR"
            and row["proof_pair_status"] == "BOTH_PROVED_FROZEN_STATEMENTS"
            and row["N"] is not None and row["L"] is not None
        )
        rows.append(row)
    eligible = [row for row in rows if row["paired_proof_eligible"]]
    summary = {
        "scheduled_tasks": len(rows),
        "faithful_statement_pairs": sum(row["pair_status"] == "AUDITED_FAITHFUL_PAIR"
                                         for row in rows),
        "paired_complete_proofs": len(eligible),
        "L_direct_reach_tasks": sum(bool(row["direct_numstability_names"])
                                    for row in rows),
        "L_shorter_raw_proof_tasks": sum(
            row["L"]["proof_raw_lines"] < row["N"]["proof_raw_lines"]
            for row in eligible),
        "L_shorter_code_proof_tasks": sum(
            row["L"]["proof_code_lines"] < row["N"]["proof_code_lines"]
            for row in eligible),
    }
    for field in ("proof_raw_lines", "proof_code_lines",
                  "contestant_system_wall_seconds", "net_new_tokens",
                  "task_retrieval_seconds"):
        n = sum(row["N"][field] for row in eligible)
        l = sum(row["L"][field] for row in eligible)
        summary[field] = {"N_sum": n, "L_sum": l,
                          "L_over_N_sum": l / n if n else None}
    for field in ("proof_raw_lines", "proof_code_lines",
                  "contestant_system_wall_seconds", "net_new_tokens"):
        ratios = [row["L"][field] / row["N"][field] for row in eligible
                  if row["N"][field] > 0 and row["L"][field] > 0]
        summary[field]["geometric_mean_L_over_N"] = (
            math.exp(sum(map(math.log, ratios)) / len(ratios)) if ratios else None
        )
    return {
        "schema_version": "pilot-29-proof-descriptive-report-1",
        "scientific_status": "OUTCOME_AWARE_EXPLORATORY_NOT_CONFIRMATORY",
        "campaign_sha256": sha256_file(campaign_root / "campaign.json"),
        "admission_sha256": sha256_file(admission_path),
        "summary": summary,
        "tasks": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-root", required=True, type=Path)
    parser.add_argument("--admission", required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(report(args.campaign_root, args.admission), indent=2,
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
