#!/usr/bin/env python3
"""Predeclared, hash-checked phase report for the Pilot 33 development corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from common import BenchmarkError, canonical_json_bytes, load_json, sha256_file
from design29_report import _checked_candidate, _condition
from design33_admission import SCHEMA as ADMISSION_SCHEMA, verify_admission
from deployment import load_deployment


PROOF_SCAN = Path(__file__).with_name("design33_proof_dependencies.lean")
NON_SUBSTANTIVE = {
    "NumStability.FPModel", "NumStability.gamma", "NumStability.gammaValid",
    "NumStability.FloatingPointFormat",
}


def _checked_attempts(root: Path, record: dict) -> None:
    if load_json(root / "report.json") != record:
        raise BenchmarkError(f"condition report differs from pair: {root}")
    for attempt in record.get("attempts", []):
        _checked_candidate(attempt["candidate"])
        path = root / "submissions" / f"{attempt['attempt']:02d}" / "validation.json"
        if sha256_file(path) != attempt["validation_sha256"]:
            raise BenchmarkError(f"statement validation changed: {path}")
        audit = attempt.get("audit", {})
        decision_sha = audit.get("decision_sha256")
        if decision_sha is not None:
            decision_path = root / "audits" / attempt["semantic_sha256"] / "decision.json"
            if sha256_file(decision_path) != decision_sha:
                raise BenchmarkError(f"statement audit changed: {decision_path}")
    if load_json(root / "proof-stage.json") != record.get("proof_stage"):
        raise BenchmarkError(f"proof-stage record differs from condition: {root}")
    for attempt in record.get("proof_stage", {}).get("attempts", []):
        _checked_candidate(attempt["candidate"])
        digest = attempt.get("validation_sha256")
        if digest is not None:
            path = root / "proof-submissions" / f"{attempt['attempt']:02d}" / "validation.json"
            if sha256_file(path) != digest:
                raise BenchmarkError(f"proof validation changed: {path}")
    if record.get("proof_stage", {}).get("status") == "PROVED_FROZEN_STATEMENT":
        final = record["proof_stage"]["attempts"][-1]
        path = root / "proof-submissions" / f"{final['attempt']:02d}" / "validation.json"
        if load_json(path).get("pass") is not True:
            raise BenchmarkError("proved proof has no passing zero-hole validation")


def _proof_library_names(candidate: dict, deployment_path: Path,
                         scratch_root: Path) -> list[str]:
    """Read the accepted proof term through Lean, never source-name matching."""
    path = _checked_candidate(candidate)
    deployment = load_deployment(deployment_path)
    common_project = deployment.packages_root.parents[1]
    lean = deployment.toolchain_root / "bin" / "lean"
    lake = deployment.toolchain_root / "bin" / "lake"
    probe = subprocess.run(
        [str(lake), "env", "printenv", "LEAN_PATH"], cwd=common_project,
        capture_output=True, text=True, timeout=60, check=False,
    )
    if probe.returncode != 0 or not probe.stdout.strip():
        raise BenchmarkError("cannot obtain pinned Mathlib LEAN_PATH")
    base_path = f"{deployment.library_olean}:{probe.stdout.strip()}"
    if not scratch_root.is_absolute() or not scratch_root.is_dir():
        raise BenchmarkError("proof dependency scratch root must preexist")
    with tempfile.TemporaryDirectory(prefix="pilot33-proof-scan-",
                                     dir=scratch_root) as temp_name:
        temp = Path(temp_name)
        copied = temp / "Candidate.lean"
        shutil.copyfile(path, copied)
        if sha256_file(copied) != candidate["sha256"]:
            raise BenchmarkError("proof scan copy hash changed")
        env = dict(os.environ)
        env["LEAN_PATH"] = base_path
        env["PATH"] = f"{deployment.toolchain_root / 'bin'}:{env.get('PATH', '')}"
        compiled = subprocess.run(
            [str(lean), "-o", "Candidate.olean", "Candidate.lean"], cwd=temp,
            env=env, capture_output=True, text=True, timeout=600, check=False,
        )
        if compiled.returncode != 0:
            raise BenchmarkError("accepted proof failed reporter recompilation: "
                                 + compiled.stderr[-2000:] + compiled.stdout[-2000:])
        env["LEAN_PATH"] = f"{temp}:{base_path}"
        scan = subprocess.run(
            [str(lean), "--run", str(PROOF_SCAN), "Candidate",
             "HighamBenchCandidate.target"],
            cwd=temp, env=env, capture_output=True, text=True, timeout=600,
            check=False,
        )
        if scan.returncode != 0:
            raise BenchmarkError("proof dependency scan failed: "
                                 + scan.stderr[-2000:] + scan.stdout[-2000:])
        names = []
        for line in scan.stdout.splitlines():
            if line.startswith("proof-library\t"):
                names.append(line.split("\t", 1)[1])
        if not any(line.startswith("summary\t") for line in scan.stdout.splitlines()):
            raise BenchmarkError("proof dependency scan omitted summary")
        return sorted(set(names))


def _phase(record: dict, deployment_path: Path, scratch_root: Path,
           *, scan_proof: bool) -> dict:
    base = _condition(record)
    proof = record.get("proof_stage", {})
    proof_started = proof.get("status") != "NOT_STARTED_STATEMENT_NOT_FAITHFUL"
    formal_seconds = record.get("contestant_system_wall_seconds")
    proof_seconds = proof.get("contestant_active_seconds") if proof_started else None
    formal_tokens = record.get("net_new_tokens")
    proof_tokens = proof.get("net_new_tokens") if proof_started else None
    if formal_seconds is None or formal_tokens is None:
        raise BenchmarkError("condition lacks formalization clock or usage")
    if proof_started and (proof_seconds is None or proof_tokens is None):
        raise BenchmarkError("started proof stage lacks clock or usage")
    summed_seconds = formal_seconds + (proof_seconds or 0)
    summed_tokens = formal_tokens + (proof_tokens or 0)
    if (abs(summed_seconds - record["end_to_end_contestant_system_wall_seconds"]) > 1e-5
            or summed_tokens != record["end_to_end_net_new_tokens"]):
        raise BenchmarkError("phase clocks/tokens do not reconcile")
    names: list[str] | None = None
    if scan_proof and proof.get("status") == "PROVED_FROZEN_STATEMENT":
        names = _proof_library_names(
            proof["attempts"][-1]["candidate"], deployment_path, scratch_root,
        )
    return {
        **base,
        "formalization_seconds_inclusive": formal_seconds,
        "formalization_tokens_net_new": formal_tokens,
        "formalization_usage": record.get("usage"),
        "formalization_submissions": record.get("submission_count"),
        "proof_seconds_inclusive": proof_seconds,
        "proof_tokens_net_new": proof_tokens,
        "proof_usage": proof.get("usage") if proof_started else None,
        "proof_submissions": proof.get("submission_count") if proof_started else None,
        "total_seconds_inclusive": summed_seconds,
        "total_tokens_net_new": summed_tokens,
        "audit_seconds_excluded": record.get("audit_seconds_excluded_from_contestant"),
        "audit_usage_excluded": record.get("audit_usage_excluded"),
        "statement_validation_seconds_excluded":
            record.get("validation_seconds_excluded_from_contestant"),
        "semantic_dossier_seconds_excluded":
            record.get("dossier_seconds_excluded_from_contestant"),
        "proof_validation_seconds_excluded": proof.get("validation_seconds_excluded"),
        "proof_dossier_seconds_excluded": proof.get("dossier_seconds_excluded"),
        "proof_term_numstability_names": names,
    }


def _totals(rows: list[dict], field: str) -> dict:
    n = sum(row["N"][field] for row in rows)
    l = sum(row["L"][field] for row in rows)
    ratios = [row["L"][field] / row["N"][field] for row in rows
              if row["N"][field] > 0 and row["L"][field] > 0]
    return {
        "N_sum": n, "L_sum": l, "L_over_N_sum": l / n if n else None,
        "geometric_mean_L_over_N":
            math.exp(sum(math.log(value) for value in ratios) / len(ratios))
            if ratios else None,
        "denominator_pairs": len(rows),
    }


def report(campaign_root: Path, admission_path: Path, corpus_path: Path,
           deployment_path: Path, scratch_root: Path) -> dict:
    campaign_path = campaign_root / "campaign.json"
    campaign = load_json(campaign_path)
    if (campaign.get("schema_version") != "pilot-27-proof-required-campaign-1"
            or campaign.get("status") != "COMPLETE"):
        raise BenchmarkError("Pilot 33 campaign is not complete")
    inputs = campaign["inputs"]
    controller_root = Path(__file__).resolve().parents[3]
    controller_commit = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"], cwd=controller_root,
        capture_output=True, text=True, timeout=30, check=False,
    )
    if (controller_commit.returncode != 0
            or controller_commit.stdout.strip() != inputs.get("controller_commit")):
        raise BenchmarkError("reporter checkout differs from frozen controller")
    if (hashlib.sha256(canonical_json_bytes(inputs)).hexdigest()
            != campaign.get("inputs_sha256")
            or sha256_file(admission_path) != inputs["admission_sha256"]
            or sha256_file(corpus_path) != inputs["corpus_sha256"]
            or sha256_file(deployment_path) != inputs["deployment_sha256"]):
        raise BenchmarkError("frozen inputs changed")
    admission = load_json(admission_path)
    corpus = load_json(corpus_path)
    if admission.get("schema_version") != ADMISSION_SCHEMA:
        raise BenchmarkError("wrong Pilot 33 admission schema")
    schedule = inputs["schedule"]
    entries = campaign["pairs"]
    if (len(schedule) != len(entries)
            or set(schedule) != {entry["task_id"] for entry in entries}
            or set(schedule) != set(admission["tasks"])
            or schedule != corpus["scheduled_order"]):
        raise BenchmarkError("completed schedule is incomplete or duplicated")
    by_task = {entry["task_id"]: entry for entry in entries}
    rows = []
    task_root = Path(inputs["task_root"])
    deployment = load_deployment(deployment_path)
    for task_id in schedule:
        entry = by_task[task_id]
        pair_path = campaign_root / task_id / "pair-report.json"
        if sha256_file(pair_path) != entry["pair_report_sha256"]:
            raise BenchmarkError(f"pair report changed: {task_id}")
        pair = load_json(pair_path)
        packet_path = task_root / "packets" / f"{task_id}.json"
        packet = load_json(packet_path)
        source = task_root / "sources" / packet["paper_pdf"]["path_basename"]
        if not source.is_file():
            source = deployment.pdf_root / packet["paper_pdf"]["path_basename"]
        verify_admission(task_id, packet_path=packet_path, paper=source,
                         admission_path=admission_path, corpus_path=corpus_path)
        conditions = pair.get("conditions", {})
        for key in ("R0", "R1"):
            if key in conditions:
                _checked_attempts(campaign_root / task_id / key, conditions[key])
        n = (_phase(conditions["R0"], deployment_path, scratch_root,
                    scan_proof=False) if "R0" in conditions else None)
        l = (_phase(conditions["R1"], deployment_path, scratch_root,
                    scan_proof=True) if "R1" in conditions else None)
        statement_names = entry.get("treatment_uptake", {}).get("direct_reached", [])
        row = {
            "task_id": task_id,
            "source_cluster": admission["tasks"][task_id]["source_cluster"],
            "difficulty_predeclared": admission["tasks"][task_id]["difficulty"],
            "outcome_aware_retained": admission["tasks"][task_id]["evidence_kind"]
                == "outcome_aware_pilot29",
            "pair_status": pair.get("status"),
            "proof_pair_status": pair.get("proof_pair_status"),
            "direct_statement_numstability_names": statement_names,
            "substantive_statement_numstability_names": sorted(
                set(statement_names) - NON_SUBSTANTIVE),
            "N": n, "L": l,
        }
        row["paired_statement_eligible"] = (
            row["pair_status"] == "AUDITED_FAITHFUL_PAIR" and n is not None
            and l is not None)
        row["paired_proof_eligible"] = (
            row["paired_statement_eligible"]
            and row["proof_pair_status"] == "BOTH_PROVED_FROZEN_STATEMENTS")
        rows.append(row)
    faithful = [row for row in rows if row["paired_statement_eligible"]]
    proved = [row for row in rows if row["paired_proof_eligible"]]
    phase_fields = (
        ("formalization_seconds_inclusive", faithful),
        ("formalization_tokens_net_new", faithful),
        ("proof_seconds_inclusive", proved),
        ("proof_tokens_net_new", proved),
        ("total_seconds_inclusive", proved),
        ("total_tokens_net_new", proved),
        ("statement_code_lines", faithful),
        ("proof_code_lines", proved),
    )
    return {
        "schema_version": "pilot-33-phase-report-1",
        "scientific_status": "OUTCOME_AWARE_EXPLORATORY_NOT_CONFIRMATORY",
        "campaign_sha256": sha256_file(campaign_path),
        "admission_sha256": sha256_file(admission_path),
        "corpus_sha256": sha256_file(corpus_path),
        "proof_dependency_scanner_sha256": sha256_file(PROOF_SCAN),
        "interpretation": (
            "Previously favorable tasks were deliberately retained; new tasks were "
            "source-screened before this campaign. Same-paper tasks are clustered, "
            "not independent replications. Ratios use only the stated paired "
            "eligibility sets; all failures remain in the task table. Proof-term "
            "use is extracted from accepted Lean proof expressions, not text matching. "
            "Hardware peaks are sampled and may miss brief spikes."
        ),
        "summary": {
            "scheduled_tasks": len(rows),
            "faithful_statement_pairs": len(faithful),
            "both_proved_pairs": len(proved),
            "proof_attrition_pairs": len(rows) - len(proved),
            "outcome_aware_retained_tasks": sum(row["outcome_aware_retained"]
                                                for row in rows),
            "source_cluster_counts": {
                source: sum(row["source_cluster"] == source for row in rows)
                for source in sorted({row["source_cluster"] for row in rows})
            },
            "L_substantive_statement_use_tasks": sum(
                bool(row["substantive_statement_numstability_names"])
                for row in rows),
            "L_direct_proof_term_use_tasks": sum(
                bool(row["L"] and row["L"]["proof_term_numstability_names"])
                for row in rows),
            "L_shorter_statement_code_tasks": sum(
                row["L"]["statement_code_lines"]
                < row["N"]["statement_code_lines"] for row in faithful),
            "L_shorter_proof_code_tasks": sum(
                row["L"]["proof_code_lines"] < row["N"]["proof_code_lines"]
                for row in proved),
            "L_faster_total_proved_tasks": sum(
                row["L"]["total_seconds_inclusive"]
                < row["N"]["total_seconds_inclusive"] for row in proved),
            "phase_comparisons": {
                field: _totals(group, field) for field, group in phase_fields
            },
            "peak_cpu_cores_sampled": max(
                (condition["peak_cpu_cores_sampled"] for row in rows
                 for condition in (row["N"], row["L"]) if condition),
                default=0.0),
            "peak_ram_gib_sampled": max(
                (condition["peak_ram_gib_sampled"] for row in rows
                 for condition in (row["N"], row["L"]) if condition),
                default=0.0),
        },
        "tasks": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("campaign-root", "admission", "corpus", "deployment",
                 "scratch-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(report(args.campaign_root, args.admission, args.corpus,
                            args.deployment, args.scratch_root),
                     sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, KeyError) as error:
        raise SystemExit(f"Pilot 33 report error: {error}")
