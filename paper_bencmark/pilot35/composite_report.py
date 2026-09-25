#!/usr/bin/env python3
"""Hash-checked 15-task phase report across Pilot 34 and incident recovery 35."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

TOOLS = Path(__file__).resolve().parents[1] / "formalization_benchmark" / "tools"
sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, canonical_json_bytes, load_json, sha256_file
from design33_admission import SCHEMA as ADMISSION_SCHEMA, verify_admission
from design33_report import (_checked_attempts, _phase, _totals,
                             NON_SUBSTANTIVE, PROOF_SCAN)
from deployment import load_deployment


def report(root34: Path, root35: Path, manifest_path: Path,
           admission_path: Path, corpus_path: Path, deployment_path: Path,
           scratch_root: Path) -> dict:
    manifest = load_json(manifest_path)
    if manifest.get("schema_version") != "pilot-35-recovery-manifest-1":
        raise BenchmarkError("wrong recovery manifest")
    if root34.resolve() != Path(manifest["source_campaign_root"]).resolve():
        raise BenchmarkError("source root differs from manifest")
    path34, path35 = root34 / "campaign.json", root35 / "campaign.json"
    if sha256_file(path34) != manifest["source_campaign_sha256"]:
        raise BenchmarkError("Pilot 34 journal changed")
    j34, j35 = load_json(path34), load_json(path35)
    if (j34.get("status") != "PAUSED_CONCURRENT_INCIDENT"
            or j35.get("schema_version")
            != "pilot-35-audit-incident-recovery-campaign-1"
            or j35.get("status") != "COMPLETE_RECOVERY"
            or j35.get("inputs", {}).get("recovery_manifest_sha256")
            != sha256_file(manifest_path)
            or j35.get("inputs", {}).get("source_campaign_sha256")
            != manifest["source_campaign_sha256"]
            or j34.get("inputs_sha256") != manifest["source_inputs_sha256"]):
        raise BenchmarkError("campaign provenance or completion failed")
    for journal in (j34, j35):
        if hashlib.sha256(canonical_json_bytes(journal["inputs"])).hexdigest() != journal["inputs_sha256"]:
            raise BenchmarkError("campaign input identity changed")
    if (j34["inputs"]["schedule"] != j35["inputs"]["schedule"]
            or sha256_file(admission_path) != j34["inputs"]["admission_sha256"]
            or sha256_file(corpus_path) != j34["inputs"]["corpus_sha256"]
            or sha256_file(deployment_path) != j34["inputs"]["deployment_sha256"]
            or j35["inputs"]["admission_sha256"] != j34["inputs"]["admission_sha256"]
            or j35["inputs"]["corpus_sha256"] != j34["inputs"]["corpus_sha256"]):
        raise BenchmarkError("frozen task/deployment inputs changed")
    controller_root = Path(__file__).resolve().parents[2]
    actual_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=controller_root, text=True,
    ).strip()
    if actual_commit != j35["inputs"]["controller_commit"]:
        raise BenchmarkError("Pilot 35 reporter checkout differs from controller")
    schedule = j34["inputs"]["schedule"]
    preserved = manifest["preserved_pair_report_sha256"]
    incident = manifest["incident_pair_report_sha256"]
    recovery = manifest["recovery_task_order"]
    if (len(schedule) != 15 or recovery != [task for task in schedule if task not in preserved]
            or set(incident) != {"CAST08-PROP3.1"}
            or len(j34["pairs"]) != len(preserved) + 1
            or len(j35["pairs"]) != len(recovery)
            or {item["task_id"] for item in j35["pairs"]} != set(recovery)):
        raise BenchmarkError("15-task recovery partition changed")
    prior_entries = {item["task_id"]: item for item in j34["pairs"]}
    recovery_entries = {item["task_id"]: item for item in j35["pairs"]}
    for task, digest in {**preserved, **incident}.items():
        path = root34 / task / "pair-report.json"
        if (sha256_file(path) != digest
                or prior_entries[task]["pair_report_sha256"] != digest):
            raise BenchmarkError(f"Pilot 34 pair changed: {task}")
    if load_json(root34 / "CAST08-PROP3.1" / "pair-report.json").get("status") != "PAIR_INCIDENT":
        raise BenchmarkError("original audit incident was lost")
    admission, corpus = load_json(admission_path), load_json(corpus_path)
    if (admission.get("schema_version") != ADMISSION_SCHEMA
            or corpus["scheduled_order"] != schedule
            or set(admission["tasks"]) != set(schedule)):
        raise BenchmarkError("admission schedule changed")
    task_root = Path(j34["inputs"]["task_root"])
    deployment = load_deployment(deployment_path)
    rows = []
    for task in schedule:
        root, entry, provenance = (
            (root34, prior_entries[task], "Pilot 34") if task in preserved
            else (root35, recovery_entries[task], "Pilot 35")
        )
        pair_path = root / task / "pair-report.json"
        if sha256_file(pair_path) != entry["pair_report_sha256"]:
            raise BenchmarkError(f"selected pair changed: {task}")
        pair = load_json(pair_path)
        if (pair.get("task_id") != task
                or entry["scheduled_index"] != schedule.index(task)):
            raise BenchmarkError(f"task index or identity changed: {task}")
        packet_path = task_root / "packets" / f"{task}.json"
        packet = load_json(packet_path)
        source = task_root / "sources" / packet["paper_pdf"]["path_basename"]
        if not source.is_file():
            source = deployment.pdf_root / packet["paper_pdf"]["path_basename"]
        verify_admission(task, packet_path=packet_path, paper=source,
                         admission_path=admission_path, corpus_path=corpus_path)
        conditions = pair.get("conditions", {})
        for key in ("R0", "R1"):
            if key in conditions:
                _checked_attempts(root / task / key, conditions[key])
        n = (_phase(conditions["R0"], deployment_path, scratch_root,
                    scan_proof=False) if "R0" in conditions else None)
        l = (_phase(conditions["R1"], deployment_path, scratch_root,
                    scan_proof=True) if "R1" in conditions else None)
        names = entry.get("treatment_uptake", {}).get("direct_reached", [])
        row = {
            "task_id": task, "source_pilot": provenance,
            "source_cluster": admission["tasks"][task]["source_cluster"],
            "difficulty_predeclared": admission["tasks"][task]["difficulty"],
            "outcome_aware_retained": admission["tasks"][task]["evidence_kind"]
                == "outcome_aware_pilot29",
            "pair_status": pair.get("status"),
            "proof_pair_status": pair.get("proof_pair_status"),
            "direct_statement_numstability_names": names,
            "substantive_statement_numstability_names": sorted(
                set(names) - NON_SUBSTANTIVE),
            "N": n, "L": l,
        }
        row["paired_statement_eligible"] = (
            row["pair_status"] == "AUDITED_FAITHFUL_PAIR"
            and n is not None and l is not None)
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
        "schema_version": "pilot-35-two-campaign-15-task-report-1",
        "scientific_status": "OUTCOME_AWARE_EXPLORATORY_INCIDENT_RECOVERY_NOT_CONFIRMATORY",
        "pilot34_campaign_sha256": sha256_file(path34),
        "pilot35_campaign_sha256": sha256_file(path35),
        "recovery_manifest_sha256": sha256_file(manifest_path),
        "proof_dependency_scanner_sha256": sha256_file(PROOF_SCAN),
        "interpretation": (
            "Five previously favorable tasks were deliberately retained. "
            "Eight P14 tasks are clustered and not independent replications. "
            "One Pilot 34 pair had an audit-schema incident; its partial evidence "
            "is preserved, and only its fresh Pilot 35 pair enters comparisons. "
            "All other Pilot 34 pairs were retained without rerun. Proof-size "
            "comparisons include only both-faithful, both-proved pairs. "
            "Proof-term use is elaborated, not source text matching. "
            "Hardware peaks are sampled and may miss brief spikes."
        ),
        "incidents": [{
            "task_id": "CAST08-PROP3.1", "source_pilot": "Pilot 34",
            "pair_report_sha256": incident["CAST08-PROP3.1"],
            "reason": "round-trip judge's correct nonvacuity rejection was rejected by the audit implication/classification validator",
        }],
        "summary": {
            "scheduled_tasks": len(rows),
            "provenance_pair_counts": {
                "Pilot 34": len(preserved), "Pilot 35": len(recovery),
            },
            "faithful_statement_pairs": len(faithful),
            "both_proved_pairs": len(proved),
            "proof_attrition_pairs": len(rows) - len(proved),
            "outcome_aware_retained_tasks": sum(row["outcome_aware_retained"] for row in rows),
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
                row["L"]["statement_code_lines"] < row["N"]["statement_code_lines"]
                for row in faithful),
            "L_shorter_proof_code_tasks": sum(
                row["L"]["proof_code_lines"] < row["N"]["proof_code_lines"]
                for row in proved),
            "L_faster_total_proved_tasks": sum(
                row["L"]["total_seconds_inclusive"] < row["N"]["total_seconds_inclusive"]
                for row in proved),
            "phase_comparisons": {field: _totals(group, field)
                                  for field, group in phase_fields},
            "peak_cpu_cores_sampled": max(
                (condition["peak_cpu_cores_sampled"] for row in rows
                 for condition in (row["N"], row["L"]) if condition), default=0.0),
            "peak_ram_gib_sampled": max(
                (condition["peak_ram_gib_sampled"] for row in rows
                 for condition in (row["N"], row["L"]) if condition), default=0.0),
        },
        "tasks": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("pilot34-root", "pilot35-root", "recovery-manifest",
                 "admission", "corpus", "deployment", "scratch-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(report(args.pilot34_root, args.pilot35_root,
                            args.recovery_manifest, args.admission, args.corpus,
                            args.deployment, args.scratch_root),
                     sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, KeyError) as error:
        raise SystemExit(f"Pilot 35 composite report error: {error}")
