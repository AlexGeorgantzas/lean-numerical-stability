#!/usr/bin/env python3
"""Build, then verify, the prospective ten-task proof admission record.

Run only after the new CAST08-PROP3.1 source review and private full audit have
sealed. This reads previous immutable evidence; it never supplies old Lean
sources or audit feedback to a contestant.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from common import BenchmarkError, load_json, sha256_file, write_json_atomic
from design29_admission import SCHEMA, verify_admission


ROOT = Path(__file__).resolve().parents[1]
PRIOR = ROOT / "design20" / "ADMISSION_12.json"
CAMPAIGN = Path(
    "/hdd/alexgeorgantzas/highambench/pilot26-development-12-20260923-a"
)
TASK_ROOT = ROOT / "design20"
REQUIRED = {
    "FAB19-EQ3.5": ("algorithm_error", ["NumStability.fl_recursiveSum"]),
    "FAB19-EQ3.6": ("algorithm_error", ["NumStability.fl_kahanSum"]),
    "CAST08-FIXED3": ("algorithm_error", ["NumStability.fl_dotProduct"]),
    "CAST08-PROP3.2": ("algorithm_error", ["NumStability.fl_dotProduct"]),
    "RUMP12-THM3.4": ("finite_format", ["NumStability.FloatingPointFormat"]),
    "RUMP12-THM3.5": ("finite_format", ["NumStability.FloatingPointFormat"]),
    "LL07-THM4": ("finite_format", ["NumStability.polyDesc"]),
    "LL07-THM7": ("finite_format", ["NumStability.polyDesc"]),
    "H20-8": ("error_interface", [
        "NumStability.lsNormwiseBackwardErrorMatrixOnlyEtaF"
    ]),
    "CAST08-PROP3.1": ("algorithm_error", ["NumStability.fl_recursiveSum"]),
}


def build(*, corpus_path: Path, cast_source_review: Path,
          cast_audit_result: Path, cast_candidate: Path,
          cast32_audit_result: Path, cast32_candidate: Path,
          pdf_root: Path) -> dict:
    corpus = load_json(corpus_path)
    schedule = corpus.get("scheduled_order", [])
    if len(schedule) != 10 or set(schedule) != set(REQUIRED):
        raise BenchmarkError("Pilot 29 draft must contain the exact ten screened tasks")
    prior = load_json(PRIOR)
    campaign_path = CAMPAIGN / "campaign.json"
    campaign = load_json(campaign_path)
    if campaign.get("status") != "COMPLETE":
        raise BenchmarkError("prior Pilot 26 campaign is not complete")
    tasks = {}
    for task_id in schedule:
        packet_path = TASK_ROOT / "packets" / f"{task_id}.json"
        packet = load_json(packet_path)
        if packet.get("task_id") != task_id:
            raise BenchmarkError(f"packet task ID changed: {task_id}")
        paper = TASK_ROOT / "sources" / packet["paper_pdf"]["path_basename"]
        if not paper.is_file():
            paper = pdf_root / packet["paper_pdf"]["path_basename"]
        if not paper.is_file():
            raise BenchmarkError(f"task source PDF missing: {task_id}")
        if sha256_file(paper) != packet["paper_pdf"]["sha256"]:
            raise BenchmarkError(f"task source PDF changed: {task_id}")
        stratum, required = REQUIRED[task_id]
        task = {
            "status": "ADMITTED_DEVELOPMENT",
            "model_stratum": stratum,
            "source_packet_sha256": sha256_file(packet_path),
            "source_pdf_sha256": sha256_file(paper),
            "target_collision_review": "NO_TARGET_RESULT_FOUND",
            "required_direct_names": required,
        }
        if task_id == "CAST08-PROP3.1":
            task.update({
                "collision_review_note": (
                    "The snapshot has recursive-sum and generic tree bounds, "
                    "but the inspected summation declarations do not contain "
                    "Proposition 3.1's t-level algorithm plus optimality result."
                ),
                "source_review_path": str(cast_source_review.resolve()),
                "source_review_sha256": sha256_file(cast_source_review),
                "evidence_kind": "new_private_audit",
                "private_candidate_path": str(cast_candidate.resolve()),
                "private_candidate_sha256": sha256_file(cast_candidate),
                "private_audit_result_path": str(cast_audit_result.resolve()),
                "private_audit_result_sha256": sha256_file(cast_audit_result),
            })
        elif task_id == "CAST08-PROP3.2":
            previous = prior.get("tasks", {}).get(task_id)
            if not isinstance(previous, dict):
                raise BenchmarkError(f"prior source admission lacks {task_id}")
            task.update({
                "collision_review_note": previous["target_collision_review_note"],
                "source_review_path": previous["source_review_path"],
                "source_review_sha256": previous["source_review_sha256"],
                "evidence_kind": "new_private_audit",
                "private_candidate_path": str(cast32_candidate.resolve()),
                "private_candidate_sha256": sha256_file(cast32_candidate),
                "private_audit_result_path": str(cast32_audit_result.resolve()),
                "private_audit_result_sha256": sha256_file(cast32_audit_result),
            })
        else:
            previous = prior.get("tasks", {}).get(task_id)
            if not isinstance(previous, dict):
                raise BenchmarkError(f"prior admission lacks {task_id}")
            entries = [entry for entry in campaign["pairs"]
                       if entry.get("task_id") == task_id]
            if len(entries) != 1:
                raise BenchmarkError(f"prior campaign lacks {task_id}")
            pair_path = CAMPAIGN / task_id / "pair-report.json"
            pair = load_json(pair_path)
            task.update({
                "collision_review_note": previous["target_collision_review_note"],
                "source_review_path": previous["source_review_path"],
                "source_review_sha256": previous["source_review_sha256"],
                "evidence_kind": "prior_faithful_pair",
                "prior_pair_report_sha256": sha256_file(pair_path),
                "prior_faithful_l_candidate_sha256":
                    pair["conditions"]["R1"]["candidate_sha256"],
            })
        tasks[task_id] = task
    return {
        "schema_version": SCHEMA,
        "status": "ADMITTED_DEVELOPMENT",
        "scope": (
            "Ten outcome-aware exploratory tasks; six direct algorithm/"
            "error-interface candidates and four foundational/finite-format "
            "cases. Not confirmatory; actual uptake and proof attrition remain outcomes."
        ),
        "prior_admission_path": str(PRIOR.relative_to(ROOT.parents[1])),
        "prior_admission_sha256": sha256_file(PRIOR),
        "prior_campaign_path": str(CAMPAIGN),
        "prior_campaign_sha256": sha256_file(campaign_path),
        "tasks": tasks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=Path)
    parser.add_argument("--cast-source-review", required=True, type=Path)
    parser.add_argument("--cast-audit-result", required=True, type=Path)
    parser.add_argument("--cast-candidate", required=True, type=Path)
    parser.add_argument("--cast32-audit-result", required=True, type=Path)
    parser.add_argument("--cast32-candidate", required=True, type=Path)
    parser.add_argument("--pdf-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists() or args.output.is_symlink():
        raise BenchmarkError("admission output already exists")
    record = build(
        corpus_path=args.corpus,
        cast_source_review=args.cast_source_review,
        cast_audit_result=args.cast_audit_result,
        cast_candidate=args.cast_candidate,
        cast32_audit_result=args.cast32_audit_result,
        cast32_candidate=args.cast32_candidate,
        pdf_root=args.pdf_root,
    )
    write_json_atomic(args.output, record, mode=0o400)
    for task_id in load_json(args.corpus)["scheduled_order"]:
        packet = TASK_ROOT / "packets" / f"{task_id}.json"
        paper = TASK_ROOT / "sources" / load_json(packet)["paper_pdf"]["path_basename"]
        if not paper.is_file():
            paper = args.pdf_root / load_json(packet)["paper_pdf"]["path_basename"]
        verify_admission(
            task_id, packet_path=packet, paper=paper,
            admission_path=args.output, corpus_path=args.corpus,
        )
    print(f"ADMITTED_DEVELOPMENT: {len(record['tasks'])} tasks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
