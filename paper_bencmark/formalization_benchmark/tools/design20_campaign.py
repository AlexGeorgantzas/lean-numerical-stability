#!/usr/bin/env python3
"""Run Pilot-20 development pairs with a mandatory first-pair inspection gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from common import BenchmarkError, canonical_json_bytes, load_json, sha256_file, utc_now, write_json_atomic
from design18_campaign import _host_lock, _treatment_uptake
from design20_envelope import launch_or_activate
from design20_matched import CORPUS, ROOT, run as run_pair
from design20_admission import ADMISSION


SCHEMA = "pilot-21-development-campaign-1"
PILOT_ID = "pilot21-dev3-controller-nullfix"


def _inputs(args: argparse.Namespace) -> dict:
    corpus = load_json(CORPUS)
    controller_root = ROOT.parents[2]
    controller_commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=controller_root, text=True,
    ).strip()
    if subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=controller_root).returncode != 0:
        raise BenchmarkError("campaign controller has tracked uncommitted changes")
    return {
        "pilot_id": PILOT_ID,
        "controller_commit": controller_commit,
        "corpus_sha256": sha256_file(CORPUS),
        "admission_sha256": sha256_file(ADMISSION),
        "schedule": corpus["scheduled_order"],
        "packets": {task: sha256_file(ROOT / "packets" / f"{task}.json")
                    for task in corpus["scheduled_order"]},
        "sources": {task: load_json(ROOT / "packets" / f"{task}.json")["paper_pdf"]["sha256"]
                    for task in corpus["scheduled_order"]},
        "prompts": {name: sha256_file(ROOT / "prompts" / f"{name}.md")
                    for name in ("common", "library_appendix", "scout_compact")},
        "deployment_sha256": sha256_file(args.deployment),
        "mathlib_atlas_sha256": sha256_file(args.mathlib_atlas / "declarations.jsonl"),
        "numstability_atlas_sha256": sha256_file(args.numstability_atlas / "declarations.jsonl"),
        "qualification_sha256": sha256_file(args.model_qualification),
        "warm_root_sha256": sha256_file(args.warm_root / "warm-root.json"),
        "runner_sha256": sha256_file(Path(__file__).with_name("design20_matched.py")),
    }


def run(args: argparse.Namespace) -> dict:
    if args.output_root.is_symlink() or not args.output_root.is_absolute():
        raise BenchmarkError("campaign output must be an absolute non-symlink path")
    frozen = _inputs(args)
    identity = hashlib.sha256(canonical_json_bytes(frozen)).hexdigest()
    journal_path = args.output_root / "campaign.json"
    if args.resume_after_review:
        if not journal_path.is_file() or journal_path.is_symlink():
            raise BenchmarkError("no Pilot-20 campaign to resume")
        journal = load_json(journal_path)
        if (journal.get("schema_version") != SCHEMA
                or journal.get("status") != "PAUSED_FIRST_REVIEW"
                or journal.get("inputs_sha256") != identity
                or len(journal.get("pairs", [])) != 1):
            raise BenchmarkError("frozen first-review state or inputs do not match")
        first = journal["pairs"][0]
        if first["task_id"] != frozen["schedule"][0] or first["pair_report_sha256"] != sha256_file(
                args.output_root / first["task_id"] / "pair-report.json"):
            raise BenchmarkError("first measured pair changed during review")
        start_index = 1
        journal["status"] = "RUNNING"
        journal["resumed_after_review_at_utc"] = utc_now()
        write_json_atomic(journal_path, journal, mode=0o400)
    else:
        if args.output_root.exists():
            raise BenchmarkError("campaign already exists; never overwrite or silently rerun")
        args.output_root.mkdir(parents=True, mode=0o700)
        journal = {"schema_version": SCHEMA, "status": "RUNNING",
                   "inputs": frozen, "inputs_sha256": identity,
                   "pairs": [], "created_at_utc": utc_now()}
        write_json_atomic(journal_path, journal, mode=0o400)
        start_index = 0
    with _host_lock():
        for index in range(start_index, len(frozen["schedule"])):
            task_id = frozen["schedule"][index]
            order = "R0,R1" if index % 2 == 0 else "R1,R0"
            pair_root = args.output_root / task_id
            pair_args = argparse.Namespace(
                deployment=args.deployment, mathlib_atlas=args.mathlib_atlas,
                numstability_atlas=args.numstability_atlas,
                model_qualification=args.model_qualification,
                warm_root=args.warm_root, task_id=task_id,
                condition_order=order, output_root=pair_root,
            )
            try:
                pair = run_pair(pair_args)
                uptake = _treatment_uptake(pair_root, pair)
                journal["pairs"].append({
                    "task_id": task_id, "condition_order": order,
                    "pair_status": pair["status"],
                    "pair_report_sha256": sha256_file(pair_root / "pair-report.json"),
                    "r1_over_r0_contestant_system_wall_seconds": pair.get("comparison", {}).get(
                        "r1_over_r0", {}).get("contestant_system_wall_seconds"),
                    "treatment_uptake": uptake,
                })
                if pair["status"] == "PAIR_INCIDENT":
                    journal["status"] = "PAUSED_PAIR_INCIDENT"
                elif index == 0:
                    journal["status"] = "PAUSED_FIRST_REVIEW"
                elif index == len(frozen["schedule"]) - 1:
                    journal["status"] = "COMPLETE"
                write_json_atomic(journal_path, journal, mode=0o400)
                if journal["status"] != "RUNNING":
                    break
            except Exception as error:
                journal["status"] = "PAUSED_CONTROLLER_INCIDENT"
                journal["incident"] = {"task_id": task_id,
                                       "type": type(error).__name__,
                                       "message": str(error),
                                       "recorded_at_utc": utc_now()}
                write_json_atomic(journal_path, journal, mode=0o400)
                raise
    journal["last_updated_at_utc"] = utc_now()
    write_json_atomic(journal_path, journal, mode=0o400)
    return journal


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("deployment", "mathlib-atlas", "numstability-atlas",
                 "model-qualification", "warm-root", "output-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--resume-after-review", action="store_true")
    args = parser.parse_args()
    launched = launch_or_activate(Path(__file__), lane="A")
    if launched is not None:
        return launched
    journal = run(args)
    print(json.dumps({"status": journal["status"],
                      "completed_pairs": len(journal["pairs"]),
                      "scheduled_pairs": len(journal["inputs"]["schedule"])},
                     sort_keys=True))
    return 0 if journal["status"] == "COMPLETE" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot-20 campaign error: {error}", file=sys.stderr)
        raise SystemExit(2)
