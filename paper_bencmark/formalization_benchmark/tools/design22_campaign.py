#!/usr/bin/env python3
"""Frozen development canary, review pause, then three refilled isolated lanes."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from common import (BenchmarkError, canonical_json_bytes, load_json, sha256_file,
                    utc_now, write_bytes_atomic, write_json_atomic)
from design18_campaign import _host_lock, _treatment_uptake
from design20_admission import ADMISSION
from design20_matched import CORPUS, ROOT
from design20_lanes import LANE_CPUS, LANE_MEMORY_BYTES


SCHEMA = "pilot-26-development-campaign-1"
PAIR_SCRIPT = Path(__file__).with_name("design22_pair_lane.py")
LANES = ("A", "B", "C")


def _controller_commit() -> str:
    repo = ROOT.parents[2]
    commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", "HEAD"], cwd=repo, text=True,
    ).strip()
    if subprocess.run(["git", "diff", "--quiet", "HEAD"], cwd=repo,
                      check=False).returncode != 0:
        raise BenchmarkError("development controller has tracked uncommitted changes")
    return commit


def _inputs(args: argparse.Namespace) -> dict:
    corpus_path = getattr(args, "corpus", None) or CORPUS
    admission_path = getattr(args, "admission", None) or ADMISSION
    corpus = load_json(corpus_path)
    schedule = corpus["scheduled_order"]
    if len(schedule) < 1 or len(schedule) != len(set(schedule)):
        raise BenchmarkError("development schedule must be nonempty with unique tasks")
    if not isinstance(args.pilot_id, str) or not args.pilot_id.startswith("pilot"):
        raise BenchmarkError("an explicit pilot identity is required")
    return {
        "pilot_id": args.pilot_id,
        "controller_commit": _controller_commit(),
        "corpus_sha256": sha256_file(corpus_path),
        "admission_sha256": sha256_file(admission_path),
        "schedule": schedule,
        "condition_order_policy": "alternate by frozen zero-based schedule index",
        "packets": {task: sha256_file(ROOT / "packets" / f"{task}.json")
                    for task in schedule},
        "sources": {task: load_json(ROOT / "packets" / f"{task}.json")["paper_pdf"]["sha256"]
                    for task in schedule},
        "prompts": {name: sha256_file(ROOT / "prompts" / f"{name}.md")
                    for name in ("common", "library_appendix", "scout_compact")},
        "audit_prompts": {
            name: sha256_file(ROOT.parent / "audit" / "prompts" / f"{name}.md")
            for name in ("blind_translation", "direct_judge", "roundtrip_judge",
                         "adjudicator")
        },
        "deployment_sha256": sha256_file(args.deployment),
        "mathlib_atlas_sha256": sha256_file(args.mathlib_atlas / "declarations.jsonl"),
        "numstability_atlas_sha256": sha256_file(args.numstability_atlas / "declarations.jsonl"),
        "qualification_sha256": sha256_file(args.model_qualification),
        "warm_root_sha256": sha256_file(args.warm_root / "warm-root.json"),
        "lanes": {lane: {"cpus": list(cpus), "memory_limit_bytes": LANE_MEMORY_BYTES}
                  for lane, cpus in LANE_CPUS.items()},
        "pair_runner_sha256": sha256_file(Path(__file__).with_name("design20_matched.py")),
        "lane_wrapper_sha256": sha256_file(PAIR_SCRIPT),
    }


def _pair_command(args: argparse.Namespace, task_id: str, index: int, lane: str) -> list[str]:
    order = "R0,R1" if index % 2 == 0 else "R1,R0"
    command = [
        sys.executable, str(PAIR_SCRIPT),
        "--deployment", str(args.deployment),
        "--mathlib-atlas", str(args.mathlib_atlas),
        "--numstability-atlas", str(args.numstability_atlas),
        "--model-qualification", str(args.model_qualification),
        "--warm-root", str(args.warm_root),
        "--output-root", str(args.output_root / task_id),
        "--task-id", task_id,
        "--condition-order", order,
        "--lane", lane,
    ]
    if getattr(args, "corpus", None) is not None:
        command.extend(("--corpus", str(args.corpus)))
    if getattr(args, "admission", None) is not None:
        command.extend(("--admission", str(args.admission)))
    return command


def _pair_env() -> dict[str, str]:
    # The orchestrator is outside every lane.  Even if invoked by a scheduler
    # from an existing service, a child must establish its own lane boundary.
    env = dict(os.environ)
    for name in ("HIGHAMBENCH_TITAN_ENVELOPE", "HIGHAMBENCH_HARDWARE_PROFILE",
                 "HIGHAMBENCH_COMMAND_CGROUP_PROCS"):
        env.pop(name, None)
    return env


def _record_pair(args: argparse.Namespace, journal: dict, task_id: str,
                 index: int, lane: str, code: int, stdout: bytes, stderr: bytes,
                 co_scheduled: list[str]) -> dict:
    logs = args.output_root / "controller-logs"
    logs.mkdir(mode=0o700, exist_ok=True)
    stdout_path = logs / f"{task_id}.stdout.log"
    stderr_path = logs / f"{task_id}.stderr.log"
    write_bytes_atomic(stdout_path, stdout, mode=0o400)
    write_bytes_atomic(stderr_path, stderr, mode=0o400)
    report_path = args.output_root / task_id / "pair-report.json"
    pair = load_json(report_path) if report_path.is_file() else None
    status = pair.get("status") if isinstance(pair, dict) else "NO_PAIR_REPORT"
    uptake = (_treatment_uptake(args.output_root / task_id, pair)
              if isinstance(pair, dict) and "R1" in pair.get("conditions", {})
              else {"status": "NOT_AVAILABLE"})
    entry = {
        "task_id": task_id, "scheduled_index": index, "lane": lane,
        "condition_order": "R0,R1" if index % 2 == 0 else "R1,R0",
        "co_scheduled_task_ids": co_scheduled,
        "process_exit_code": code, "pair_status": status,
        "pair_report_sha256": sha256_file(report_path) if report_path.is_file() else None,
        "stdout_sha256": sha256_file(stdout_path),
        "stderr_sha256": sha256_file(stderr_path),
        "r1_over_r0_contestant_system_wall_seconds": (
            pair.get("comparison", {}).get("r1_over_r0", {}).get(
                "contestant_system_wall_seconds") if isinstance(pair, dict) else None),
        "treatment_uptake": uptake,
        "completed_at_utc": utc_now(),
    }
    journal["pairs"].append(entry)
    write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
    return entry


def _run_refilled_lanes(args: argparse.Namespace, journal: dict,
                        schedule: list[str]) -> bool:
    """Start a new pair on a freed lane without changing its hardware envelope.

    On an incident, launch no further pairs, but allow all already-running pairs
    to finish and seal before releasing the host lock.  Record every actual
    co-scheduled companion, including one that completed earlier.
    """
    pending = iter(enumerate(schedule[1:], start=1))
    active: dict[str, tuple[str, int, subprocess.Popen[bytes]]] = {}
    overlaps: dict[str, set[str]] = {}
    next_pair = next(pending, None)
    incident = False
    try:
        while active or (next_pair is not None and not incident):
            for lane in LANES:
                if incident or next_pair is None or lane in active:
                    continue
                index, task = next_pair
                companions = [item[0] for item in active.values()]
                process = subprocess.Popen(
                    _pair_command(args, task, index, lane), cwd=ROOT.parents[2],
                    env=_pair_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                active[lane] = (task, index, process)
                overlaps.setdefault(task, set()).update(companions)
                for companion in companions:
                    overlaps.setdefault(companion, set()).add(task)
                journal.setdefault("launches", []).append({
                    "task_id": task, "scheduled_index": index, "lane": lane,
                    "launched_at_utc": utc_now(),
                })
                write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
                next_pair = next(pending, None)
            finished = [lane for lane, (_, _, process) in active.items()
                        if process.poll() is not None]
            if not finished:
                time.sleep(0.2)
                continue
            for lane in finished:
                task, index, process = active[lane]
                stdout, stderr = process.communicate()
                companions = sorted(overlaps.get(task, set()),
                                    key=schedule.index)
                entry = _record_pair(args, journal, task, index, lane,
                                     process.returncode, stdout, stderr, companions)
                del active[lane]
                incident = incident or process.returncode != 0 or entry["pair_status"] in {
                    "NO_PAIR_REPORT", "PAIR_INCIDENT",
                }
        return incident
    except Exception:
        # An orchestrator error does not orphan an already-launched measured
        # pair.  Seal each sibling before the outer handler records the pause.
        for lane, (task, index, process) in list(active.items()):
            stdout, stderr = process.communicate()
            if not any(item["task_id"] == task for item in journal["pairs"]):
                try:
                    _record_pair(args, journal, task, index, lane,
                                 process.returncode, stdout, stderr,
                                 sorted(overlaps.get(task, set()),
                                        key=schedule.index))
                except Exception:
                    pass
        raise


def run(args: argparse.Namespace) -> dict:
    if not args.output_root.is_absolute() or args.output_root.is_symlink():
        raise BenchmarkError("pilot output must be an absolute non-symlink path")
    frozen = _inputs(args)
    identity = hashlib.sha256(canonical_json_bytes(frozen)).hexdigest()
    journal_path = args.output_root / "campaign.json"
    if args.resume_after_review:
        if not journal_path.is_file() or journal_path.is_symlink():
            raise BenchmarkError("first-review campaign does not exist")
        journal = load_json(journal_path)
        if (journal.get("schema_version") != SCHEMA
                or journal.get("status") != "PAUSED_FIRST_REVIEW"
                or journal.get("inputs_sha256") != identity
                or len(journal.get("pairs", [])) != 1):
            raise BenchmarkError("frozen first-review inputs do not match")
        first = journal["pairs"][0]
        first_report = args.output_root / frozen["schedule"][0] / "pair-report.json"
        if (first.get("task_id") != frozen["schedule"][0]
                or first.get("pair_report_sha256") != sha256_file(first_report)):
            raise BenchmarkError("first pair changed during review")
        journal["status"] = "RUNNING_PARALLEL"
        journal["resumed_after_review_at_utc"] = utc_now()
        write_json_atomic(journal_path, journal, mode=0o400)
    else:
        if args.output_root.exists():
            raise BenchmarkError("campaign already exists; never overwrite")
        args.output_root.mkdir(parents=True, mode=0o700)
        journal = {"schema_version": SCHEMA, "status": "RUNNING_FIRST_PAIR",
                   "inputs": frozen, "inputs_sha256": identity, "pairs": [],
                   "created_at_utc": utc_now()}
        write_json_atomic(journal_path, journal, mode=0o400)

    try:
        with _host_lock():
            if not args.resume_after_review:
                task = frozen["schedule"][0]
                result = subprocess.run(_pair_command(args, task, 0, "A"),
                                        cwd=ROOT.parents[2], env=_pair_env(),
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                        check=False)
                entry = _record_pair(args, journal, task, 0, "A", result.returncode,
                                     result.stdout, result.stderr, [])
                journal["status"] = (
                    "PAUSED_FIRST_REVIEW" if result.returncode == 0
                    and entry["pair_status"] not in {"NO_PAIR_REPORT", "PAIR_INCIDENT"}
                    else "PAUSED_FIRST_PAIR_INCIDENT"
                )
            else:
                incident = _run_refilled_lanes(args, journal, frozen["schedule"])
                journal["status"] = "PAUSED_CONCURRENT_INCIDENT" if incident else "COMPLETE"
    except Exception as error:
        journal["status"] = "PAUSED_CONTROLLER_INCIDENT"
        journal["incident"] = {"type": type(error).__name__, "message": str(error),
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
    parser.add_argument("--pilot-id", required=True)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--admission", type=Path)
    parser.add_argument("--resume-after-review", action="store_true")
    args = parser.parse_args()
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
        print(f"Development campaign error: {error}", file=sys.stderr)
        raise SystemExit(2)
