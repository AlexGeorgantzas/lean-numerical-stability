#!/usr/bin/env python3
"""Run the frozen Pilot-18 schedule, with automatic early-pair review gates.

There is no result-oriented retry. A halted campaign retains its pair outputs
and requires a new pilot identity for any source, router, prompt, or controller
change. The user can inspect the journal before any further work.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import sys
from typing import Any, Callable

from common import BenchmarkError, load_json, sha256_file, utc_now, write_json_atomic
from design18_envelope import launch_or_activate
from design18_matched import run as run_pair
from design18_preflight import DESIGN_ROOT, check_corpus


SCHEMA = "pilot-18-campaign-1"
SLOWDOWN_GATE = 1.5
HOST_LOCK = Path("/tmp/highambench-design16-timed-contestant.lock")


@contextmanager
def _host_lock():
    if HOST_LOCK.is_symlink():
        raise BenchmarkError("timed-contestant host lock may not be a symlink")
    flags = os.O_RDWR | os.O_CREAT
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(HOST_LOCK, flags, 0o600)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise BenchmarkError("another timed campaign holds the host lock") from error
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _treatment_uptake(pair_root: Path, report: dict[str, Any]) -> dict[str, Any]:
    """Measure reached treatment declarations, not mere packet exposure."""
    r1 = report["conditions"]["R1"]
    accepted = next(
        (index for index, attempt in enumerate(r1.get("attempts", []), 1)
         if attempt.get("status") == "ACCEPTED_FAITHFUL"),
        None,
    )
    if accepted is None:
        return {"status": "NO_ACCEPTED_R1_STATEMENT", "direct_reached": [],
                "observed_imports": []}
    attempt_root = pair_root / "R1" / "submissions" / f"{accepted:02d}"
    private_path = attempt_root / "audit-preparation" / "private_semantic_manifest.json"
    interface_path = attempt_root / "treatment-interface.json"
    private = load_json(private_path)
    interface = load_json(interface_path)
    raw = private.get("raw_semantic_report")
    if not isinstance(raw, dict):
        raise BenchmarkError("accepted R1 semantic report is missing")
    dependencies = raw.get("dependencies")
    edges = raw.get("edges")
    if not isinstance(dependencies, list) or not isinstance(edges, list):
        raise BenchmarkError("accepted R1 dependency graph is missing")
    owners = {entry.get("name"): entry.get("owner_module")
              for entry in dependencies if isinstance(entry, dict)}
    child_edges: dict[str, set[str]] = {}
    for edge in edges:
        if not isinstance(edge, dict) or not isinstance(edge.get("parent"), str) \
                or not isinstance(edge.get("child"), str):
            raise BenchmarkError("accepted R1 dependency edge is malformed")
        child_edges.setdefault(edge["parent"], set()).add(edge["child"])
    pending = ["HighamBenchCandidate.target"]
    visited: set[str] = set()
    reached: set[str] = set()
    while pending:
        parent = pending.pop()
        if parent in visited:
            continue
        visited.add(parent)
        for child in child_edges.get(parent, set()):
            owner = owners.get(child)
            if not isinstance(owner, str):
                continue
            if owner == "NumStability" or owner.startswith("NumStability."):
                reached.add(child)
            elif owner == "Candidate" or owner.startswith("Candidate."):
                pending.append(child)
    imports = interface.get("observed_numstability_imports")
    if not isinstance(imports, list):
        raise BenchmarkError("accepted R1 import record is missing")
    return {
        "status": "DIRECT_TREATMENT_REACHED" if reached else "NO_DIRECT_TREATMENT_REACHED",
        "direct_reached": sorted(reached),
        "observed_imports": imports,
        "private_semantic_manifest_sha256": sha256_file(private_path),
        "treatment_interface_sha256": sha256_file(interface_path),
    }


def _early_review(pair_root: Path, pair: dict[str, Any], *, uptake: dict) -> list[str]:
    reasons: list[str] = []
    if pair.get("status") != "AUDITED_FAITHFUL_PAIR":
        reasons.append("PAIR_NOT_BOTH_AUDITED_FAITHFUL")
    ratio = pair.get("comparison", {}).get("r1_over_r0", {}).get(
        "contestant_system_wall_seconds"
    )
    if isinstance(ratio, (int, float)) and ratio >= SLOWDOWN_GATE:
        reasons.append("R1_CONTESTANT_SYSTEM_SLOWDOWN_AT_LEAST_1_5")
    if uptake.get("status") == "NO_DIRECT_TREATMENT_REACHED":
        reasons.append("NO_DIRECT_TREATMENT_REACHED_BY_FINAL_R1_STATEMENT")
    if uptake.get("status") == "NO_ACCEPTED_R1_STATEMENT":
        reasons.append("NO_ACCEPTED_R1_STATEMENT")
    return reasons


def run_campaign(args: argparse.Namespace, *, pair_runner: Callable = run_pair,
                 uptake_reader: Callable = _treatment_uptake,
                 require_envelope: bool = True) -> dict[str, Any]:
    if require_envelope:
        from hardware import snapshot_hardware
        snapshot_hardware(strict=True)
        with _host_lock():
            return _run_campaign_unlocked(args, pair_runner=pair_runner,
                                          uptake_reader=uptake_reader)
    return _run_campaign_unlocked(args, pair_runner=pair_runner,
                                  uptake_reader=uptake_reader)


def _run_campaign_unlocked(args: argparse.Namespace, *, pair_runner: Callable,
                           uptake_reader: Callable) -> dict[str, Any]:
    corpus, _packets, flags = check_corpus()
    if flags:
        raise BenchmarkError(f"source flags bar measured Pilot 18 runs: {flags}")
    if not args.output_root.is_absolute():
        raise BenchmarkError("campaign output must be an absolute path")
    if args.output_root.exists() or args.output_root.is_symlink():
        raise BenchmarkError("campaign output already exists; no silent resume or overwrite")
    schedule = corpus["scheduled_order"]
    args.output_root.mkdir(parents=True, mode=0o700)
    journal = {
        "schema_version": SCHEMA,
        "status": "RUNNING",
        "pilot": "18",
        "scheduled_order": schedule,
        "corpus_sha256": sha256_file(DESIGN_ROOT / "CORPUS_12.json"),
        "early_review_order": corpus["early_review_order"],
        "early_slowdown_gate": SLOWDOWN_GATE,
        "pairs": [],
        "created_at_utc": utc_now(),
    }
    journal_path = args.output_root / "campaign.json"
    write_json_atomic(journal_path, journal, mode=0o400)
    for index, task_id in enumerate(schedule):
        order = "R0,R1" if index % 2 == 0 else "R1,R0"
        pair_root = args.output_root / task_id
        pair_args = argparse.Namespace(
            deployment=args.deployment,
            mathlib_atlas=args.mathlib_atlas,
            model_qualification=args.model_qualification,
            warm_root=args.warm_root,
            task_id=task_id,
            condition_order=order,
            output_root=pair_root,
        )
        try:
            pair = pair_runner(pair_args)
            uptake = uptake_reader(pair_root, pair)
            reasons = _early_review(pair_root, pair, uptake=uptake) if index < 3 else []
            record = {
                "task_id": task_id,
                "condition_order": order,
                "pair_status": pair.get("status"),
                "pair_report_sha256": sha256_file(pair_root / "pair-report.json"),
                "r1_over_r0_contestant_system_wall_seconds": pair.get(
                    "comparison", {}).get("r1_over_r0", {}).get(
                    "contestant_system_wall_seconds"),
                "treatment_uptake": uptake,
                "early_review_reasons": reasons,
            }
            journal["pairs"].append(record)
            if pair.get("status") == "PAIR_INCIDENT":
                journal["status"] = "PAUSED_PAIR_INCIDENT"
            elif reasons:
                journal["status"] = "PAUSED_EARLY_REVIEW"
            elif index == len(schedule) - 1:
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
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", required=True, type=Path)
    parser.add_argument("--mathlib-atlas", required=True, type=Path)
    parser.add_argument("--model-qualification", required=True, type=Path)
    parser.add_argument("--warm-root", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    journal = run_campaign(parser.parse_args())
    print(json.dumps({"status": journal["status"],
                      "completed_pairs": len(journal["pairs"]),
                      "scheduled_pairs": len(journal["scheduled_order"])}, sort_keys=True))
    return 0 if journal["status"] == "COMPLETE" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 18 campaign error: {error}", file=sys.stderr)
        raise SystemExit(2)
