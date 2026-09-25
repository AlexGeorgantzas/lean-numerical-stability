#!/usr/bin/env python3
"""Recover Pilot 34's audit incident and unstarted tasks, never its sealed pairs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

TOOLS = Path(__file__).resolve().parents[1] / "formalization_benchmark" / "tools"
sys.path.insert(0, str(TOOLS))

from common import (BenchmarkError, canonical_json_bytes, load_json, sha256_file,
                    utc_now, write_bytes_atomic, write_json_atomic)
from design18_campaign import _host_lock, _treatment_uptake
from design22_campaign import _inputs, _pair_command, _pair_env, LANES, ROOT

SCHEMA = "pilot-35-audit-incident-recovery-campaign-1"
INCIDENT = {"NO_PAIR_REPORT", "PAIR_INCIDENT", "PAIR_PROOF_INCIDENT"}


def verify_source(manifest: dict, corpus: dict) -> tuple[Path, dict]:
    source = Path(manifest["source_campaign_root"])
    path = source / "campaign.json"
    if (not source.is_absolute() or source.is_symlink()
            or sha256_file(path) != manifest["source_campaign_sha256"]):
        raise BenchmarkError("Pilot 34 campaign identity changed")
    prior = load_json(path)
    schedule = corpus["scheduled_order"]
    if (prior.get("status") != "PAUSED_CONCURRENT_INCIDENT"
            or prior.get("inputs_sha256") != manifest["source_inputs_sha256"]
            or prior["inputs"]["schedule"] != schedule or len(schedule) != 15
            or hashlib.sha256(canonical_json_bytes(prior["inputs"])).hexdigest()
            != prior["inputs_sha256"]):
        raise BenchmarkError("Pilot 34 is not the expected paused campaign")
    entries = {item["task_id"]: item for item in prior["pairs"]}
    preserved = manifest["preserved_pair_report_sha256"]
    incident = manifest["incident_pair_report_sha256"]
    recovery = manifest["recovery_task_order"]
    if (len(entries) != len(prior["pairs"]) or len(incident) != 1
            or set(entries) != set(preserved) | set(incident)
            or len(recovery) != len(set(recovery))
            or recovery != [task for task in schedule if task not in preserved]
            or set(recovery) != set(schedule) - set(preserved)):
        raise BenchmarkError("recovery partition or ordering changed")
    # Pilot 34's reviewed canary was launched before the parallel journal's
    # `launches` list began. Its sealed entry is the only permitted exception.
    launched = {entry["task_id"] for entry in prior["launches"]}
    if launched | {schedule[0]} != set(entries):
        raise BenchmarkError("Pilot 34 launched set differs from sealed reports")
    for task, digest in {**preserved, **incident}.items():
        report = source / task / "pair-report.json"
        if (sha256_file(report) != digest
                or entries[task]["pair_report_sha256"] != digest):
            raise BenchmarkError(f"Pilot 34 sealed pair changed: {task}")
        status = load_json(report).get("status")
        if (task in incident and status not in INCIDENT) or (
            task in preserved and status in INCIDENT | {"RUNNING"}
        ):
            raise BenchmarkError(f"Pilot 34 pair status changed: {task}")
    for task in set(recovery) - set(incident):
        if (source / task).exists():
            raise BenchmarkError(f"unstarted Pilot 34 task has artifacts: {task}")
    return source, prior


def record_pair(args: argparse.Namespace, journal: dict, task: str, index: int,
                lane: str, process: subprocess.Popen[bytes],
                overlap: list[str]) -> dict:
    stdout, stderr = process.communicate()
    logs = args.output_root / "controller-logs"
    logs.mkdir(mode=0o700, exist_ok=True)
    out = logs / f"{task}.stdout.log"
    err = logs / f"{task}.stderr.log"
    write_bytes_atomic(out, stdout, mode=0o400)
    write_bytes_atomic(err, stderr, mode=0o400)
    path = args.output_root / task / "pair-report.json"
    pair = load_json(path) if path.is_file() else None
    status = pair.get("status") if isinstance(pair, dict) else "NO_PAIR_REPORT"
    uptake = (_treatment_uptake(args.output_root / task, pair)
              if isinstance(pair, dict) and "R1" in pair.get("conditions", {})
              else {"status": "NOT_AVAILABLE"})
    entry = {
        "task_id": task, "scheduled_index": index, "lane": lane,
        "condition_order": "R0,R1" if index % 2 == 0 else "R1,R0",
        "co_scheduled_task_ids": overlap,
        "process_exit_code": process.returncode, "pair_status": status,
        "pair_report_sha256": sha256_file(path) if path.is_file() else None,
        "stdout_sha256": sha256_file(out), "stderr_sha256": sha256_file(err),
        "proof_pair_status": pair.get("proof_pair_status") if pair else None,
        "treatment_uptake": uptake, "completed_at_utc": utc_now(),
    }
    journal["pairs"].append(entry)
    write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
    return entry


def run_remaining(args: argparse.Namespace, journal: dict,
                  schedule: list[str], recovery: list[str]) -> bool:
    pending = iter((schedule.index(task), task) for task in recovery)
    next_pair = next(pending, None)
    active: dict[str, tuple[str, int, subprocess.Popen[bytes]]] = {}
    overlaps: dict[str, set[str]] = {}
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
                journal["launches"].append({
                    "task_id": task, "original_scheduled_index": index,
                    "lane": lane, "launched_at_utc": utc_now(),
                })
                write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
                next_pair = next(pending, None)
            finished = [lane for lane, (_, _, process) in active.items()
                        if process.poll() is not None]
            if not finished:
                time.sleep(0.2)
                continue
            for lane in finished:
                task, index, process = active.pop(lane)
                entry = record_pair(args, journal, task, index, lane, process,
                                    sorted(overlaps.get(task, set()), key=schedule.index))
                incident = (incident or process.returncode != 0
                            or entry["pair_status"] in INCIDENT)
        return incident
    except Exception:
        for lane, (task, index, process) in list(active.items()):
            if not any(item["task_id"] == task for item in journal["pairs"]):
                try:
                    record_pair(args, journal, task, index, lane, process,
                                sorted(overlaps.get(task, set()), key=schedule.index))
                except Exception:
                    pass
        raise


def run(args: argparse.Namespace) -> dict:
    if (not args.output_root.is_absolute() or args.output_root.exists()
            or args.output_root.is_symlink()):
        raise BenchmarkError("recovery output must be a new absolute directory")
    manifest = load_json(args.recovery_manifest)
    if (manifest.get("schema_version") != "pilot-35-recovery-manifest-1"
            or args.pilot_id != "pilot35-audit-recovery"):
        raise BenchmarkError("wrong Pilot 35 identity")
    corpus = load_json(args.corpus)
    source, prior = verify_source(manifest, corpus)
    frozen = _inputs(args)
    frozen.update({
        "recovery_manifest_sha256": sha256_file(args.recovery_manifest),
        "recovery_controller_sha256": sha256_file(Path(__file__)),
        "source_campaign_sha256": manifest["source_campaign_sha256"],
        "source_campaign_input_identity": prior["inputs_sha256"],
        "recovery_task_order": manifest["recovery_task_order"],
        "original_scheduled_indices": {
            task: corpus["scheduled_order"].index(task)
            for task in manifest["recovery_task_order"]
        },
    })
    identity = hashlib.sha256(canonical_json_bytes(frozen)).hexdigest()
    with _host_lock():
        if args.output_root.exists():
            raise BenchmarkError("recovery output was created concurrently")
        args.output_root.mkdir(parents=True, mode=0o700)
        journal = {
            "schema_version": SCHEMA, "status": "RUNNING_RECOVERY",
            "inputs": frozen, "inputs_sha256": identity,
            "source_campaign_root": str(source),
            "preserved_pair_report_sha256": manifest["preserved_pair_report_sha256"],
            "incident_pair_report_sha256": manifest["incident_pair_report_sha256"],
            "pairs": [], "launches": [], "created_at_utc": utc_now(),
        }
        write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
        try:
            incident = run_remaining(args, journal, corpus["scheduled_order"],
                                     manifest["recovery_task_order"])
            journal["status"] = (
                "PAUSED_RECOVERY_INCIDENT" if incident else "COMPLETE_RECOVERY"
            )
        except Exception as error:
            journal["status"] = "PAUSED_CONTROLLER_INCIDENT"
            journal["incident"] = {"type": type(error).__name__,
                                   "message": str(error), "recorded_at_utc": utc_now()}
            write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
            raise
        journal["last_updated_at_utc"] = utc_now()
        write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
    return journal


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("deployment", "mathlib-atlas", "numstability-atlas",
                 "model-qualification", "warm-root", "output-root", "corpus",
                 "admission", "task-root", "prompt-root", "proof-prompt-path",
                 "warm-scout-prompt-path", "recovery-manifest"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--pilot-id", required=True)
    parser.add_argument("--selection-policy", required=True)
    parser.add_argument("--root-limit", required=True, type=int)
    parser.add_argument("--dependency-limit", required=True, type=int)
    parser.add_argument("--proof-time-limit-seconds", required=True, type=float)
    parser.add_argument("--proof-submission-limit", required=True, type=int)
    parser.add_argument("--warm-root-schema-version", required=True)
    parser.add_argument("--proof-after-faithful", action="store_true")
    args = parser.parse_args()
    if not args.proof_after_faithful:
        raise BenchmarkError("recovery requires complete-proof attempts")
    journal = run(args)
    print(json.dumps({"status": journal["status"],
                      "completed_recovery_pairs": len(journal["pairs"]),
                      "scheduled_recovery_pairs": len(journal["inputs"]["recovery_task_order"])},
                     sort_keys=True))
    return 0 if journal["status"] == "COMPLETE_RECOVERY" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 35 recovery error: {error}", file=sys.stderr)
        raise SystemExit(2)
