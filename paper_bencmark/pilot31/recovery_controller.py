#!/usr/bin/env python3
"""Run only Pilot 29's five unfinished tasks under a distinct recovery identity."""

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
                    utc_now, write_json_atomic)
from design18_campaign import _host_lock
from design22_campaign import (_inputs, _pair_command, _pair_env, _record_pair,
                               LANES, ROOT)


SCHEMA = "pilot-31-five-pair-recovery-campaign-1"
INCIDENT_STATUSES = {"NO_PAIR_REPORT", "PAIR_INCIDENT", "PAIR_PROOF_INCIDENT"}


def _verify_source(manifest: dict, corpus: dict) -> tuple[Path, dict]:
    source = Path(manifest["source_campaign_root"])
    campaign_path = source / "campaign.json"
    if (not source.is_absolute() or source.is_symlink()
            or sha256_file(campaign_path) != manifest["source_campaign_sha256"]):
        raise BenchmarkError("Pilot 29 source campaign changed")
    campaign = load_json(campaign_path)
    schedule = corpus["scheduled_order"]
    if (campaign.get("status") != "RUNNING_PARALLEL"
            or campaign["inputs"]["schedule"] != schedule
            or len(schedule) != 10
            or len(campaign.get("pairs", [])) != 5):
        raise BenchmarkError("Pilot 29 is not the expected interrupted ten-task campaign")
    sealed = {entry["task_id"]: entry for entry in campaign["pairs"]}
    preserved = manifest["preserved_pair_report_sha256"]
    partial = manifest["interrupted_partial_pair_report_sha256"]
    remaining = manifest["remaining_task_order"]
    if (set(sealed) != set(preserved) or len(remaining) != 5
            or len(set(remaining)) != 5
            or set(remaining) != set(schedule) - set(preserved)
            or set(partial) - set(remaining)):
        raise BenchmarkError("recovery task partition changed")
    launched = {entry["task_id"] for entry in campaign.get("launches", [])}
    if launched - set(sealed) != set(partial):
        raise BenchmarkError("interrupted launch set changed")
    for task_id, digest in preserved.items():
        pair_path = source / task_id / "pair-report.json"
        if (sha256_file(pair_path) != digest
                or sealed[task_id]["pair_report_sha256"] != digest
                or load_json(pair_path).get("status") in INCIDENT_STATUSES | {"RUNNING"}):
            raise BenchmarkError(f"sealed Pilot 29 pair changed: {task_id}")
    for task_id, digest in partial.items():
        pair_path = source / task_id / "pair-report.json"
        if (sha256_file(pair_path) != digest
                or load_json(pair_path).get("status") != "RUNNING"):
            raise BenchmarkError(f"partial Pilot 29 pair changed: {task_id}")
    for task_id in set(remaining) - set(partial):
        if (source / task_id).exists():
            raise BenchmarkError(f"unstarted Pilot 29 task has artifacts: {task_id}")
    return source, campaign


def _run_remaining(args: argparse.Namespace, journal: dict,
                   schedule: list[str], remaining: list[str]) -> bool:
    pending = iter((schedule.index(task), task) for task in remaining)
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
                task, index, process = active[lane]
                stdout, stderr = process.communicate()
                companions = sorted(overlaps.get(task, set()), key=schedule.index)
                entry = _record_pair(args, journal, task, index, lane,
                                     process.returncode, stdout, stderr, companions)
                del active[lane]
                incident = (incident or process.returncode != 0
                            or entry["pair_status"] in INCIDENT_STATUSES)
        return incident
    except Exception:
        for lane, (task, index, process) in list(active.items()):
            stdout, stderr = process.communicate()
            if not any(item["task_id"] == task for item in journal["pairs"]):
                try:
                    _record_pair(args, journal, task, index, lane,
                                 process.returncode, stdout, stderr,
                                 sorted(overlaps.get(task, set()), key=schedule.index))
                except Exception:
                    pass
        raise


def run(args: argparse.Namespace) -> dict:
    if (not args.output_root.is_absolute() or args.output_root.exists()
            or args.output_root.is_symlink()):
        raise BenchmarkError("recovery output must be a new absolute directory")
    manifest = load_json(args.recovery_manifest)
    if manifest.get("schema_version") != "pilot-31-recovery-composite-1":
        raise BenchmarkError("wrong recovery manifest")
    if args.pilot_id != "pilot31-five-pair-recovery":
        raise BenchmarkError("wrong Pilot 31 identity")
    corpus = load_json(args.corpus)
    source, prior = _verify_source(manifest, corpus)
    frozen = _inputs(args)
    frozen["recovery_manifest_sha256"] = sha256_file(args.recovery_manifest)
    frozen["recovery_controller_sha256"] = sha256_file(Path(__file__))
    frozen["source_campaign_sha256"] = manifest["source_campaign_sha256"]
    frozen["source_campaign_input_identity"] = prior["inputs_sha256"]
    frozen["remaining_task_order"] = manifest["remaining_task_order"]
    frozen["original_scheduled_indices"] = {
        task: corpus["scheduled_order"].index(task)
        for task in manifest["remaining_task_order"]
    }
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
            "interrupted_partial_pair_report_sha256":
                manifest["interrupted_partial_pair_report_sha256"],
            "pairs": [], "launches": [], "created_at_utc": utc_now(),
        }
        write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
        try:
            incident = _run_remaining(
                args, journal, corpus["scheduled_order"],
                manifest["remaining_task_order"],
            )
            journal["status"] = (
                "PAUSED_RECOVERY_INCIDENT" if incident else "COMPLETE_RECOVERY"
            )
        except Exception as error:
            journal["status"] = "PAUSED_CONTROLLER_INCIDENT"
            journal["incident"] = {
                "type": type(error).__name__, "message": str(error),
                "recorded_at_utc": utc_now(),
            }
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
                      "scheduled_recovery_pairs":
                          len(journal["inputs"]["remaining_task_order"])},
                     sort_keys=True))
    return 0 if journal["status"] == "COMPLETE_RECOVERY" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 31 recovery error: {error}", file=sys.stderr)
        raise SystemExit(2)
