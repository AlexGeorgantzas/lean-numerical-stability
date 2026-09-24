#!/usr/bin/env python3
"""Run only the unsealed LL07-THM7 pair in a distinct, disclosed recovery."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

TOOLS = Path(__file__).resolve().parents[1] / "formalization_benchmark" / "tools"
sys.path.insert(0, str(TOOLS))

from common import (BenchmarkError, canonical_json_bytes, load_json, sha256_file,
                    utc_now, write_json_atomic)
from design18_campaign import _host_lock
from design22_campaign import _inputs, _pair_command, _pair_env, _record_pair, ROOT


SCHEMA = "pilot-32-one-pair-recovery-campaign-1"
MANIFEST_SCHEMA = "pilot-32-one-pair-recovery-1"
TASK = "LL07-THM7"
MIN_ROOT_FREE_BYTES = 2 * 2**30


def _verify_prior(manifest: dict, corpus: dict) -> tuple[dict, dict]:
    if (manifest.get("schema_version") != MANIFEST_SCHEMA
            or manifest.get("remaining_task_id") != TASK
            or manifest.get("original_scheduled_index") != 8
            or manifest.get("condition_order") != "R0,R1"
            or manifest.get("lane") != "C"):
        raise BenchmarkError("wrong one-pair recovery manifest")
    schedule = corpus["scheduled_order"]
    if len(schedule) != 10 or schedule[8] != TASK:
        raise BenchmarkError("the original ten-task schedule changed")
    prior_manifest_path = ROOT.parents[2] / manifest["pilot29_manifest"]
    prior_manifest = load_json(prior_manifest_path)
    pilot29_root = Path(prior_manifest["source_campaign_root"])
    pilot29_path = pilot29_root / "campaign.json"
    if (pilot29_root.is_symlink()
            or sha256_file(pilot29_path) != prior_manifest["source_campaign_sha256"]):
        raise BenchmarkError("Pilot 29 journal changed")
    pilot29 = load_json(pilot29_path)
    if (pilot29.get("status") != "RUNNING_PARALLEL"
            or pilot29["inputs"]["schedule"] != schedule
            or len(pilot29["pairs"]) != 5):
        raise BenchmarkError("Pilot 29 source is not the preserved five-pair campaign")
    for task, digest in prior_manifest["preserved_pair_report_sha256"].items():
        entry = next((p for p in pilot29["pairs"] if p["task_id"] == task), None)
        if (entry is None or entry["pair_report_sha256"] != digest
                or sha256_file(pilot29_root / task / "pair-report.json") != digest):
            raise BenchmarkError(f"Pilot 29 sealed pair changed: {task}")
    for task, digest in prior_manifest["interrupted_partial_pair_report_sha256"].items():
        if sha256_file(pilot29_root / task / "pair-report.json") != digest:
            raise BenchmarkError(f"Pilot 29 partial evidence changed: {task}")

    pilot31_root = Path(manifest["pilot31_campaign_root"])
    pilot31_path = pilot31_root / "campaign.json"
    if (not pilot31_root.is_absolute() or pilot31_root.is_symlink()
            or sha256_file(pilot31_path) != manifest["pilot31_campaign_sha256"]):
        raise BenchmarkError("Pilot 31 journal changed")
    pilot31 = load_json(pilot31_path)
    if (pilot31.get("status") != "RUNNING_RECOVERY"
            or pilot31.get("inputs_sha256")
            != manifest["pilot31_input_identity_sha256"]
            or pilot31["inputs"]["schedule"] != schedule
            or len(pilot31["pairs"]) != 4
            or len(pilot31["launches"]) != 5):
        raise BenchmarkError("Pilot 31 is not the expected stopped recovery")
    preserved = manifest["pilot31_sealed_pair_report_sha256"]
    if ({p["task_id"] for p in pilot31["pairs"]} != set(preserved)
            or {p["task_id"] for p in pilot31["launches"]}
            != set(preserved) | {TASK}):
        raise BenchmarkError("Pilot 31 launched/sealed partition changed")
    for task, digest in preserved.items():
        entry = next(p for p in pilot31["pairs"] if p["task_id"] == task)
        if (entry["pair_report_sha256"] != digest
                or sha256_file(pilot31_root / task / "pair-report.json") != digest
                or load_json(pilot31_root / task / "pair-report.json").get("status")
                == "RUNNING"):
            raise BenchmarkError(f"Pilot 31 sealed pair changed: {task}")
    partial_path = pilot31_root / TASK / "pair-report.json"
    if (sha256_file(partial_path)
            != manifest["pilot31_interrupted_pair_report_sha256"]
            or load_json(partial_path).get("status") != "RUNNING"):
        raise BenchmarkError("Pilot 31 interrupted pair changed")
    return pilot29, pilot31


def run(args: argparse.Namespace) -> dict:
    if (not args.output_root.is_absolute() or args.output_root.exists()
            or args.output_root.is_symlink()):
        raise BenchmarkError("output must be a new absolute directory")
    if args.pilot_id != "pilot32-ll07-thm7-recovery":
        raise BenchmarkError("wrong Pilot 32 identity")
    manifest = load_json(args.recovery_manifest)
    corpus = load_json(args.corpus)
    pilot29, pilot31 = _verify_prior(manifest, corpus)
    if shutil.disk_usage("/").free < MIN_ROOT_FREE_BYTES:
        raise BenchmarkError("system filesystem has less than 2 GiB free")
    frozen = _inputs(args)
    unchanged_fields = (
        "corpus_sha256", "admission_sha256", "schedule",
        "condition_order_policy", "packets", "sources", "prompts",
        "audit_prompts", "deployment_sha256", "mathlib_atlas_sha256",
        "numstability_atlas_sha256", "qualification_sha256",
        "warm_root_sha256", "lanes", "pair_runner_sha256",
        "lane_wrapper_sha256", "proof_protocol",
    )
    for field in unchanged_fields:
        if frozen.get(field) != pilot31["inputs"].get(field):
            raise BenchmarkError(f"frozen input differs from Pilot 31: {field}")
    frozen.update({
        "recovery_manifest_sha256": sha256_file(args.recovery_manifest),
        "recovery_controller_sha256": sha256_file(Path(__file__)),
        "pilot29_input_identity": pilot29["inputs_sha256"],
        "pilot31_input_identity": pilot31["inputs_sha256"],
        "pilot31_campaign_sha256": manifest["pilot31_campaign_sha256"],
        "remaining_task_order": [TASK],
        "original_scheduled_index": 8,
        "single_lane": "C",
        "system_free_bytes_at_preflight": shutil.disk_usage("/").free,
    })
    identity = hashlib.sha256(canonical_json_bytes(frozen)).hexdigest()
    with _host_lock():
        if args.output_root.exists():
            raise BenchmarkError("output appeared concurrently")
        args.output_root.mkdir(parents=True, mode=0o700)
        journal = {
            "schema_version": SCHEMA,
            "status": "RUNNING_ONE_PAIR_RECOVERY",
            "inputs": frozen,
            "inputs_sha256": identity,
            "source_campaign_roots": [
                load_json(ROOT.parents[2] / manifest["pilot29_manifest"])
                ["source_campaign_root"],
                manifest["pilot31_campaign_root"],
            ],
            "preserved_pilot31_pair_report_sha256":
                manifest["pilot31_sealed_pair_report_sha256"],
            "interrupted_pilot31_pair_report_sha256":
                manifest["pilot31_interrupted_pair_report_sha256"],
            "pairs": [],
            "launches": [{"task_id": TASK, "original_scheduled_index": 8,
                          "lane": "C", "launched_at_utc": utc_now()}],
            "created_at_utc": utc_now(),
        }
        write_json_atomic(args.output_root / "campaign.json", journal, mode=0o400)
        try:
            result = subprocess.run(
                _pair_command(args, TASK, 8, "C"), cwd=ROOT.parents[2],
                env=_pair_env(), capture_output=True, check=False,
            )
            entry = _record_pair(args, journal, TASK, 8, "C",
                                 result.returncode, result.stdout, result.stderr, [])
            if entry["pair_status"] in ("NO_PAIR_REPORT", "RUNNING"):
                journal["status"] = "PAUSED_UNSEALED_PAIR"
            elif (result.returncode != 0
                  or entry["pair_status"] in ("PAIR_INCIDENT", "PAIR_PROOF_INCIDENT")):
                journal["status"] = "COMPLETE_ONE_PAIR_WITH_INCIDENT"
            else:
                journal["status"] = "COMPLETE_ONE_PAIR_RECOVERY"
        except Exception as error:
            journal["status"] = "PAUSED_CONTROLLER_INCIDENT"
            journal["incident"] = {"type": type(error).__name__,
                                   "message": str(error),
                                   "recorded_at_utc": utc_now()}
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
        raise BenchmarkError("complete-proof attempts are required")
    journal = run(args)
    print(json.dumps({"status": journal["status"],
                      "completed_recovery_pairs": len(journal["pairs"])},
                     sort_keys=True))
    return 0 if journal["status"].startswith("COMPLETE_ONE_PAIR") else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 32 recovery error: {error}", file=sys.stderr)
        raise SystemExit(2)
