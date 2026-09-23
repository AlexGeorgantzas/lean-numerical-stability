#!/usr/bin/env python3
"""Non-contestant fixed-workload calibration for Pilot-20 lane contention.

Run each lane alone, then all three concurrently with identical inputs. This
measures host CPU/memory interference only; it cannot certify external model
provider independence. Outputs are immutable-path JSON artifacts.
"""

from __future__ import annotations

import argparse
import hashlib
import multiprocessing as mp
import os
from pathlib import Path
import sys
import time

from common import BenchmarkError, sha256_file, utc_now, write_json_atomic
from design20_envelope import launch_or_activate
from design20_telemetry import CgroupSampler, lane_service_cgroup
from hardware import snapshot_hardware


def _worker(size_mib: int, rounds: int, ready: mp.Queue, start: mp.Event,
            results: mp.Queue) -> None:
    try:
        chunk = bytes(range(256)) * 4096
        block = bytearray(size_mib * 1024 ** 2)
        for offset in range(0, len(block), len(chunk)):
            block[offset:offset + len(chunk)] = chunk[:min(len(chunk), len(block) - offset)]
        ready.put(True)
        if not start.wait(timeout=120):
            raise RuntimeError("calibration start barrier timed out")
        begun = time.monotonic()
        digest = hashlib.sha256()
        for _ in range(rounds):
            digest.update(block)
        results.put({"seconds": time.monotonic() - begun, "sha256": digest.hexdigest()})
    except Exception as error:
        results.put({"error": f"{type(error).__name__}: {error}"})


def run(args: argparse.Namespace) -> dict:
    if args.workers != 8 or args.size_mib != 64 or args.rounds != 64:
        raise BenchmarkError("calibration workload is frozen at 8 x 64 MiB x 64 rounds")
    if not args.output.is_absolute() or args.output.exists():
        raise BenchmarkError("calibration output must be a new absolute path")
    hardware = snapshot_hardware(strict=True)
    command_procs = os.environ.get("HIGHAMBENCH_COMMAND_CGROUP_PROCS")
    if not command_procs:
        raise BenchmarkError("calibration requires the delegated command cgroup")
    service_cgroup = lane_service_cgroup(
        Path(hardware["cgroup_v2_path"]), Path(command_procs)
    )
    ready: mp.Queue = mp.Queue()
    results: mp.Queue = mp.Queue()
    start = mp.Event()
    workers = [mp.Process(target=_worker, args=(args.size_mib, args.rounds,
                                                ready, start, results))
               for _ in range(args.workers)]
    prepared_at_utc = utc_now()
    for worker in workers:
        worker.start()
    for _ in workers:
        if ready.get(timeout=120) is not True:
            raise BenchmarkError("calibration worker failed to prepare")
    sampler = CgroupSampler(service_cgroup, interval_seconds=0.25)
    with sampler:
        begun = time.monotonic()
        start.set()
        worker_results = [results.get(timeout=180) for _ in workers]
        for worker in workers:
            worker.join(timeout=10)
        elapsed = time.monotonic() - begun
    if any(worker.exitcode != 0 for worker in workers):
        raise BenchmarkError("calibration worker exited abnormally")
    if any("error" in result for result in worker_results):
        raise BenchmarkError(f"calibration worker error: {worker_results}")
    expected_digest = worker_results[0]["sha256"]
    if any(result["sha256"] != expected_digest for result in worker_results):
        raise BenchmarkError("calibration workers produced inconsistent digests")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    trace = args.output.with_suffix(".resources.jsonl")
    summary = args.output.with_suffix(".resources.json")
    resource_summary = sampler.write(trace, summary)
    report = {
        "schema_version": "pilot-20-contention-calibration-1",
        "lane": args.lane,
        "calibration_mode": args.mode,
        "repetition": args.repetition,
        "workload": {"workers": args.workers, "size_mib_each": args.size_mib,
                     "rounds": args.rounds},
        "workload_script_sha256": sha256_file(Path(__file__)),
        "prepared_at_utc": prepared_at_utc,
        "completed_at_utc": utc_now(),
        "elapsed_seconds": elapsed,
        "worker_seconds": [result["seconds"] for result in worker_results],
        "worker_result_sha256": expected_digest,
        "hardware": hardware,
        "resources": resource_summary,
        "resource_summary_sha256": sha256_file(summary),
    }
    write_json_atomic(args.output, report, mode=0o400)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lane", choices=("A", "B", "C"), required=True)
    parser.add_argument("--mode", choices=("solo", "triple"), required=True)
    parser.add_argument("--repetition", type=int, choices=(1, 2, 3), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--size-mib", type=int, default=64)
    parser.add_argument("--rounds", type=int, default=64)
    args = parser.parse_args()
    child = launch_or_activate(Path(__file__), lane=args.lane)
    if child is not None:
        return child
    report = run(args)
    print({key: report[key] for key in ("lane", "calibration_mode", "repetition",
                                            "elapsed_seconds")})
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 20 calibration error: {error}", file=sys.stderr)
        raise SystemExit(2)
