#!/usr/bin/env python3
"""Compile private admission skeletons without exposing them to contestants."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from common import BenchmarkError, sha256_file, utc_now, write_json_atomic
from deployment import load_deployment
from design16_matched import condition_spec
from design18_envelope import launch_or_activate
from formalization_validator import compiled_candidate_workspace
from hardware import snapshot_hardware
from lean_sandbox import compiler_command


# The trusted compiler probe expects this specific declaration. It has no
# mathematical content and is appended only to check that each private source
# statement elaborates; it is never included in a contestant workspace.
PROBE = (b"\nnamespace HighamBenchCandidate\n"
         b"theorem target : True := by sorry\n"
         b"end HighamBenchCandidate\n")
SKELETONS = {
    "FAB19-EQ3.5": "FAB19-EQ3.5-3.7-skeleton.lean",
    "FAB19-EQ3.7": "FAB19-EQ3.5-3.7-skeleton.lean",
    "H20-8": "H20-8-attainment-skeleton.lean",
}


def run(args: argparse.Namespace) -> dict:
    if args.output_root.exists() or args.output_root.is_symlink() or not args.output_root.is_absolute():
        raise BenchmarkError("skeleton compilation output must be a new absolute directory")
    deployment = load_deployment(args.deployment)
    spec = condition_spec("R1", deployment=deployment, mathlib_atlas=args.mathlib_atlas)
    before = snapshot_hardware(strict=True)
    args.output_root.mkdir(parents=True, mode=0o700)
    report = {"schema_version": "pilot-20-private-skeleton-compile-1",
              "status": "RUNNING", "hardware_before": before,
              "deployment_sha256": sha256_file(args.deployment),
              "probe_sha256": __import__("hashlib").sha256(PROBE).hexdigest(),
              "tasks": {}, "created_at_utc": utc_now()}
    path = args.output_root / "skeleton-compilation.json"
    write_json_atomic(path, report, mode=0o400)
    try:
        for task_id, basename in SKELETONS.items():
            source = args.private_root / basename
            scratch = args.output_root / task_id / "scratch"
            scratch.mkdir(parents=True, mode=0o700)
            with compiled_candidate_workspace(
                source.read_bytes() + PROBE,
                compiler_command=compiler_command(deployment, spec.compiler_condition),
                scratch_root=scratch, timeout_seconds=600,
            ) as (_, compile_record):
                if compile_record["pass"] is not True:
                    raise BenchmarkError(f"private compatibility skeleton failed: {task_id}")
            report["tasks"][task_id] = {
                "status": "COMPILED_SORRY_STATEMENT_ONLY",
                "private_source_path": str(source),
                "private_source_sha256": sha256_file(source),
                "compile": compile_record,
            }
            write_json_atomic(path, report, mode=0o400)
    except Exception as error:
        report["status"] = "INCIDENT"
        report["incident"] = {"type": type(error).__name__, "message": str(error)}
        write_json_atomic(path, report, mode=0o400)
        raise
    report["status"] = "PASS"
    report["hardware_after"] = snapshot_hardware(strict=True)
    report["completed_at_utc"] = utc_now()
    write_json_atomic(path, report, mode=0o400)
    return report


def main() -> int:
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("deployment", "mathlib-atlas", "private-root", "output-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    result = run(parser.parse_args())
    print(json.dumps({"status": result["status"], "task_ids": list(result["tasks"])},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot-20 skeleton verification error: {error}", file=sys.stderr)
        raise SystemExit(2)
