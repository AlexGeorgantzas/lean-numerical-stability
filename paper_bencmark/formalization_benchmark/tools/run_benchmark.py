#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

from common import BenchmarkError, sha256_file
from deployment import load_deployment
from evaluation_gate import evaluate_gate
from manifest_control import verify_manifest
from pair_controller import PairController


TASK_IDS = (
    "H00-00",
    "P01-T2", "P02-T2", "P03-T2", "P13-T2", "P14-T2",
    "H22-11", "H22-5", "H20-6", "H7-12", "H20-9", "H20-8",
    "H23-6", "H5-5", "H10-7", "H12-4", "H19-5", "H7-14", "H15-3",
)


def normalized_task_id(value: str) -> str:
    rendered = value.strip().upper().replace("_", "-")
    if rendered not in TASK_IDS:
        raise argparse.ArgumentTypeError(
            "task must be one of the 19 task IDs frozen in pilot-15"
        )
    return rendered


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run exactly one source-first HighamBench N/L formalization pair."
    )
    parser.add_argument("--deployment", type=Path)
    parser.add_argument(
        "--development-no-hardware-enforcement",
        action="store_true",
        help="provider-free local development only; results are never measurement-admissible",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name in ("doctor", "status", "qualify-provider"):
        child = subparsers.add_parser(name)
        child.add_argument("--task-id", required=True, type=normalized_task_id)
    run = subparsers.add_parser("run")
    run.add_argument("--task-id", required=True, type=normalized_task_id)
    run.add_argument(
        "--dry-run",
        action="store_true",
        help="stage and authenticate the pair without provider calls",
    )
    subparsers.add_parser("verify-release")
    subparsers.add_parser("prepare-warm-root")
    subparsers.add_parser("evaluate-gate")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    if args.command == "verify-release":
        manifest, config = verify_manifest()
        print(
            json.dumps(
                {
                    "status": "verified",
                    "pilot_id": config["pilot_id"],
                    "task_ids": config["task_ids"],
                    "manifest_payload_sha256": manifest["manifest_payload_sha256"],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    deployment = load_deployment(args.deployment)
    bound_path = os.environ.get("HIGHAMBENCH_FORMALIZATION_DEPLOYMENT")
    bound_sha256 = os.environ.get("HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256")
    if bound_path:
        expected_path = Path(bound_path).expanduser().resolve()
        if deployment.path != expected_path:
            raise BenchmarkError("deployment override does not match the installed launcher")
    if bound_sha256:
        if len(bound_sha256) != 64 or sha256_file(deployment.path) != bound_sha256:
            raise BenchmarkError("deployment record does not match the installed launcher")
    controller = PairController(
        deployment,
        allow_unenforced_hardware=args.development_no_hardware_enforcement,
    )
    if args.command == "evaluate-gate":
        result = evaluate_gate(controller, controller.config)
    elif args.command == "prepare-warm-root":
        if (
            args.development_no_hardware_enforcement
            or not deployment.strict_hardware
            or os.environ.get("HIGHAMBENCH_TITAN_ENVELOPE") != "1"
            or not bound_path
            or not bound_sha256
        ):
            raise BenchmarkError(
                "warm-root preparation requires the digest-bound strict Titan launcher"
            )
        result = controller.prepare_warm_root_when_idle()
    elif args.command == "doctor":
        result = controller.doctor_when_idle(args.task_id)
    elif args.command == "status":
        result = controller.status(args.task_id)
    elif args.command == "qualify-provider":
        if (
            args.development_no_hardware_enforcement
            or not deployment.strict_hardware
            or os.environ.get("HIGHAMBENCH_TITAN_ENVELOPE") != "1"
            or not bound_path
            or not bound_sha256
        ):
            raise BenchmarkError(
                "provider qualification requires the digest-bound strict Titan launcher"
            )
        result = controller.qualify_provider_when_idle(args.task_id)
    else:
        if args.development_no_hardware_enforcement and not args.dry_run:
            raise BenchmarkError(
                "unenforced hardware is permitted only with provider-free --dry-run"
            )
        if not args.dry_run and not deployment.strict_hardware:
            raise BenchmarkError(
                "official measured runs require a strict-hardware deployment"
            )
        if not args.dry_run and (
            os.environ.get("HIGHAMBENCH_TITAN_ENVELOPE") != "1"
            or not bound_path
            or not bound_sha256
        ):
            raise BenchmarkError(
                "official measured runs require the installed digest-bound Titan launcher"
            )
        result = controller.run(args.task_id, dry_run=args.dry_run)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"formalization benchmark error: {error}", file=sys.stderr)
        raise SystemExit(2)
