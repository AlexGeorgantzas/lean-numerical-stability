#!/usr/bin/env python3
"""Run the canonical multi-role faithfulness audit for one Design-16 candidate.

The candidate condition is used only to select the correct Lean compilation
environment while constructing the blinded semantic dossier.  The fresh blind
translation, direct, round-trip, and conditional adjudication roles never see
the condition, attempt number, proof text, retrieval packet, or performance
telemetry.  Auditor time and tokens are recorded separately and excluded from
contestant measurements.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

from audit_controller import AuditController
from common import BenchmarkError, sha256_file, write_json_atomic
from deployment import load_deployment
from lean_sandbox import compiler_command, extractor_command
from prepare_candidate_audit import CandidateAuditError, prepare_candidate_audit


SCIENTIFIC_STATUS = "CANONICAL_MULTI_ROLE_FAITHFULNESS_AUDIT"


def run_cli(args: argparse.Namespace) -> dict[str, Any]:
    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("Design-16 full-audit output root must not already exist")
    output_root.mkdir(parents=True, mode=0o700)

    deployment = load_deployment(args.deployment)
    candidate = args.candidate.expanduser().resolve()
    paper = args.paper.expanduser().resolve()
    source_packet = args.source_packet.expanduser().resolve()
    condition = args.condition.upper()
    if condition not in {"N", "L"}:
        raise BenchmarkError("Design-16 full-audit condition must be N or L")
    for path, label in (
        (candidate, "candidate"),
        (paper, "paper"),
        (source_packet, "source packet"),
    ):
        if not path.is_file() or path.is_symlink():
            raise BenchmarkError(f"Design-16 full-audit {label} is missing or unsafe")

    preparation_root = output_root / "preparation"
    preparation_root.mkdir(mode=0o700)
    scratch = preparation_root / "scratch"
    scratch.mkdir(mode=0o700)
    helper = Path(__file__).with_name("declaration_dossier.lean")
    blind, private = prepare_candidate_audit(
        candidate,
        compiler_command=compiler_command(deployment, condition),
        extractor_command=extractor_command(deployment, condition, helper),
        compiler_environment={},
        extractor_environment={},
        scratch_root=scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
        allow_single_target_sorry=bool(args.statement_only),
    )
    dossier_path = preparation_root / "blind_semantic_dossier.json"
    private_path = preparation_root / "private_semantic_manifest.json"
    write_json_atomic(private_path, private, mode=0o400)
    write_json_atomic(dossier_path, blind, mode=0o400)
    semantic_sha256 = blind.get("semantic_sha256")
    if (
        not isinstance(semantic_sha256, str)
        or private.get("blind_semantic_sha256") != semantic_sha256
    ):
        raise BenchmarkError("Design-16 full-audit dossier hash contract failed")

    controller = AuditController(
        codex_binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        auth_file=deployment.auth_file,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        timeout_seconds=float(args.timeout_seconds),
        maximum_infrastructure_retries=int(args.infrastructure_retries),
        bwrap_binary=deployment.bwrap_binary,
        offline_shell=deployment.offline_shell,
        toolchain_root=deployment.toolchain_root,
        packages_root=deployment.packages_root,
    )
    decision = controller.run(
        task_id=args.task_id,
        paper_path=paper,
        paper_sha256=sha256_file(paper),
        source_packet=source_packet,
        dossier_path=dossier_path,
        semantic_sha256=semantic_sha256,
        audit_root=output_root / "audit",
    )
    result = {
        "schema_version": "formalization-design16-full-audit-run-1",
        "scientific_status": SCIENTIFIC_STATUS,
        "task_id": args.task_id,
        "candidate_sha256": private["candidate"]["sha256"],
        "source_packet_sha256": sha256_file(source_packet),
        "paper_sha256": sha256_file(paper),
        "candidate_semantic_sha256": semantic_sha256,
        "blind_dossier_sha256": sha256_file(dossier_path),
        "private_manifest_sha256": sha256_file(private_path),
        "decision": decision,
        "auditor_tokens_excluded_from_benchmark": True,
        "condition_blind": True,
        "attempt_blind": True,
        "source_contract": (
            "statement-only-single-target-sorry"
            if args.statement_only
            else "complete-kernel-checked-proof"
        ),
        "output_root": str(output_root),
    }
    write_json_atomic(output_root / "result.json", result, mode=0o400)
    return result


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--paper", type=Path, required=True)
    parser.add_argument("--source-packet", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--condition", choices=("N", "L", "n", "l"), required=True)
    parser.add_argument("--model", default="gpt-6-astra")
    parser.add_argument("--reasoning-effort", default="high")
    parser.add_argument("--timeout-seconds", type=float, default=7200)
    parser.add_argument("--validation-timeout-seconds", type=float, default=600)
    parser.add_argument(
        "--statement-only",
        action="store_true",
        help="audit a candidate whose final target proof is exactly one permitted sorry",
    )
    parser.add_argument(
        "--infrastructure-retries",
        type=int,
        default=2,
        help="fresh retries after malformed/infrastructure output (default: two)",
    )
    return parser


def main() -> int:
    try:
        result = run_cli(make_parser().parse_args())
    except CandidateAuditError as error:
        print(
            f"Design-16 full-audit dossier failed ({error.failure_code}): {error}",
            file=sys.stderr,
        )
        return 1 if error.failure_code in {"RULE_VIOLATION", "COMPILATION_FAILURE"} else 2
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Design-16 full-audit error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
