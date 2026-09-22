#!/usr/bin/env python3
"""Run one audited Pilot-18 statement pair after all admission gates pass.

This reuses the validated Design-17 compiler/audit/repair machinery but has a
new source corpus, component router, model qualification, and warm R1 fork.
It cannot be run against today's draft corpus with unresolved source flags.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

from common import BenchmarkError, load_json, sha256_file, utc_now, write_json_atomic
from deployment import load_deployment
from design16_matched import (
    _condition_order, _run_condition, _statement_pair_status, condition_spec,
)
from design18_preflight import DESIGN_ROOT, check_corpus
from hardware import snapshot_hardware


MODEL = "gpt-6-sol"
EFFORT = "xhigh"
AUDIT_MODEL = "gpt-6-astra"
AUDIT_EFFORT = "high"


def _qualified(path: Path, *, binary: Path, code_mode_host_sha256: str) -> dict:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError("Pilot 18 model qualification is missing or unsafe")
    record = load_json(path)
    if (record.get("schema_version") != "pilot-18-model-qualification-1"
            or record.get("status") != "PASS"
            or record.get("model") != MODEL
            or record.get("reasoning_effort") != EFFORT
            or record.get("codex_binary_sha256") != sha256_file(binary)
            or record.get("code_mode_host_sha256") != code_mode_host_sha256
            or record.get("usage_complete") is not True):
        raise BenchmarkError("GPT-6 Sol provider is not qualified for this Titan runtime")
    return record


def run(args: argparse.Namespace) -> dict[str, Any]:
    corpus, packets, flags = check_corpus()
    if flags:
        raise BenchmarkError(f"source flags bar measured Pilot 18 runs: {flags}")
    task_id = args.task_id.strip().upper()
    if task_id not in corpus["scheduled_order"]:
        raise BenchmarkError("task is outside the Pilot 18 schedule")
    expected_order = ("R0", "R1") if corpus["scheduled_order"].index(task_id) % 2 == 0 else ("R1", "R0")
    if _condition_order(args.condition_order) != expected_order:
        raise BenchmarkError(f"condition order is frozen as {','.join(expected_order)}")
    if not args.output_root.is_absolute():
        raise BenchmarkError("Pilot 18 pair output must be an absolute path")
    if args.output_root.exists() or args.output_root.is_symlink():
        raise BenchmarkError("Pilot 18 pair output already exists")
    deployment = load_deployment(args.deployment)
    qualification = _qualified(
        args.model_qualification, binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
    )
    warm_root = args.warm_root.expanduser().resolve()
    warm = load_json(warm_root / "warm-root.json")
    if (warm.get("schema_version") != "pilot-18-warm-root-1"
            or warm.get("status") != "READY"
            or warm.get("model") != MODEL
            or warm.get("reasoning_effort") != EFFORT
            or warm.get("scout_prompt_sha256") != sha256_file(DESIGN_ROOT / "prompts" / "scout.md")
            or warm.get("library_atlas_sha256") != sha256_file(deployment.library_atlas / "declarations.jsonl")
            or warm.get("codex_binary_sha256") != sha256_file(deployment.codex_binary)
            or warm.get("code_mode_host_sha256") != deployment.code_mode_host_sha256):
        raise BenchmarkError("Pilot 18 warm scout is not ready")
    packet_path = DESIGN_ROOT / "packets" / f"{task_id}.json"
    packet = next(item for item in packets if item["task_id"] == task_id)
    paper = DESIGN_ROOT / "sources" / packet["paper_pdf"]["path_basename"]
    if sha256_file(paper) != packet["paper_pdf"]["sha256"]:
        raise BenchmarkError("Pilot 18 source PDF changed")
    common = (DESIGN_ROOT / "prompts" / "common.md").read_bytes()
    appendix = (DESIGN_ROOT / "prompts" / "library_appendix.md").read_bytes()
    prompts = {"R0": common, "R1": common + appendix}
    specs = {condition: condition_spec(condition, deployment=deployment,
                                       mathlib_atlas=args.mathlib_atlas)
             for condition in ("R0", "R1")}
    hardware = snapshot_hardware(strict=True)
    args.output_root.mkdir(parents=True, mode=0o700)
    pair: dict[str, Any] = {
        "schema_version": "pilot-18-matched-pair-1",
        "status": "RUNNING", "task_id": task_id,
        "scientific_status": "EXPLORATORY_UNTIL_CORPUS_AND_CONTROLLER_FROZEN",
        "condition_order": list(expected_order),
        "model": MODEL, "reasoning_effort": EFFORT,
        "audit_model": AUDIT_MODEL, "audit_reasoning_effort": AUDIT_EFFORT,
        "source_packet_sha256": sha256_file(packet_path),
        "source_pdf_sha256": sha256_file(paper),
        "condition_prompt_sha256": {key: hashlib.sha256(value).hexdigest()
                                    for key, value in prompts.items()},
        "r1_has_exact_r0_prompt_prefix": prompts["R1"].startswith(prompts["R0"]),
        "model_qualification_sha256": sha256_file(args.model_qualification),
        "warm_root_record_sha256": sha256_file(warm_root / "warm-root.json"),
        "hardware_before": hardware,
        "conditions": {}, "created_at_utc": utc_now(),
    }
    write_json_atomic(args.output_root / "pair-report.json", pair, mode=0o400)
    condition_args = argparse.Namespace(
        model=MODEL, reasoning_effort=EFFORT, audit_model=AUDIT_MODEL,
        audit_reasoning_effort=AUDIT_EFFORT, audit_timeout_seconds=7200,
        audit_infrastructure_retries=2, time_limit_seconds=18000,
        validation_timeout_seconds=600, root_limit=10, dependency_limit=2,
        maximum_packet_bytes=64 * 1024, submission_limit=4,
        require_titan_envelope=True, statement_only=True,
        selection_policy="component-roles-1", warm_root=warm_root,
        warm_scout_prompt_path=DESIGN_ROOT / "prompts" / "scout.md",
    )
    try:
        for condition in expected_order:
            report = _run_condition(
                args=condition_args, deployment=deployment,
                spec=specs[condition], packet_path=packet_path, packet=packet,
                contract_additions=[], paper=paper,
                prompt=prompts[condition], output_root=args.output_root,
            )
            pair["conditions"][condition] = report
            write_json_atomic(args.output_root / "pair-report.json", pair, mode=0o400)
    except Exception as error:
        pair["status"] = "PAIR_INCIDENT"
        pair["incident"] = {"type": type(error).__name__, "message": str(error),
                            "recorded_at_utc": utc_now()}
        write_json_atomic(args.output_root / "pair-report.json", pair, mode=0o400)
        raise
    pair_status, faithful_status = _statement_pair_status(
        pair["conditions"]["R0"]["result_status"],
        pair["conditions"]["R1"]["result_status"],
    )
    pair["status"] = pair_status
    pair["faithfulness_status"] = faithful_status
    r0 = pair["conditions"]["R0"]
    r1 = pair["conditions"]["R1"]
    eligible = pair_status == "AUDITED_FAITHFUL_PAIR"
    fields = (
        "retrieval_wall_seconds", "contestant_active_seconds",
        "contestant_system_wall_seconds", "formalizer_wall_seconds",
        "net_new_tokens", "candidate_lines", "submission_count",
    )
    pair["comparison"] = {
        "effect_analysis_eligible": eligible,
        "r1_over_r0": {
            field: (float(r1[field]) / float(r0[field])
                    if eligible and isinstance(r0.get(field), (int, float))
                    and isinstance(r1.get(field), (int, float)) and r0[field] > 0
                    else None)
            for field in fields
        },
        "interpretation": (
            "audited faithful paired comparison" if eligible
            else "both conditions are not audited faithful; no effect ratio"
        ),
    }
    pair["hardware_after"] = snapshot_hardware(strict=True)
    pair["completed_at_utc"] = utc_now()
    write_json_atomic(args.output_root / "pair-report.json", pair, mode=0o400)
    return pair


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", required=True, type=Path)
    parser.add_argument("--mathlib-atlas", required=True, type=Path)
    parser.add_argument("--model-qualification", required=True, type=Path)
    parser.add_argument("--warm-root", required=True, type=Path)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--condition-order", required=True)
    parser.add_argument("--output-root", required=True, type=Path)
    args = parser.parse_args()
    pair = run(args)
    print(json.dumps({"task_id": pair["task_id"], "status": pair["status"],
                      "faithfulness_status": pair.get("faithfulness_status")},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 18 matched error: {error}", file=sys.stderr)
        raise SystemExit(2)
