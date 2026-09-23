#!/usr/bin/env python3
"""Run one Pilot-20 development pair with open, frozen library snapshots."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

from common import BenchmarkError, load_json, sha256_file, utc_now, write_json_atomic
from deployment import load_deployment
from design18_atlas import bind_release_atlases
from design16_matched import _condition_order, _run_condition, _statement_pair_status, condition_spec
from design18_matched import _qualified
from design20_admission import verify_admission
from hardware import snapshot_hardware


ROOT = Path(__file__).resolve().parents[1] / "design20"
CORPUS = ROOT / "CORPUS_3.json"
MODEL = "gpt-6-sol"
EFFORT = "high"
AUDIT_MODEL = "gpt-6-astra"
AUDIT_EFFORT = "high"


def run(args: argparse.Namespace) -> dict[str, Any]:
    corpus = load_json(CORPUS)
    schedule = corpus["scheduled_order"]
    task_id = args.task_id.strip().upper()
    if task_id not in schedule:
        raise BenchmarkError("task is outside the frozen Pilot-20 development schedule")
    expected = ("R0", "R1") if schedule.index(task_id) % 2 == 0 else ("R1", "R0")
    if _condition_order(args.condition_order) != expected:
        raise BenchmarkError("condition order differs from frozen schedule")
    if not args.output_root.is_absolute() or args.output_root.exists() or args.output_root.is_symlink():
        raise BenchmarkError("pair output must be a new absolute directory")
    deployment = load_deployment(args.deployment)
    deployment, mathlib_atlas = bind_release_atlases(
        deployment, mathlib=args.mathlib_atlas, numstability=args.numstability_atlas,
    )
    _qualified(
        args.model_qualification, binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        model=MODEL, effort=EFFORT,
        schema_version="pilot-20-model-qualification-1",
    )
    warm_root = args.warm_root.expanduser().resolve()
    warm = load_json(warm_root / "warm-root.json")
    if (warm.get("schema_version") != "pilot-20-warm-root-1"
            or warm.get("status") != "READY"
            or warm.get("model") != MODEL
            or warm.get("reasoning_effort") != EFFORT
            or warm.get("scout_prompt_sha256") != sha256_file(ROOT / "prompts" / "scout_compact.md")
            or warm.get("library_atlas_sha256") != sha256_file(deployment.library_atlas / "declarations.jsonl")
            or warm.get("codex_binary_sha256") != sha256_file(deployment.codex_binary)
            or warm.get("code_mode_host_sha256") != deployment.code_mode_host_sha256
            or warm.get("model_qualification_sha256") != sha256_file(args.model_qualification)):
        raise BenchmarkError("Pilot-20 warm root is incompatible")
    packet_path = ROOT / "packets" / f"{task_id}.json"
    packet = load_json(packet_path)
    if packet.get("task_id") != task_id:
        raise BenchmarkError("source packet task ID mismatch")
    paper = ROOT / "sources" / packet["paper_pdf"]["path_basename"]
    if not paper.is_file():
        paper = deployment.pdf_root / packet["paper_pdf"]["path_basename"]
    if sha256_file(paper) != packet["paper_pdf"]["sha256"]:
        raise BenchmarkError("source PDF changed")
    admission = verify_admission(task_id, packet_path=packet_path, paper=paper)
    common = (ROOT / "prompts" / "common.md").read_bytes()
    appendix = (ROOT / "prompts" / "library_appendix.md").read_bytes()
    prompts = {"R0": common, "R1": common + b"\n" + appendix}
    specs = {condition: condition_spec(condition, deployment=deployment,
                                       mathlib_atlas=mathlib_atlas)
             for condition in ("R0", "R1")}
    args.output_root.mkdir(parents=True, mode=0o700)
    pair: dict[str, Any] = {
        "schema_version": "pilot-20-development-pair-1", "status": "RUNNING",
        "task_id": task_id, "scientific_status": corpus["scientific_status"],
        "condition_order": list(expected), "model": MODEL,
        "reasoning_effort": EFFORT, "audit_model": AUDIT_MODEL,
        "audit_reasoning_effort": AUDIT_EFFORT,
        "source_packet_sha256": sha256_file(packet_path),
        "source_pdf_sha256": sha256_file(paper),
        "admission_status": admission["status"],
        "condition_prompt_sha256": {key: hashlib.sha256(value).hexdigest()
                                    for key, value in prompts.items()},
        "r1_has_exact_r0_prompt_prefix": prompts["R1"].startswith(prompts["R0"]),
        "model_qualification_sha256": sha256_file(args.model_qualification),
        "warm_root_record_sha256": sha256_file(warm_root / "warm-root.json"),
        "hardware_before": snapshot_hardware(strict=True),
        "conditions": {}, "created_at_utc": utc_now(),
    }
    write_json_atomic(args.output_root / "pair-report.json", pair, mode=0o400)
    condition_args = argparse.Namespace(
        model=MODEL, reasoning_effort=EFFORT, audit_model=AUDIT_MODEL,
        audit_reasoning_effort=AUDIT_EFFORT, audit_timeout_seconds=7200,
        audit_infrastructure_retries=2, time_limit_seconds=18000,
        validation_timeout_seconds=600, root_limit=12, dependency_limit=3,
        maximum_packet_bytes=64 * 1024, submission_limit=4,
        require_titan_envelope=True, statement_only=True,
        selection_policy="component-roles-contextual-2", library_access_policy="open-snapshot",
        sample_hardware=True, warm_root=warm_root,
        warm_root_schema_version="pilot-20-warm-root-1",
        warm_scout_prompt_path=ROOT / "prompts" / "scout_compact.md",
    )
    try:
        for condition in expected:
            pair["conditions"][condition] = _run_condition(
                args=condition_args, deployment=deployment,
                spec=specs[condition], packet_path=packet_path, packet=packet,
                contract_additions=[], paper=paper, prompt=prompts[condition],
                output_root=args.output_root,
            )
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
    r0, r1 = pair["conditions"]["R0"], pair["conditions"]["R1"]
    eligible = pair_status == "AUDITED_FAITHFUL_PAIR"
    fields = ("retrieval_wall_seconds", "contestant_active_seconds",
              "contestant_system_wall_seconds", "formalizer_wall_seconds",
              "net_new_tokens", "candidate_lines", "submission_count")
    pair["comparison"] = {
        "effect_analysis_eligible": eligible,
        "r1_over_r0": {
            field: (float(r1[field]) / float(r0[field])
                    if eligible and isinstance(r0.get(field), (int, float))
                    and isinstance(r1.get(field), (int, float)) and r0[field] > 0
                    else None)
            for field in fields
        },
        "interpretation": ("audited faithful paired comparison" if eligible
                           else "both conditions are not audited faithful; no effect ratio"),
    }
    pair["hardware_after"] = snapshot_hardware(strict=True)
    pair["completed_at_utc"] = utc_now()
    write_json_atomic(args.output_root / "pair-report.json", pair, mode=0o400)
    return pair


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("deployment", "mathlib-atlas", "numstability-atlas",
                 "model-qualification", "warm-root", "output-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--condition-order", required=True)
    pair = run(parser.parse_args())
    print(json.dumps({"task_id": pair["task_id"], "status": pair["status"],
                      "faithfulness_status": pair.get("faithfulness_status")},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot-20 matched pair error: {error}", file=sys.stderr)
        raise SystemExit(2)
