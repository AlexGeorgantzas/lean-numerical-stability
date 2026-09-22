#!/usr/bin/env python3
"""Compile Pilot-18 controller packets/templates without a model or audit.

This is an off-benchmark infrastructure check. It may inspect only task-neutral
retrieval, elaborated declaration signatures, packet OLean closure, and the
controller-generated one-sorry template; it never creates a candidate result.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from common import BenchmarkError, sha256_file, utc_now, write_json_atomic
from composition_packets import build_composition_packet
from deployment import load_deployment
from design16_matched import (
    _build_packet_olean_runtime, _candidate_template, _derive_signature_interface,
    _packet_exposed_records, _packet_treatment_allowlist, condition_spec,
)
from design18_envelope import launch_or_activate
from design18_preflight import DESIGN_ROOT, check_corpus
from formalization_validator import compiled_candidate_workspace
from hardware import snapshot_hardware
from lean_sandbox import compiler_command


SCHEMA = "pilot-18-compile-preflight-1"


def run(*, deployment_path: Path, mathlib_atlas: Path,
        output_root: Path, task_ids: list[str]) -> dict:
    corpus, packets, flags = check_corpus()
    if not task_ids or len(set(task_ids)) != len(task_ids):
        raise BenchmarkError("compile preflight needs distinct selected task IDs")
    if set(task_ids) - set(corpus["task_ids"]):
        raise BenchmarkError("compile preflight selected an unknown task")
    if set(task_ids) & set(flags):
        raise BenchmarkError("compile preflight may not use flagged source tasks")
    if not output_root.is_absolute() or output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("compile preflight output must be a new absolute path")
    deployment = load_deployment(deployment_path)
    snapshot = snapshot_hardware(strict=True)
    specs = {key: condition_spec(key, deployment=deployment,
                                 mathlib_atlas=mathlib_atlas)
             for key in ("R0", "R1")}
    by_id = {packet["task_id"]: packet for packet in packets}
    output_root.mkdir(parents=True, mode=0o700)
    report = {
        "schema_version": SCHEMA, "status": "RUNNING",
        "task_ids": task_ids, "source_flags_excluded": flags,
        "deployment_sha256": sha256_file(deployment_path),
        "hardware_before": snapshot, "conditions": {},
        "created_at_utc": utc_now(),
    }
    report_path = output_root / "compile-preflight.json"
    write_json_atomic(report_path, report, mode=0o400)
    try:
        for task_id in task_ids:
            report["conditions"][task_id] = {}
            packet_path = DESIGN_ROOT / "packets" / f"{task_id}.json"
            packet = by_id[task_id]
            pdf_path = DESIGN_ROOT / "sources" / packet["paper_pdf"]["path_basename"]
            if sha256_file(pdf_path) != packet["paper_pdf"]["sha256"]:
                raise BenchmarkError(f"source PDF changed for {task_id}")
            for condition in ("R0", "R1"):
                spec = specs[condition]
                condition_root = output_root / task_id / condition
                condition_root.mkdir(parents=True, mode=0o700)
                raw, _ = build_composition_packet(
                    source_packet_path=packet_path,
                    atlas_paths=list(spec.atlas_paths), corpus_id=spec.corpus_id,
                    contract_additions=[], root_limit=10, dependency_limit=2,
                    maximum_markdown_bytes=64 * 1024,
                    selection_policy="component-roles-1",
                )
                interface = _derive_signature_interface(
                    deployment=deployment, composition=raw,
                    output_root=condition_root, timeout_seconds=600,
                )
                if condition == "R0" and interface["direct_type_declarations"]:
                    raise BenchmarkError("R0 signature closure has treatment declarations")
                signatures = {entry["name"]: entry["readable_signature"]
                              for entry in interface["seed_declarations"]}
                composition, api = build_composition_packet(
                    source_packet_path=packet_path,
                    atlas_paths=list(spec.atlas_paths), corpus_id=spec.corpus_id,
                    contract_additions=[], root_limit=10, dependency_limit=2,
                    maximum_markdown_bytes=64 * 1024,
                    selection_policy="component-roles-1",
                    exposed_signature_overrides=signatures,
                )
                if (composition["route_status"] != raw["route_status"]
                        or _packet_exposed_records(composition)
                        != _packet_exposed_records(raw)):
                    raise BenchmarkError("signature rendering changed selected declarations")
                _, selected_modules = _packet_treatment_allowlist(composition)
                runtime = None
                if condition == "R1" and selected_modules:
                    runtime = _build_packet_olean_runtime(
                        composition=composition,
                        source_root=deployment.library_source,
                        olean_root=deployment.library_olean,
                        destination=condition_root / "packet-library-olean",
                    )
                template = _candidate_template(composition, statement_only=True)
                if template.count("sorry") != 1:
                    raise BenchmarkError("controller template has the wrong proof-hole count")
                scratch = condition_root / "compile-scratch"
                scratch.mkdir(mode=0o700)
                with compiled_candidate_workspace(
                    template.encode("utf-8"),
                    compiler_command=compiler_command(deployment, spec.compiler_condition),
                    scratch_root=scratch, timeout_seconds=600,
                ) as (_, compile_record):
                    if compile_record.get("pass") is not True:
                        raise BenchmarkError(f"template compilation failed for {task_id}/{condition}")
                report["conditions"][task_id][condition] = {
                    "status": "PASS", "root_count": len(composition["retrieved_roots"]),
                    "route_status": composition["route_status"],
                    "component_roles": [card.get("component_role")
                                        for card in composition["retrieved_roots"]],
                    "api_bytes": len(api),
                    "packet_olean_module_count": len(runtime["files"]) if runtime else 0,
                    "signature_interface_sha256": sha256_file(
                        condition_root / "signature-interface" / "interface.json"),
                    "template_compile": compile_record,
                }
                write_json_atomic(report_path, report, mode=0o400)
    except Exception as error:
        report["status"] = "INCIDENT"
        report["incident"] = {"type": type(error).__name__, "message": str(error),
                              "recorded_at_utc": utc_now()}
        write_json_atomic(report_path, report, mode=0o400)
        raise
    report["status"] = "PASS"
    report["hardware_after"] = snapshot_hardware(strict=True)
    report["completed_at_utc"] = utc_now()
    write_json_atomic(report_path, report, mode=0o400)
    return report


def main() -> int:
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", required=True, type=Path)
    parser.add_argument("--mathlib-atlas", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    parser.add_argument("--task-id", action="append")
    args = parser.parse_args()
    corpus, _, _ = check_corpus()
    task_ids = args.task_id or corpus["early_review_order"]
    result = run(deployment_path=args.deployment,
                 mathlib_atlas=args.mathlib_atlas,
                 output_root=args.output_root, task_ids=task_ids)
    print(json.dumps({"status": result["status"], "task_ids": task_ids}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 18 compile preflight error: {error}", file=sys.stderr)
        raise SystemExit(2)
