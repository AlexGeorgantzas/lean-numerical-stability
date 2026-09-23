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
import time

from common import BenchmarkError, load_json, sha256_file, utc_now, write_json_atomic
from composition_packets import build_composition_packet
from deployment import load_deployment
from design18_atlas import bind_release_atlases
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


def _proposal_packet(path: Path) -> tuple[str, dict]:
    """Resolve an unadmitted packet without modifying the measured corpus."""
    proposal_dir = DESIGN_ROOT / "proposals"
    if (path.is_symlink() or not path.is_file()
            or path.parent.resolve() != proposal_dir.resolve()):
        raise BenchmarkError("proposal packet must be a regular file in design18/proposals")
    packet = load_json(path)
    task_id = packet.get("task_id")
    if (not isinstance(task_id, str) or not task_id
            or path.name not in {f"{task_id}.json", f"{task_id}-corrected.json"}
            or packet.get("schema_version") != "formalization-source-packet-2-draft"
            or not str(packet.get("status", "")).startswith("UNADOPTED_")):
        raise BenchmarkError("proposal packet identity or status is invalid")
    if not all(isinstance(packet.get(key), list) and packet[key] for key in
               ("task_clarification", "scope_constraints", "paper_locations")):
        raise BenchmarkError("proposal packet lacks a complete source contract")
    pdf = packet.get("paper_pdf", {})
    basename = pdf.get("path_basename")
    if (not isinstance(basename, str) or Path(basename).name != basename
            or not isinstance(pdf.get("sha256"), str)):
        raise BenchmarkError("proposal PDF identity is invalid")
    pdf_path = DESIGN_ROOT / "sources" / basename
    if (pdf_path.is_symlink() or not pdf_path.is_file()
            or sha256_file(pdf_path) != pdf["sha256"]):
        raise BenchmarkError(f"proposal source PDF changed for {task_id}")
    return task_id, packet


def run(*, deployment_path: Path, mathlib_atlas: Path, numstability_atlas: Path,
        output_root: Path, task_ids: list[str],
        proposal_paths: list[Path] | None = None) -> dict:
    corpus, packets, flags = check_corpus()
    proposal_mode = bool(proposal_paths)
    if proposal_mode:
        if task_ids:
            raise BenchmarkError("proposal compile preflight cannot select corpus task IDs")
        selected = [_proposal_packet(path) for path in proposal_paths or []]
        task_ids = [task_id for task_id, _ in selected]
        packet_paths = {task_id: path for (task_id, _), path in
                        zip(selected, proposal_paths or [])}
        by_id = dict(selected)
    else:
        packet_paths = {task_id: DESIGN_ROOT / "packets" / f"{task_id}.json"
                        for task_id in task_ids}
        by_id = {packet["task_id"]: packet for packet in packets}
    if not task_ids or len(set(task_ids)) != len(task_ids):
        raise BenchmarkError("compile preflight needs distinct selected task IDs")
    if not proposal_mode and set(task_ids) - set(corpus["task_ids"]):
        raise BenchmarkError("compile preflight selected an unknown task")
    if not proposal_mode and set(task_ids) & set(flags):
        raise BenchmarkError("compile preflight may not use flagged source tasks")
    if not output_root.is_absolute() or output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("compile preflight output must be a new absolute path")
    deployment = load_deployment(deployment_path)
    deployment, mathlib_atlas = bind_release_atlases(
        deployment, mathlib=mathlib_atlas, numstability=numstability_atlas,
    )
    snapshot = snapshot_hardware(strict=True)
    specs = {key: condition_spec(key, deployment=deployment,
                                 mathlib_atlas=mathlib_atlas)
             for key in ("R0", "R1")}
    output_root.mkdir(parents=True, mode=0o700)
    report = {
        "schema_version": SCHEMA, "status": "RUNNING",
        "mode": "UNADOPTED_PROPOSAL_STATIC_ONLY" if proposal_mode else "CORPUS_STATIC_ONLY",
        "task_ids": task_ids, "source_flags_excluded": flags,
        "proposal_packet_sha256": {task_id: sha256_file(packet_paths[task_id])
                                   for task_id in task_ids} if proposal_mode else {},
        "deployment_sha256": sha256_file(deployment_path),
        "hardware_before": snapshot, "conditions": {},
        "created_at_utc": utc_now(),
    }
    report_path = output_root / "compile-preflight.json"
    write_json_atomic(report_path, report, mode=0o400)
    try:
        for task_id in task_ids:
            report["conditions"][task_id] = {}
            packet_path = packet_paths[task_id]
            packet = by_id[task_id]
            pdf_path = DESIGN_ROOT / "sources" / packet["paper_pdf"]["path_basename"]
            if sha256_file(pdf_path) != packet["paper_pdf"]["sha256"]:
                raise BenchmarkError(f"source PDF changed for {task_id}")
            for condition in ("R0", "R1"):
                condition_started = time.monotonic()
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
                if template.count("\n  sorry\n") != 1:
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
                    "preflight_wall_seconds": time.monotonic() - condition_started,
                }
                write_json_atomic(report_path, report, mode=0o400)
    except Exception as error:
        report["status"] = "INCIDENT"
        report["incident"] = {"type": type(error).__name__, "message": str(error),
                              "recorded_at_utc": utc_now()}
        write_json_atomic(report_path, report, mode=0o400)
        raise
    report["status"] = "PASS_PROPOSAL_STATIC_ONLY" if proposal_mode else "PASS"
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
    parser.add_argument("--numstability-atlas", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    parser.add_argument("--task-id", action="append")
    parser.add_argument("--proposal-packet", action="append", type=Path,
                        help="unadmitted source proposal; cannot be used by the measured runner")
    args = parser.parse_args()
    corpus, _, _ = check_corpus()
    if args.proposal_packet and args.task_id:
        raise BenchmarkError("--proposal-packet and --task-id are mutually exclusive")
    task_ids = [] if args.proposal_packet else (args.task_id or corpus["early_review_order"])
    result = run(deployment_path=args.deployment,
                 mathlib_atlas=args.mathlib_atlas,
                 numstability_atlas=args.numstability_atlas,
                 output_root=args.output_root, task_ids=task_ids,
                 proposal_paths=args.proposal_packet)
    print(json.dumps({"status": result["status"], "task_ids": result["task_ids"]},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 18 compile preflight error: {error}", file=sys.stderr)
        raise SystemExit(2)
