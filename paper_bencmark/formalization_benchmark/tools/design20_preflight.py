#!/usr/bin/env python3
"""Off-benchmark static packet, mount, and compiler preflight for Pilot 20."""

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
from design16_matched import (_candidate_template, _derive_signature_interface,
                              _packet_exposed_records, condition_spec)
from design20_matched import CORPUS, ROOT
from design18_envelope import launch_or_activate
from formalization_validator import compiled_candidate_workspace
from hardware import snapshot_hardware
from lean_sandbox import compiler_command


def run(args: argparse.Namespace) -> dict:
    if not args.output_root.is_absolute() or args.output_root.exists() or args.output_root.is_symlink():
        raise BenchmarkError("preflight output must be a new absolute directory")
    corpus = load_json(CORPUS)
    deployment = load_deployment(args.deployment)
    deployment, mathlib_atlas = bind_release_atlases(
        deployment, mathlib=args.mathlib_atlas, numstability=args.numstability_atlas,
    )
    specs = {key: condition_spec(key, deployment=deployment,
                                 mathlib_atlas=mathlib_atlas)
             for key in ("R0", "R1")}
    args.output_root.mkdir(parents=True, mode=0o700)
    report = {"schema_version": "pilot-20-static-preflight-1", "status": "RUNNING",
              "tasks": {}, "corpus_sha256": sha256_file(CORPUS),
              "hardware_before": snapshot_hardware(strict=True),
              "created_at_utc": utc_now()}
    report_path = args.output_root / "preflight.json"
    write_json_atomic(report_path, report, mode=0o400)
    try:
        for task_id in corpus["scheduled_order"]:
            packet_path = ROOT / "packets" / f"{task_id}.json"
            packet = load_json(packet_path)
            if packet.get("task_id") != task_id:
                raise BenchmarkError(f"packet identity mismatch: {task_id}")
            pdf = ROOT / "sources" / packet["paper_pdf"]["path_basename"]
            if not pdf.is_file():
                pdf = deployment.pdf_root / packet["paper_pdf"]["path_basename"]
            if sha256_file(pdf) != packet["paper_pdf"]["sha256"]:
                raise BenchmarkError(f"source PDF mismatch: {task_id}")
            report["tasks"][task_id] = {}
            for condition, spec in specs.items():
                started = time.monotonic()
                root = args.output_root / task_id / condition
                root.mkdir(parents=True, mode=0o700)
                raw, _ = build_composition_packet(
                    source_packet_path=packet_path,
                    atlas_paths=list(spec.atlas_paths), corpus_id=spec.corpus_id,
                    contract_additions=[], root_limit=12, dependency_limit=3,
                    maximum_markdown_bytes=64 * 1024,
                    selection_policy="component-roles-1", open_library_access=True,
                )
                interface = _derive_signature_interface(
                    deployment=deployment, composition=raw,
                    output_root=root, timeout_seconds=600,
                )
                if condition == "R0" and interface["direct_type_declarations"]:
                    raise BenchmarkError("N packet carries NumStability type dependencies")
                signatures = {item["name"]: item["readable_signature"]
                              for item in interface["seed_declarations"]}
                composition, api = build_composition_packet(
                    source_packet_path=packet_path,
                    atlas_paths=list(spec.atlas_paths), corpus_id=spec.corpus_id,
                    contract_additions=[], root_limit=12, dependency_limit=3,
                    maximum_markdown_bytes=64 * 1024,
                    exposed_signature_overrides=signatures,
                    selection_policy="component-roles-1", open_library_access=True,
                )
                if (composition["route_status"] != raw["route_status"]
                        or _packet_exposed_records(composition)
                        != _packet_exposed_records(raw)):
                    raise BenchmarkError("signature rendering changed retrieval")
                template = _candidate_template(composition, statement_only=True)
                scratch = root / "compile-scratch"
                scratch.mkdir(mode=0o700)
                with compiled_candidate_workspace(
                    template.encode("utf-8"),
                    compiler_command=compiler_command(deployment, spec.compiler_condition),
                    scratch_root=scratch, timeout_seconds=600,
                ) as (_, compile_record):
                    if compile_record.get("pass") is not True:
                        raise BenchmarkError(f"template compile failed: {task_id}/{condition}")
                report["tasks"][task_id][condition] = {
                    "status": "PASS", "route_status": composition["route_status"],
                    "selected_roots": [item["declaration"]["name"]
                                       for item in composition["retrieved_roots"]],
                    "packet_bytes": len(api),
                    "signature_interface_sha256": sha256_file(
                        root / "signature-interface" / "interface.json"),
                    "template_compile": compile_record,
                    "wall_seconds": time.monotonic() - started,
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
    for name in ("deployment", "mathlib-atlas", "numstability-atlas", "output-root"):
        parser.add_argument("--" + name, required=True, type=Path)
    report = run(parser.parse_args())
    print(json.dumps({"status": report["status"], "task_ids": list(report["tasks"])},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot-20 preflight error: {error}", file=sys.stderr)
        raise SystemExit(2)
