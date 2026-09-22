#!/usr/bin/env python3
"""Qualify every Design-17 packet path without making provider calls."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import time
from typing import Any

from common import BenchmarkError, sha256_file, write_bytes_atomic, write_json_atomic
from composition_packets import build_composition_packet
from deployment import load_deployment
from design16_matched import (
    ALLOWED_EXPLORATORY_TASKS,
    _build_packet_olean_runtime,
    _contract_additions,
    _derive_signature_interface,
    _packet_exposed_records,
    _packet_treatment_allowlist,
    condition_spec,
)
from manifest_control import ROOT


SCHEMA_VERSION = "formalization-design17-preflight-1"


def _qualify_condition(
    *,
    task_id: str,
    condition: str,
    deployment: Any,
    spec: Any,
    output_root: Path,
    root_limit: int,
    dependency_limit: int,
    maximum_packet_bytes: int,
    timeout_seconds: float,
) -> dict[str, Any]:
    started = time.monotonic()
    condition_root = output_root / "tasks" / task_id / condition
    condition_root.mkdir(parents=True, mode=0o700)
    packet_path = ROOT / "packets" / f"{task_id}.json"
    additions, contract_sha256 = _contract_additions(task_id)
    retrieval, _ = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=list(spec.atlas_paths),
        corpus_id=spec.corpus_id,
        contract_additions=additions,
        root_limit=root_limit,
        dependency_limit=dependency_limit,
        maximum_markdown_bytes=maximum_packet_bytes,
    )
    interface = _derive_signature_interface(
        deployment=deployment,
        composition=retrieval,
        output_root=condition_root,
        timeout_seconds=timeout_seconds,
    )
    if condition == "R0" and interface["direct_type_declarations"]:
        raise BenchmarkError("Mathlib-only packet has NumStability type dependencies")
    canonical = {
        record["name"]: record["readable_signature"]
        for record in interface["seed_declarations"]
    }
    composition, markdown = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=list(spec.atlas_paths),
        corpus_id=spec.corpus_id,
        contract_additions=additions,
        root_limit=root_limit,
        dependency_limit=dependency_limit,
        maximum_markdown_bytes=maximum_packet_bytes,
        exposed_signature_overrides=canonical,
    )
    if (
        composition["route_status"] != retrieval["route_status"]
        or _packet_exposed_records(composition) != _packet_exposed_records(retrieval)
    ):
        raise BenchmarkError("canonical signature rendering changed packet retrieval")
    composition["retrieval_schema_version"] = composition["schema_version"]
    composition["schema_version"] = "formalization-composition-packet-2"
    composition["signature_interface"] = interface
    composition["policy"]["type_interface_rule"] = "one-hop-elaborated-types-only"
    composition["policy"]["declaration_bodies_inspected"] = False
    composition_path = condition_root / "composition-packet.json"
    markdown_path = condition_root / "LIBRARY_API.md"
    write_json_atomic(composition_path, composition, mode=0o400)
    write_bytes_atomic(markdown_path, markdown, mode=0o400)

    runtime_manifest: dict[str, Any] | None = None
    _allowed_names, selected_modules = _packet_treatment_allowlist(composition)
    if condition == "R1" and selected_modules:
        if spec.library_olean is None:
            raise BenchmarkError("R1 packet selected NumStability without an OLean tree")
        runtime_manifest = _build_packet_olean_runtime(
            composition=composition,
            source_root=deployment.library_source,
            olean_root=spec.library_olean,
            destination=condition_root / "packet-library-olean",
        )

    result = {
        "schema_version": SCHEMA_VERSION,
        "status": "PASS",
        "task_id": task_id,
        "condition": condition,
        "corpus_id": spec.corpus_id,
        "source_packet_sha256": sha256_file(packet_path),
        "contract_overlay_sha256": contract_sha256,
        "composition_packet_sha256": sha256_file(composition_path),
        "library_api_sha256": sha256_file(markdown_path),
        "signature_interface_sha256": sha256_file(
            condition_root / "signature-interface" / "interface.json"
        ),
        "seed_declaration_count": len(interface["seed_declarations"]),
        "direct_type_declaration_count": len(interface["direct_type_declarations"]),
        "allowed_declaration_count": len(interface["allowed_declarations"]),
        "selected_treatment_modules": sorted(selected_modules),
        "runtime_manifest_sha256": (
            sha256_file(condition_root / "packet-library-olean" / "runtime-manifest.json")
            if runtime_manifest is not None
            else None
        ),
        "elapsed_seconds": time.monotonic() - started,
    }
    write_json_atomic(condition_root / "preflight.json", result, mode=0o400)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--task-id", action="append", required=True)
    parser.add_argument("--root-limit", type=int, default=3)
    parser.add_argument("--dependency-limit", type=int, default=5)
    parser.add_argument("--maximum-packet-bytes", type=int, default=48 * 1024)
    parser.add_argument("--timeout-seconds", type=float, default=600.0)
    parser.add_argument("--parallelism", type=int, default=4)
    args = parser.parse_args()

    task_ids = list(dict.fromkeys(args.task_id))
    unknown = sorted(set(task_ids) - ALLOWED_EXPLORATORY_TASKS)
    if unknown:
        raise BenchmarkError(f"unsupported Design-17 task IDs: {', '.join(unknown)}")
    if not (1 <= args.parallelism <= 8):
        raise BenchmarkError("preflight parallelism must be between 1 and 8")
    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("preflight output root already exists")
    output_root.mkdir(parents=True, mode=0o700)
    deployment_path = args.deployment.expanduser().resolve()
    mathlib_atlas = args.mathlib_atlas.expanduser().resolve()
    deployment = load_deployment(deployment_path)
    specs = {
        condition: condition_spec(
            condition, deployment=deployment, mathlib_atlas=mathlib_atlas
        )
        for condition in ("R0", "R1")
    }

    started = time.monotonic()
    records: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    with ThreadPoolExecutor(max_workers=args.parallelism) as executor:
        futures = {
            executor.submit(
                _qualify_condition,
                task_id=task_id,
                condition=condition,
                deployment=deployment,
                spec=specs[condition],
                output_root=output_root,
                root_limit=args.root_limit,
                dependency_limit=args.dependency_limit,
                maximum_packet_bytes=args.maximum_packet_bytes,
                timeout_seconds=args.timeout_seconds,
            ): (task_id, condition)
            for task_id in task_ids
            for condition in ("R0", "R1")
        }
        for future in as_completed(futures):
            task_id, condition = futures[future]
            try:
                records.append(future.result())
            except Exception as error:  # preserve every independent preflight result
                failure = {
                    "task_id": task_id,
                    "condition": condition,
                    "error_type": type(error).__name__,
                    "message": str(error),
                }
                failures.append(failure)
                write_json_atomic(
                    output_root / "tasks" / task_id / condition / "incident.json",
                    {"schema_version": SCHEMA_VERSION, "status": "FAIL", **failure},
                    mode=0o400,
                )

    records.sort(key=lambda item: (item["task_id"], item["condition"]))
    failures.sort(key=lambda item: (item["task_id"], item["condition"]))
    result = {
        "schema_version": SCHEMA_VERSION,
        "status": "PASS" if not failures else "FAIL",
        "provider_calls": 0,
        "deployment_sha256": sha256_file(deployment_path),
        "mathlib_atlas_metadata_sha256": sha256_file(mathlib_atlas / "atlas.json"),
        "mathlib_atlas_declarations_sha256": sha256_file(
            mathlib_atlas / "declarations.jsonl"
        ),
        "numstability_atlas_metadata_sha256": sha256_file(
            deployment.library_atlas / "atlas.json"
        ),
        "numstability_atlas_declarations_sha256": sha256_file(
            deployment.library_atlas / "declarations.jsonl"
        ),
        "preflight_tool_sha256": sha256_file(Path(__file__)),
        "task_ids": task_ids,
        "condition_count": len(records) + len(failures),
        "parallelism": args.parallelism,
        "elapsed_seconds": time.monotonic() - started,
        "conditions": records,
        "failures": failures,
    }
    result_path = output_root / "preflight-result.json"
    write_json_atomic(result_path, result, mode=0o400)
    print(result_path)
    return 0 if not failures else 2


if __name__ == "__main__":
    raise SystemExit(main())
