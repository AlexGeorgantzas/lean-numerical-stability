#!/usr/bin/env python3
"""Qualify the Design-17 H5-5 signature interface against frozen OLean files."""

from __future__ import annotations

import argparse
from pathlib import Path

from common import BenchmarkError, sha256_file, write_json_atomic
from composition_packets import build_composition_packet
from deployment import load_deployment
from design16_matched import (
    _build_packet_olean_runtime,
    _derive_signature_interface,
    _packet_exposed_records,
    condition_spec,
)
from manifest_control import ROOT


EXPECTED_SEEDS = frozenset(
    {
        "NumStability.fl_rootProductEvalFrom_forward_error_bound",
        "NumStability.fl_rootProductEval_forward_error_bound",
        "NumStability.Ch14RectProductTree.roundedEval_RectMatProdError_gamma_operationBudget",
        "NumStability.fl_rootProductEvalFrom",
        "NumStability.rootProductEvalFrom",
        "NumStability.fl_rootProductEval",
        "NumStability.rootProductEval",
        "NumStability.gammaValid_mono",
        "NumStability.gamma_mono",
        "NumStability.gamma_nonneg",
        "NumStability.Ch14RectProductTree.RectMatProdError",
        "NumStability.Ch14RectProductTree.operationBudget",
    }
)
EXPECTED_DIRECT = frozenset(
    {
        "NumStability.FPModel",
        "NumStability.gamma",
        "NumStability.gammaValid",
        "NumStability.Ch14RectProductTree",
        "NumStability.Ch14RectProductTree.exactAbsProduct",
        "NumStability.Ch14RectProductTree.exactEval",
        "NumStability.Ch14RectProductTree.roundedEval",
    }
)
FORBIDDEN_NEIGHBORS = frozenset(
    {
        "NumStability.FPModel.fl_mul",
        "NumStability.FPModel.fl_sub",
        "NumStability.Ch14RectProductTree.orderCoefficient",
        "NumStability.rectMatMul",
    }
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=float, default=300.0)
    args = parser.parse_args()

    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("qualification output root already exists")
    output_root.mkdir(parents=True, mode=0o700)
    deployment = load_deployment(args.deployment)
    spec = condition_spec(
        "R1", deployment=deployment, mathlib_atlas=args.mathlib_atlas
    )
    packet_path = ROOT / "packets" / "H5-5.json"
    composition, _ = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=list(spec.atlas_paths),
        corpus_id=spec.corpus_id,
        root_limit=3,
        dependency_limit=5,
        maximum_markdown_bytes=48 * 1024,
    )
    interface = _derive_signature_interface(
        deployment=deployment,
        composition=composition,
        output_root=output_root,
        timeout_seconds=args.timeout_seconds,
    )
    observed_seeds = frozenset(
        record["name"] for record in interface["seed_declarations"]
    )
    observed_direct = frozenset(
        record["name"] for record in interface["direct_type_declarations"]
    )
    if observed_seeds != EXPECTED_SEEDS:
        raise BenchmarkError("H5-5 frozen-OLean seed surface does not match the golden set")
    if observed_direct - observed_seeds != EXPECTED_DIRECT:
        raise BenchmarkError("H5-5 frozen-OLean one-hop surface does not match the golden set")
    expected_allowed = EXPECTED_SEEDS | EXPECTED_DIRECT
    if frozenset(interface["allowed_declarations"]) != expected_allowed:
        raise BenchmarkError("H5-5 frozen-OLean allowlist is not the exact 19-name golden")
    if FORBIDDEN_NEIGHBORS & expected_allowed:
        raise BenchmarkError("H5-5 signature interface admitted a forbidden neighbor")
    rendered = "\n".join(
        str(record["readable_signature"])
        for record in interface["seed_declarations"]
    )
    for required in ("2 * roots.length", " - ", "≤"):
        if required not in rendered:
            raise BenchmarkError(
                f"H5-5 canonical signature rendering lacks normal notation: {required!r}"
            )
    for forbidden in (
        "instHMul.hMul",
        "instHSub.hSub",
        "Real.instLE.le",
        "instOfNat",
    ):
        if forbidden in rendered:
            raise BenchmarkError(
                f"H5-5 canonical signature rendering exposes internal notation: {forbidden}"
            )

    composition = dict(composition)
    composition["signature_interface"] = interface
    runtime = _build_packet_olean_runtime(
        composition=composition,
        source_root=deployment.library_source,
        olean_root=deployment.library_olean,
        destination=output_root / "packet-library-olean",
    )
    result = {
        "schema_version": "formalization-design17-signature-qualification-1",
        "status": "PASS",
        "task_id": "H5-5",
        "deployment_sha256": sha256_file(args.deployment.expanduser().resolve()),
        "mathlib_atlas": str(args.mathlib_atlas.expanduser().resolve()),
        "packet_records": _packet_exposed_records(composition),
        "expected_seed_declarations": sorted(EXPECTED_SEEDS),
        "expected_direct_type_declarations": sorted(EXPECTED_DIRECT),
        "observed_raw_direct_type_declarations": sorted(observed_direct),
        "forbidden_neighbors": sorted(FORBIDDEN_NEIGHBORS),
        "signature_interface": interface,
        "runtime_manifest": runtime,
    }
    write_json_atomic(output_root / "qualification.json", result, mode=0o400)
    print(output_root / "qualification.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
