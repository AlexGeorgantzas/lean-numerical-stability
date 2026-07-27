#!/usr/bin/env python3
"""Measure the frozen HighamBench validation path without contacting a model.

This is deliberately not an agent benchmark runner.  It reuses the private
construction proofs, places each proof in a fresh isolated workspace, and runs
the same hidden Lean validator used by the benchmark.  The resulting times
measure the local benchmark machinery only.  They must never be presented as
proof-search times or as a HighamBench score.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import statistics
import sys
import time
from typing import Any


BENCHMARK_ROOT = Path(__file__).resolve().parents[1]
if str(BENCHMARK_ROOT) not in sys.path:
    sys.path.insert(0, str(BENCHMARK_ROOT))

from tools import check_construction as construction  # noqa: E402
from tools.common import (  # noqa: E402
    BenchmarkToolError,
    read_json,
    sha256_file,
    utc_now,
    write_json,
)


SCHEMA_VERSION = "highambench-offline-validation-0.1"
KIND = "offline-private-proof-validation-timing"


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--benchmark-root", type=Path, default=BENCHMARK_ROOT)
    parser.add_argument("--private-gold", type=Path, required=True)
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--packages-root", type=Path, required=True)
    parser.add_argument("--shared-olean-root", type=Path, required=True)
    parser.add_argument("--library-source", type=Path, required=True)
    parser.add_argument("--library-root-file", type=Path, required=True)
    parser.add_argument("--library-olean", type=Path, required=True)
    parser.add_argument("--hidden-parent", type=Path)
    parser.add_argument("--bwrap", type=Path, default=Path("/bin/bwrap"))
    parser.add_argument("--shared-root-relative", default="task/shared")
    parser.add_argument("--timeout-seconds", type=float, default=180.0)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--force",
        action="store_true",
        help="discard a matching partial output instead of resuming it",
    )
    return parser


def _load_fixed_identity(benchmark_root: Path) -> dict[str, Any]:
    config_path = benchmark_root / "metadata" / "config.json"
    environment_path = benchmark_root / "metadata" / "environment.json"
    release_path = benchmark_root / "metadata" / "release_files.json"
    construction_path = (
        benchmark_root / "metadata" / "evidence" / "construction_validation.json"
    )
    run_order_path = benchmark_root / "metadata" / "run_order.json"
    config = read_json(config_path)
    environment = read_json(environment_path)
    frozen = config["frozen_environment"]
    return {
        "environment_id": frozen["environment_id"],
        "environment_bundle_sha256": frozen["environment_bundle_sha256"],
        "config_sha256": sha256_file(config_path),
        "environment_record_sha256": sha256_file(environment_path),
        "release_manifest_sha256": sha256_file(release_path),
        "construction_validation_sha256": sha256_file(construction_path),
        "run_order_sha256": sha256_file(run_order_path),
        "measurement_tool_sha256": sha256_file(Path(__file__).resolve()),
        "lean_version": environment["lean"]["version"],
        "python_version": platform.python_version(),
    }


def _planned_runs(benchmark_root: Path) -> list[dict[str, str]]:
    run_order = read_json(benchmark_root / "metadata" / "run_order.json")
    planned: list[dict[str, str]] = []
    for pair in run_order["pairs"]:
        for condition in pair["condition_order"]:
            planned.append(
                {
                    "run_id": f"{pair['pair_id']}-{condition}",
                    "pair_id": pair["pair_id"],
                    "task_id": pair["task_id"],
                    "repetition_id": pair["repetition_id"],
                    "condition": condition,
                }
            )
    if len(planned) != 18 or len({row["run_id"] for row in planned}) != 18:
        raise BenchmarkToolError("the frozen run order does not contain 18 unique runs")
    return planned


def _short_validation(result: dict[str, Any]) -> dict[str, Any]:
    validation = result.get("validation") or {}
    audit = validation.get("dependency_audit") or {}
    declarations = audit.get("library_declarations") or []
    direct_names = sorted(
        {
            item["name"]
            for item in declarations
            if isinstance(item, dict)
            and item.get("distance") == 1
            and isinstance(item.get("name"), str)
        }
    )
    preflight = result.get("n_preflight")
    return {
        "pass": bool(result.get("pass")),
        "reasons": list(result.get("reasons") or []),
        "controlled_manifest_sha256": result.get("manifest_sha256"),
        "private_proof_sha256": result.get("gold_source_sha256"),
        "helper": result.get("helper"),
        "condition_n_preflight": preflight,
        "validator": {
            "pass": bool(validation.get("pass")),
            "compile_exit_code": validation.get("compile_exit_code"),
            "compile_timed_out": bool(validation.get("compile_timed_out")),
            "statement_unchanged": bool(validation.get("statement_unchanged")),
            "semantic_statement_equal": bool(
                validation.get("semantic_statement_equal")
            ),
            "controlled_before_ok": bool(validation.get("controlled_before_ok")),
            "controlled_hidden_ok": bool(validation.get("controlled_hidden_ok")),
            "controlled_after_compile_ok": bool(
                validation.get("controlled_after_compile_ok")
            ),
            "controlled_after_expected_compile_ok": bool(
                validation.get("controlled_after_expected_compile_ok")
            ),
            "controlled_after_audit_ok": bool(
                validation.get("controlled_after_audit_ok")
            ),
            "static_finding_count": validation.get("static_finding_count"),
            "failure_code": validation.get("failure_code"),
            "dependency_audit_complete": bool(audit.get("complete")),
            "dependency_audit_format": audit.get("format_version"),
            "forbidden_dependency_count": audit.get("forbidden_dependency_count"),
            "library_use": bool(audit.get("library_use")),
            "direct_library_declarations": direct_names,
            "semantic_type_check": audit.get("semantic_type_check"),
        },
    }


def _summary(runs: list[dict[str, Any]], expected: int) -> dict[str, Any]:
    by_condition: dict[str, Any] = {}
    for condition in ("N", "L"):
        rows = [row for row in runs if row["condition"] == condition]
        times = [float(row["elapsed_seconds"]) for row in rows]
        by_condition[condition] = {
            "expected": expected // 2,
            "completed": len(rows),
            "passed": sum(bool(row["result"]["pass"]) for row in rows),
            "mean_seconds": statistics.fmean(times) if times else None,
            "median_seconds": statistics.median(times) if times else None,
            "minimum_seconds": min(times) if times else None,
            "maximum_seconds": max(times) if times else None,
        }
    return {
        "expected": expected,
        "completed": len(runs),
        "passed": sum(bool(row["result"]["pass"]) for row in runs),
        "by_condition": by_condition,
    }


def _new_document(
    identity: dict[str, Any],
    basis: dict[str, Any],
    basis_seconds: float,
    expected: int,
) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "status": "in_progress",
        "started_at_utc": utc_now(),
        "completed_at_utc": None,
        "scope": {
            "paper_count": 1,
            "paper_id": "P01",
            "tasks": ["P01-T1", "P01-T2", "P01-T3"],
            "conditions": ["N", "L"],
            "repetitions_per_task_condition": 3,
            "expected_runs": expected,
        },
        "privacy": {
            "external_model_called": False,
            "authentication_read_or_copied": False,
            "network_required": False,
            "lean_subprocess_network_namespace": "unshared",
        },
        "meaning": {
            "measures": "local staging, isolated Lean compilation, statement checking, and dependency auditing time for already-written private proofs",
            "does_not_measure": "agent proof search, model tokens, model quality, or the benefit of NumStability to an agent",
            "score_policy": "These rows are not HighamBench scores and must not be inserted into the official agent result table.",
        },
        "fixed_identity": identity,
        "verification_basis_seconds": basis_seconds,
        "verification_basis": basis,
        "runs": [],
        "summary": _summary([], expected),
    }


def main() -> int:
    args = _parser().parse_args()
    if args.timeout_seconds <= 0:
        raise SystemExit("timeout must be positive")
    benchmark_root = args.benchmark_root.resolve()
    identity = _load_fixed_identity(benchmark_root)
    planned = _planned_runs(benchmark_root)
    specifications = {
        (spec.task_id, spec.condition): spec
        for spec in construction.construction_specs()
    }

    environment = construction.resolve_environment(args)
    basis_start = time.perf_counter()
    basis = construction.verification_basis(environment)
    basis_seconds = time.perf_counter() - basis_start

    document: dict[str, Any]
    if args.output.exists() and not args.force:
        document = read_json(args.output)
        if document.get("schema_version") != SCHEMA_VERSION:
            raise BenchmarkToolError("existing output has the wrong schema")
        if document.get("fixed_identity") != identity:
            raise BenchmarkToolError("existing output belongs to a different freeze")
        known = {row["run_id"] for row in document.get("runs", [])}
        allowed = {row["run_id"] for row in planned}
        if not known.issubset(allowed):
            raise BenchmarkToolError("existing output contains an unknown run")
        document["status"] = "in_progress"
        document["completed_at_utc"] = None
        document["verification_basis_seconds"] = basis_seconds
        document["verification_basis"] = basis
    else:
        document = _new_document(identity, basis, basis_seconds, len(planned))

    completed = {row["run_id"] for row in document["runs"]}
    for plan in planned:
        if plan["run_id"] in completed:
            continue
        spec = specifications[(plan["task_id"], plan["condition"])]
        print(f"starting {plan['run_id']}", flush=True)
        started_at = utc_now()
        start = time.perf_counter()
        try:
            raw_result = construction.check_one(environment, spec)
            result = _short_validation(raw_result)
        except (OSError, BenchmarkToolError, ValueError) as error:
            result = {
                "pass": False,
                "reasons": [f"offline validation could not run: {error}"],
                "validator": None,
            }
        elapsed = time.perf_counter() - start
        row = {
            **plan,
            "started_at_utc": started_at,
            "finished_at_utc": utc_now(),
            "elapsed_seconds": elapsed,
            "model_tokens": None,
            "agent_proof_search_performed": False,
            "result": result,
        }
        document["runs"].append(row)
        document["summary"] = _summary(document["runs"], len(planned))
        write_json(args.output, document)
        state = "pass" if result["pass"] else "FAIL"
        print(f"finished {plan['run_id']}: {state} in {elapsed:.3f}s", flush=True)

    document["completed_at_utc"] = utc_now()
    document["summary"] = _summary(document["runs"], len(planned))
    document["status"] = (
        "complete"
        if document["summary"]["completed"] == len(planned)
        else "incomplete"
    )
    write_json(args.output, document)
    all_passed = (
        document["status"] == "complete"
        and document["summary"]["passed"] == len(planned)
    )
    print(json.dumps(document["summary"], indent=2, sort_keys=True), flush=True)
    return 0 if all_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
