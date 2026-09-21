#!/usr/bin/env python3
"""Run one explicitly unscored matched Design-16 exploratory pair.

R0 indexes Mathlib only and exposes only Mathlib OLean files. R1 runs the same
deterministic retriever over Mathlib plus the frozen NumStability atlas and
additionally exposes the frozen NumStability OLean tree. Each condition starts
a fresh, stateless formalizer. Conditions run sequentially so timed contestants
never contend on the same host.

This tool is engineering infrastructure, not an official pilot controller. It
does not perform a faithfulness audit and labels every result accordingly.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
from typing import Any

from codex_driver import CodexDriver
from common import (
    BenchmarkError,
    load_json,
    sha256_file,
    utc_now,
    write_bytes_atomic,
    write_json_atomic,
)
from composition_packets import build_composition_packet
from deployment import Deployment, load_deployment
from design16_smoke import _net_new, _routed_candidate_template
from formalization_validator import compiled_candidate_workspace, validate_candidate
from lean_sandbox import compiler_command
from manifest_control import ROOT
from pair_controller import _environment_note, _task_packet_markdown
from hardware import snapshot_hardware


SCIENTIFIC_STATUS = "UNSCORED_ENGINEERING_EXPLORATORY"
CONDITIONS = ("R0", "R1")
ALLOWED_EXPLORATORY_TASKS = frozenset(
    {
        "H5-5",
        "H7-12",
        "H7-14",
        "H10-7",
        "H12-4",
        "H15-3",
        "H19-5",
        "H20-6",
        "H20-8",
        "H20-9",
        "H22-5",
        "H22-11",
        "H23-6",
    }
)


@dataclass(frozen=True)
class ConditionSpec:
    name: str
    corpus_id: str
    atlas_paths: tuple[Path, ...]
    compiler_condition: str
    library_olean: Path | None


def _atlas_declarations(atlas_root: Path, *, label: str) -> Path:
    expanded = atlas_root.expanduser()
    if expanded.is_symlink():
        raise BenchmarkError(f"{label} atlas may not be a symlink: {expanded}")
    root = expanded.resolve()
    declarations = root / "declarations.jsonl"
    metadata_path = root / "atlas.json"
    if (
        not root.is_dir()
        or root.is_symlink()
        or not declarations.is_file()
        or declarations.is_symlink()
        or not metadata_path.is_file()
        or metadata_path.is_symlink()
    ):
        raise BenchmarkError(f"{label} atlas is missing or unsafe: {root}")
    metadata = load_json(metadata_path)
    if (
        metadata.get("schema_version") != "numstability-library-atlas-2"
        or metadata.get("declarations_sha256") != sha256_file(declarations)
        or not isinstance(metadata.get("declaration_count"), int)
        or metadata["declaration_count"] < 1
    ):
        raise BenchmarkError(f"{label} atlas identity is malformed or stale")
    return declarations


def _classify_atlas(path: Path, *, expect_numstability: bool) -> None:
    """Reject accidental treatment leakage or a bogus treatment atlas."""

    records = 0
    numstability_modules = 0
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise BenchmarkError(f"malformed atlas JSON at {path}:{line_number}") from error
        module = record.get("module") if isinstance(record, dict) else None
        if not isinstance(module, str) or not module:
            raise BenchmarkError(f"malformed atlas module at {path}:{line_number}")
        records += 1
        if module == "NumStability" or module.startswith("NumStability."):
            numstability_modules += 1
    if records == 0:
        raise BenchmarkError(f"empty declaration atlas: {path}")
    if expect_numstability and numstability_modules == 0:
        raise BenchmarkError("treatment atlas contains no NumStability modules")
    if not expect_numstability and numstability_modules != 0:
        raise BenchmarkError("Mathlib-only atlas is contaminated by NumStability")


def condition_spec(
    condition: str,
    *,
    deployment: Deployment,
    mathlib_atlas: Path,
) -> ConditionSpec:
    if condition not in CONDITIONS:
        raise BenchmarkError(f"unknown Design-16 matched condition: {condition}")
    mathlib_declarations = _atlas_declarations(mathlib_atlas, label="Mathlib")
    _classify_atlas(mathlib_declarations, expect_numstability=False)
    if condition == "R0":
        return ConditionSpec(
            name="R0",
            corpus_id="mathlib-only",
            atlas_paths=(mathlib_declarations,),
            compiler_condition="N",
            library_olean=None,
        )
    treatment_declarations = _atlas_declarations(
        deployment.library_atlas, label="NumStability"
    )
    _classify_atlas(treatment_declarations, expect_numstability=True)
    if treatment_declarations == mathlib_declarations:
        raise BenchmarkError("control and treatment atlases resolve to the same file")
    return ConditionSpec(
        name="R1",
        corpus_id="mathlib-plus-numstability",
        atlas_paths=(mathlib_declarations, treatment_declarations),
        compiler_condition="L",
        library_olean=deployment.library_olean,
    )


def _condition_order(raw: str) -> tuple[str, str]:
    order = tuple(value.strip().upper() for value in raw.split(","))
    if len(order) != 2 or set(order) != set(CONDITIONS):
        raise BenchmarkError("condition order must be exactly R0,R1 or R1,R0")
    return order  # type: ignore[return-value]


def _contract_additions(task_id: str) -> tuple[list[str], str | None]:
    contract_path = ROOT / "design16" / "contracts" / f"{task_id}.json"
    if not contract_path.exists():
        return [], None
    if not contract_path.is_file() or contract_path.is_symlink():
        raise BenchmarkError("Design-16 faithfulness-contract overlay is unsafe")
    contract = load_json(contract_path)
    values = contract.get("faithfulness_contract")
    if (
        contract.get("task_id") != task_id
        or not isinstance(values, list)
        or not all(isinstance(value, str) and value for value in values)
    ):
        raise BenchmarkError("Design-16 faithfulness-contract overlay is malformed")
    return list(values), sha256_file(contract_path)


def _prompt_bytes() -> bytes:
    base = (ROOT / "prompts" / "formalizer.md").read_text(encoding="utf-8").rstrip()
    addendum = (ROOT / "prompts" / "design16_matched_addendum.md").read_text(
        encoding="utf-8"
    )
    return (base + "\n" + addendum).encode("utf-8")


def _write_pair_report(output_root: Path, report: dict[str, Any]) -> None:
    write_json_atomic(output_root / "pair-report.json", report, mode=0o400)


def _ratio(numerator: int | float, denominator: int | float) -> float | None:
    return float(numerator) / float(denominator) if denominator else None


def _run_condition(
    *,
    args: argparse.Namespace,
    deployment: Deployment,
    spec: ConditionSpec,
    packet_path: Path,
    packet: dict[str, Any],
    contract_additions: list[str],
    paper: Path,
    prompt: bytes,
    output_root: Path,
) -> dict[str, Any]:
    condition_root = output_root / spec.name
    condition_root.mkdir(mode=0o700)

    hardware_snapshot = (
        snapshot_hardware(strict=True) if args.require_titan_envelope else None
    )

    retrieval_started = time.monotonic()
    composition, api_markdown = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=list(spec.atlas_paths),
        corpus_id=spec.corpus_id,
        contract_additions=contract_additions,
        root_limit=int(args.root_limit),
        dependency_limit=int(args.dependency_limit),
        maximum_markdown_bytes=int(args.maximum_packet_bytes),
    )
    retrieval_seconds = time.monotonic() - retrieval_started
    write_json_atomic(
        condition_root / "composition-packet.json", composition, mode=0o400
    )

    workspace = condition_root / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True, mode=0o700)
    shutil.copyfile(paper, source / "paper.pdf")
    (source / "paper.pdf").chmod(0o400)
    staged_packet = dict(packet)
    if contract_additions:
        staged_packet["scope_constraints"] = [
            *staged_packet["scope_constraints"],
            *contract_additions,
        ]
    write_bytes_atomic(
        source / "task.md", _task_packet_markdown(staged_packet).encode("utf-8"), mode=0o400
    )
    candidate = workspace / "Candidate.lean"
    write_bytes_atomic(candidate, _routed_candidate_template(composition).encode("utf-8"))
    write_bytes_atomic(
        workspace / "ENVIRONMENT.md", _environment_note().encode("utf-8"), mode=0o400
    )
    write_bytes_atomic(workspace / "LIBRARY_API.md", api_markdown, mode=0o400)

    preflight_scratch = condition_root / "template-validation-scratch"
    preflight_scratch.mkdir(mode=0o700)
    with compiled_candidate_workspace(
        candidate.read_bytes(),
        compiler_command=compiler_command(deployment, spec.compiler_condition),
        scratch_root=preflight_scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
    ) as (_, preflight_compile):
        preflight = {
            "schema_version": "formalization-design16-template-compile-1",
            "pass": preflight_compile.get("pass") is True,
            "compile": preflight_compile,
        }
    write_json_atomic(condition_root / "template-validation.json", preflight, mode=0o400)
    if preflight["pass"] is not True:
        raise BenchmarkError(f"{spec.name} controller-generated template did not compile")

    driver = CodexDriver(
        codex_binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        state_root=None,
        auth_file=deployment.auth_file,
        bwrap_binary=deployment.bwrap_binary,
        offline_shell=deployment.offline_shell,
        toolchain_root=deployment.toolchain_root,
        packages_root=deployment.packages_root,
        library_olean=spec.library_olean,
        workspace_writable=True,
        protected_workspace_paths=[
            source,
            workspace / "ENVIRONMENT.md",
            workspace / "LIBRARY_API.md",
        ],
    )
    formalizer_started = time.monotonic()
    try:
        turn = driver.run_turn(
            prompt=prompt.decode("utf-8"),
            workspace=workspace,
            artifact_dir=condition_root / "formalizer",
            timeout_seconds=float(args.time_limit_seconds),
        )
    finally:
        driver.close(artifact_dir=condition_root / "session-close")
    formalizer_seconds = time.monotonic() - formalizer_started

    validation_started = time.monotonic()
    validation_scratch = condition_root / "validation-scratch"
    validation_scratch.mkdir(mode=0o700)
    validation = validate_candidate(
        candidate,
        compiler_command=compiler_command(deployment, spec.compiler_condition),
        scratch_root=validation_scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
    )
    validation_seconds = time.monotonic() - validation_started
    write_json_atomic(condition_root / "validation.json", validation, mode=0o400)

    candidate_text = candidate.read_text(encoding="utf-8")
    usage = turn.usage
    condition_pass = (
        turn.exit_code == 0
        and not turn.timed_out
        and turn.usage_complete
        and validation.get("pass") is True
    )
    report: dict[str, Any] = {
        "schema_version": "formalization-design16-matched-condition-1",
        "scientific_status": SCIENTIFIC_STATUS,
        "faithfulness_status": "NOT_AUDITED",
        "result_status": (
            "COMPILED_AND_INTEGRITY_VALIDATED" if condition_pass else "CONDITION_INCIDENT"
        ),
        "task_id": packet["task_id"],
        "condition": spec.name,
        "corpus_id": spec.corpus_id,
        "created_at_utc": utc_now(),
        "fresh_stateless_formalizer": True,
        "warm_or_forked_conversation": False,
        "hardware_envelope_required": bool(args.require_titan_envelope),
        "hardware_snapshot": hardware_snapshot,
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "route_status": composition["route_status"],
        "primary_route": (
            composition["retrieved_roots"][0]["declaration"]["name"]
            if composition["retrieved_roots"]
            else None
        ),
        "library_olean_visible": spec.library_olean is not None,
        "atlas_input_sha256": [sha256_file(path) for path in spec.atlas_paths],
        "source_packet_sha256": sha256_file(packet_path),
        "prompt_sha256": sha256_file(output_root / "prompt.txt"),
        "composition_packet_sha256": sha256_file(
            condition_root / "composition-packet.json"
        ),
        "library_api_sha256": sha256_file(workspace / "LIBRARY_API.md"),
        "candidate_sha256": sha256_file(candidate),
        "candidate_lines": len(candidate_text.splitlines()),
        "numstability_name_mentions": candidate_text.count("NumStability"),
        "retrieval_wall_seconds": retrieval_seconds,
        "formalizer_wall_seconds": formalizer_seconds,
        "contestant_system_wall_seconds": retrieval_seconds + formalizer_seconds,
        "validation_seconds_excluded_from_contestant": validation_seconds,
        "formalizer_exit_code": turn.exit_code,
        "formalizer_timed_out": turn.timed_out,
        "usage_complete": turn.usage_complete,
        "usage": usage,
        "net_new_tokens": _net_new(usage),
        "validation_pass": validation.get("pass") is True,
        "output_root": str(condition_root),
    }
    write_json_atomic(condition_root / "report.json", report, mode=0o400)
    if not condition_pass:
        raise BenchmarkError(f"{spec.name} failed closed after formalization")
    return report


def run(args: argparse.Namespace) -> dict[str, Any]:
    task_id = args.task_id.strip().upper().replace("_", "-")
    if task_id not in ALLOWED_EXPLORATORY_TASKS:
        raise BenchmarkError("task is not in the 13-task Design-16 exploratory set")
    order = _condition_order(args.condition_order)
    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("matched output root must not already exist")
    output_root.mkdir(parents=True, mode=0o700)

    deployment = load_deployment(args.deployment)
    specs = {
        condition: condition_spec(
            condition, deployment=deployment, mathlib_atlas=args.mathlib_atlas
        )
        for condition in CONDITIONS
    }
    packet_path = ROOT / "packets" / f"{task_id}.json"
    if not packet_path.is_file() or packet_path.is_symlink():
        raise BenchmarkError("source packet is missing or unsafe")
    packet = load_json(packet_path)
    if packet.get("task_id") != task_id:
        raise BenchmarkError("source packet task ID does not match request")
    contract_additions, contract_sha256 = _contract_additions(task_id)
    paper = deployment.pdf_root / str(packet["paper_pdf"]["path_basename"])
    if (
        not paper.is_file()
        or paper.is_symlink()
        or sha256_file(paper) != packet["paper_pdf"]["sha256"]
    ):
        raise BenchmarkError("source PDF does not match the frozen packet")

    prompt = _prompt_bytes()
    write_bytes_atomic(output_root / "prompt.txt", prompt, mode=0o400)
    pair_report: dict[str, Any] = {
        "schema_version": "formalization-design16-matched-pair-1",
        "scientific_status": SCIENTIFIC_STATUS,
        "faithfulness_status": "NOT_AUDITED",
        "pair_status": "RUNNING",
        "task_id": task_id,
        "condition_order": list(order),
        "conditions_run_sequentially": True,
        "prompt_sha256": sha256_file(output_root / "prompt.txt"),
        "source_packet_sha256": sha256_file(packet_path),
        "source_pdf_sha256": sha256_file(paper),
        "contract_overlay_sha256": contract_sha256,
        "root_limit": int(args.root_limit),
        "dependency_limit": int(args.dependency_limit),
        "maximum_packet_bytes": int(args.maximum_packet_bytes),
        "created_at_utc": utc_now(),
        "condition_reports": {},
        "output_root": str(output_root),
    }
    _write_pair_report(output_root, pair_report)
    try:
        for condition in order:
            report = _run_condition(
                args=args,
                deployment=deployment,
                spec=specs[condition],
                packet_path=packet_path,
                packet=packet,
                contract_additions=contract_additions,
                paper=paper,
                prompt=prompt,
                output_root=output_root,
            )
            pair_report["condition_reports"][condition] = report
            _write_pair_report(output_root, pair_report)
    except Exception as error:
        pair_report["pair_status"] = "PAIR_INCIDENT"
        pair_report["incident"] = {
            "error_type": type(error).__name__,
            "message": str(error),
            "recorded_at_utc": utc_now(),
        }
        _write_pair_report(output_root, pair_report)
        raise

    r0 = pair_report["condition_reports"]["R0"]
    r1 = pair_report["condition_reports"]["R1"]
    pair_report["pair_status"] = "COMPILED_UNAUDITED"
    pair_report["comparison"] = {
        "r1_over_r0_contestant_system_wall": _ratio(
            r1["contestant_system_wall_seconds"], r0["contestant_system_wall_seconds"]
        ),
        "r1_over_r0_formalizer_wall": _ratio(
            r1["formalizer_wall_seconds"], r0["formalizer_wall_seconds"]
        ),
        "r1_over_r0_net_new_tokens": _ratio(
            r1["net_new_tokens"], r0["net_new_tokens"]
        ),
        "interpretation": "engineering comparison only; independent faithfulness audit required",
    }
    pair_report["completed_at_utc"] = utc_now()
    _write_pair_report(output_root, pair_report)
    return pair_report


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--condition-order", required=True, help="R0,R1 or R1,R0")
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--model", default="gpt-5.6-sol")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--time-limit-seconds", type=int, default=18000)
    parser.add_argument("--validation-timeout-seconds", type=int, default=600)
    parser.add_argument("--root-limit", type=int, default=3)
    parser.add_argument("--dependency-limit", type=int, default=5)
    parser.add_argument("--maximum-packet-bytes", type=int, default=48 * 1024)
    parser.add_argument(
        "--require-titan-envelope",
        action="store_true",
        help="fail closed unless the exact 8-CPU/32-GiB/no-swap envelope is active",
    )
    return parser


def main() -> int:
    result = run(make_parser().parse_args())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Design-16 matched error: {error}", file=sys.stderr)
        raise SystemExit(2)
