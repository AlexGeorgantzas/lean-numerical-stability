#!/usr/bin/env python3
"""Run one explicitly unscored Design-16 L-only engineering smoke test.

This command cannot create an official pair and writes outside the sealed pilot
run registry.  It exists to reject bad retrieval/adaptation designs cheaply
before a successor benchmark is frozen.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

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
from deployment import load_deployment
from formalization_validator import compiled_candidate_workspace, validate_candidate
from lean_sandbox import compiler_command
from manifest_control import ROOT
from pair_controller import _candidate_template, _environment_note, _task_packet_markdown


ALLOWED_DEVELOPMENT_TASKS = {"H5-5", "H10-7"}


def _net_new(usage: dict[str, int]) -> int:
    return (
        usage.get("input_tokens", 0)
        - usage.get("cached_input_tokens", 0)
        - usage.get("cache_write_input_tokens", 0)
        + usage.get("output_tokens", 0)
    )


def _routed_candidate_template(composition: dict[str, object]) -> str:
    roots = composition.get("retrieved_roots")
    if not isinstance(roots, list) or not roots:
        return _candidate_template()
    primary = roots[0]
    if not isinstance(primary, dict) or not isinstance(primary.get("declaration"), dict):
        raise BenchmarkError("composition primary route is malformed")
    declaration = primary["declaration"]
    module = str(declaration["module"])
    names = [str(declaration["name"])]
    dependencies = primary.get("dependencies", [])
    if isinstance(dependencies, list):
        names.extend(
            str(item["name"])
            for item in dependencies
            if isinstance(item, dict) and isinstance(item.get("name"), str)
        )
    checks = "\n".join(f"#check {name}" for name in dict.fromkeys(names))
    return f"""import {module}

namespace HighamBenchCandidate

/- The controller compiled these exact API checks before the measured turn. -/
{checks}

/- Replace this placeholder with the faithful paper result and complete proof. -/
theorem target : True := by
  trivial

end HighamBenchCandidate
"""


def run(args: argparse.Namespace) -> dict[str, object]:
    task_id = args.task_id.strip().upper().replace("_", "-")
    if task_id not in ALLOWED_DEVELOPMENT_TASKS:
        raise BenchmarkError(
            "Design-16 smoke is restricted to the consumed H5-5 and H10-7 development tasks"
        )
    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("Design-16 smoke output root must not already exist")
    output_root.mkdir(parents=True, mode=0o700)
    workspace = output_root / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True, mode=0o700)
    deployment = load_deployment(args.deployment)
    packet_path = ROOT / "packets" / f"{task_id}.json"
    packet = load_json(packet_path)
    contract_path = ROOT / "design16" / "contracts" / f"{task_id}.json"
    contract_additions: list[str] = []
    if contract_path.is_file() and not contract_path.is_symlink():
        contract = load_json(contract_path)
        if contract.get("task_id") != task_id or not isinstance(
            contract.get("faithfulness_contract"), list
        ):
            raise BenchmarkError("Design-16 faithfulness-contract overlay is malformed")
        contract_additions = [str(value) for value in contract["faithfulness_contract"]]
    paper = deployment.pdf_root / str(packet["paper_pdf"]["path_basename"])
    if not paper.is_file() or paper.is_symlink() or sha256_file(paper) != packet["paper_pdf"]["sha256"]:
        raise BenchmarkError("development source PDF does not match the frozen packet")

    retrieval_started = time.monotonic()
    composition, api_markdown = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=[deployment.library_atlas / "declarations.jsonl"],
        corpus_id="mathlib-plus-numstability",
        contract_additions=contract_additions,
        root_limit=3,
        dependency_limit=5,
        maximum_markdown_bytes=48 * 1024,
    )
    retrieval_seconds = time.monotonic() - retrieval_started
    if composition["route_status"] == "NO_ROUTE":
        raise BenchmarkError("development smoke requires a nonempty composition route")

    shutil.copyfile(paper, source / "paper.pdf")
    (source / "paper.pdf").chmod(0o400)
    staged_packet = dict(packet)
    if contract_additions:
        staged_packet["scope_constraints"] = [
            *staged_packet["scope_constraints"],
            *contract_additions,
        ]
    write_bytes_atomic(
        source / "task.md",
        _task_packet_markdown(staged_packet).encode("utf-8"),
        mode=0o400,
    )
    write_bytes_atomic(
        workspace / "Candidate.lean",
        _routed_candidate_template(composition).encode("utf-8"),
    )
    write_bytes_atomic(
        workspace / "ENVIRONMENT.md", _environment_note().encode("utf-8"), mode=0o400
    )
    write_bytes_atomic(workspace / "LIBRARY_API.md", api_markdown, mode=0o400)
    write_json_atomic(output_root / "composition-packet.json", composition, mode=0o400)
    prompt = (
        (ROOT / "prompts" / "formalizer.md").read_text(encoding="utf-8").rstrip()
        + "\n"
        + (ROOT / "prompts" / "design16_addendum.md").read_text(encoding="utf-8")
    )
    write_bytes_atomic(output_root / "prompt.txt", prompt.encode("utf-8"), mode=0o400)

    template_validation_scratch = output_root / "template-validation-scratch"
    template_validation_scratch.mkdir(mode=0o700)
    with compiled_candidate_workspace(
        (workspace / "Candidate.lean").read_bytes(),
        compiler_command=compiler_command(deployment, "L"),
        scratch_root=template_validation_scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
    ) as (_, template_compile):
        template_validation = {
            "schema_version": "formalization-design16-template-compile-1",
            "pass": template_compile.get("pass") is True,
            "compile": template_compile,
        }
    write_json_atomic(
        output_root / "template-validation.json", template_validation, mode=0o400
    )
    if template_validation.get("pass") is not True:
        raise BenchmarkError("controller-generated primary-route template did not compile")

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
        library_olean=deployment.library_olean,
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
            prompt=prompt,
            workspace=workspace,
            artifact_dir=output_root / "formalizer",
            timeout_seconds=float(args.time_limit_seconds),
        )
    finally:
        driver.close(artifact_dir=output_root / "session-close")
    formalizer_seconds = time.monotonic() - formalizer_started
    candidate = workspace / "Candidate.lean"
    validation_started = time.monotonic()
    validation_scratch = output_root / "validation-scratch"
    validation_scratch.mkdir(mode=0o700)
    validation = validate_candidate(
        candidate,
        compiler_command=compiler_command(deployment, "L"),
        scratch_root=validation_scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
    )
    validation_seconds = time.monotonic() - validation_started
    write_json_atomic(output_root / "validation.json", validation, mode=0o400)
    candidate_text = candidate.read_text(encoding="utf-8")
    usage = turn.usage
    report: dict[str, object] = {
        "schema_version": "formalization-design16-smoke-1",
        "scientific_status": "UNSCORED_ENGINEERING_DIAGNOSTIC",
        "task_id": task_id,
        "condition": "L_COMPOSITION_PACKET_FRESH_THREAD",
        "created_at_utc": utc_now(),
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "route_status": composition["route_status"],
        "primary_route": composition["retrieved_roots"][0]["declaration"]["name"],
        "composition_packet_sha256": sha256_file(output_root / "composition-packet.json"),
        "library_api_sha256": sha256_file(workspace / "LIBRARY_API.md"),
        "candidate_sha256": sha256_file(candidate),
        "candidate_lines": len(candidate_text.splitlines()),
        "numstability_name_mentions": candidate_text.count("NumStability"),
        "retrieval_seconds_excluded_from_formalizer": retrieval_seconds,
        "formalizer_wall_seconds": formalizer_seconds,
        "validation_seconds_excluded_from_formalizer": validation_seconds,
        "formalizer_exit_code": turn.exit_code,
        "formalizer_timed_out": turn.timed_out,
        "usage_complete": turn.usage_complete,
        "usage": usage,
        "net_new_tokens": _net_new(usage),
        "validation_pass": validation.get("pass") is True,
        "output_root": str(output_root),
    }
    write_json_atomic(output_root / "report.json", report, mode=0o400)
    return report


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--model", default="gpt-5.6-sol")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--time-limit-seconds", type=int, default=2700)
    parser.add_argument("--validation-timeout-seconds", type=int, default=600)
    return parser


def main() -> int:
    result = run(make_parser().parse_args())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Design-16 smoke error: {error}", file=sys.stderr)
        raise SystemExit(2)
