#!/usr/bin/env python3
"""Create the single task-neutral GPT-6 Sol orientation fork source.

This is deliberately one-shot and off-benchmark. A failed root is retained as
an incident; it is never overwritten or silently retried.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import sys

from codex_driver import CodexDriver
from common import (
    BenchmarkError, assert_no_credentials_in_tree, load_json, sha256_file,
    tree_manifest, utc_now, write_bytes_atomic, write_json_atomic,
)
from deployment import load_deployment
from design18_atlas import bind_release_atlases
from design18_envelope import launch_or_activate
from design18_matched import _qualified
from design18_preflight import DESIGN_ROOT, check_corpus
from hardware import snapshot_hardware


MODEL = "gpt-6-sol"
EFFORT = "xhigh"
SCHEMA = "pilot-18-warm-root-1"


def prepare(*, deployment_path: Path, mathlib_atlas: Path,
            numstability_atlas: Path, model_qualification: Path,
            output_root: Path, scout_prompt: Path | None = None,
            schema_version: str = SCHEMA,
            require_pilot18_corpus: bool = True,
            required_final_terms: tuple[str, ...] = ()) -> dict:
    if require_pilot18_corpus:
        corpus, _packets, flags = check_corpus()
        if flags:
            raise BenchmarkError(f"source flags must be resolved before scouting: {flags}")
        if corpus["formalizer_model"] != MODEL or corpus["formalizer_reasoning_effort"] != EFFORT:
            raise BenchmarkError("Pilot 18 formalizer model changed")
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("warm-root output already exists; scouting is one-shot")
    deployment = load_deployment(deployment_path)
    deployment, _ = bind_release_atlases(
        deployment, mathlib=mathlib_atlas, numstability=numstability_atlas,
    )
    _qualified(
        model_qualification, binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
    )
    prompt = scout_prompt or DESIGN_ROOT / "prompts" / "scout.md"
    if not prompt.is_file() or prompt.is_symlink():
        raise BenchmarkError("scout prompt is missing or unsafe")
    output_root.mkdir(parents=True, mode=0o700)
    checkpoint = output_root / "checkpoint"
    checkpoint.mkdir(mode=0o700)
    workspace = output_root / "scout-workspace"
    workspace.mkdir(mode=0o700)
    write_bytes_atomic(workspace / "ENVIRONMENT.md", (
        "# Task-neutral orientation workspace\n\n"
        "There is no benchmark task, task list, paper, or candidate here. "
        "Only the frozen library is mounted read-only.\n"
    ).encode("utf-8"), mode=0o400)
    planned = {
        "schema_version": schema_version, "status": "SCOUTING",
        "model": MODEL, "reasoning_effort": EFFORT,
        "source_task_material_available": False,
        "scout_prompt_sha256": sha256_file(prompt),
        "library_atlas_sha256": sha256_file(deployment.library_atlas / "declarations.jsonl"),
        "codex_binary_sha256": sha256_file(deployment.codex_binary),
        "code_mode_host_sha256": deployment.code_mode_host_sha256,
        "model_qualification_sha256": sha256_file(model_qualification),
        "hardware_before": snapshot_hardware(strict=True),
        "created_at_utc": utc_now(),
    }
    write_json_atomic(output_root / "warm-root.json", planned, mode=0o400)
    try:
        driver = CodexDriver(
            codex_binary=deployment.codex_binary,
            code_mode_host_sha256=deployment.code_mode_host_sha256,
            model=MODEL, reasoning_effort=EFFORT,
            state_root=checkpoint / "state", auth_file=deployment.auth_file,
            bwrap_binary=deployment.bwrap_binary, offline_shell=deployment.offline_shell,
            toolchain_root=deployment.toolchain_root, packages_root=deployment.packages_root,
            library_source=deployment.library_source,
            library_olean=deployment.library_olean,
            library_atlas=deployment.library_atlas,
            workspace_writable=False,
            protected_workspace_paths=[workspace / "ENVIRONMENT.md"],
        )
        try:
            turn = driver.run_turn(
                prompt=prompt.read_text(encoding="utf-8"), workspace=workspace,
                artifact_dir=output_root / "scout-artifacts", timeout_seconds=18000,
            )
        finally:
            driver.close(artifact_dir=output_root / "scout-session-close")
    except Exception as error:
        write_json_atomic(output_root / "warm-root.json", {
            **planned, "status": "FAILED", "failure_kind": type(error).__name__,
            "failure_message": str(error), "completed_at_utc": utc_now(),
        }, mode=0o400)
        raise
    turn_record = load_json(output_root / "scout-artifacts" / "turn.json")
    if (turn.exit_code != 0 or turn.timed_out or not turn.usage_complete
            or turn.thread_cumulative_usage is None
            or turn_record.get("terminal_status") != "completed"
            or not isinstance(turn_record.get("turn_id"), str)
            or not turn_record["turn_id"] or not turn.thread_id):
        failed = {**planned, "status": "FAILED", "failure_kind": turn.failure_kind,
                  "turn_exit_code": turn.exit_code, "turn_usage": turn.usage,
                  "turn_wall_seconds": turn.wall_seconds, "completed_at_utc": utc_now()}
        write_json_atomic(output_root / "warm-root.json", failed, mode=0o400)
        raise BenchmarkError("the one-time GPT-6 Sol orientation did not complete")
    final_message = (output_root / "scout-artifacts" / "last_message.txt").read_text(
        encoding="utf-8"
    )
    missing_terms = [term for term in required_final_terms if term not in final_message]
    if missing_terms:
        write_json_atomic(output_root / "warm-root.json", {
            **planned, "status": "FAILED", "failure_kind": "INCOMPLETE_ORIENTATION",
            "missing_required_terms": missing_terms, "completed_at_utc": utc_now(),
        }, mode=0o400)
        raise BenchmarkError("one-time orientation omitted required foundational names")
    marker = checkpoint / ".state-network-violations.bin"
    if marker.exists() or marker.is_symlink():
        if marker.is_symlink() or not marker.is_file() or marker.stat().st_size:
            raise BenchmarkError("warm root has a network-violation marker")
        marker.unlink()
    temporary = checkpoint / "state" / "tmp"
    if temporary.exists() or temporary.is_symlink():
        if temporary.is_symlink() or not temporary.is_dir():
            raise BenchmarkError("warm root has an unsafe temporary tree")
        shutil.rmtree(temporary)
    assert_no_credentials_in_tree(checkpoint, deployment.auth_file)
    ready = {
        **planned, "status": "READY", "source_thread_id": turn.thread_id,
        "source_last_turn_id": turn_record["turn_id"],
        "source_cumulative_usage": turn.thread_cumulative_usage,
        "scout_usage": turn.usage, "scout_usage_complete": turn.usage_complete,
        "scout_wall_seconds": turn.wall_seconds,
        "scout_turn_sha256": sha256_file(output_root / "scout-artifacts" / "turn.json"),
        "checkpoint_manifest": tree_manifest(checkpoint),
        "hardware_after": snapshot_hardware(strict=True),
        "completed_at_utc": utc_now(),
        "cost_accounting": "logged_once_excluded_from_per_task_active_metrics",
    }
    write_json_atomic(output_root / "warm-root.json", ready, mode=0o400)
    return ready


def main() -> int:
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--numstability-atlas", type=Path, required=True)
    parser.add_argument("--model-qualification", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    result = prepare(deployment_path=args.deployment,
                     mathlib_atlas=args.mathlib_atlas,
                     numstability_atlas=args.numstability_atlas,
                     model_qualification=args.model_qualification,
                     output_root=args.output_root)
    print(json.dumps({key: result[key] for key in
                      ("status", "model", "scout_usage", "scout_wall_seconds")}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 18 warm-root error: {error}", file=sys.stderr)
        raise SystemExit(2)
