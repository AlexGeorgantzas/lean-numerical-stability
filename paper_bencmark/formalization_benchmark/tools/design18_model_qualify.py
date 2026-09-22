#!/usr/bin/env python3
"""One-shot, off-benchmark GPT-6 Sol tool/usage qualification on Titan."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from codex_driver import CodexDriver
from common import BenchmarkError, sha256_file, utc_now, write_bytes_atomic, write_json_atomic
from deployment import load_deployment
from design18_envelope import launch_or_activate
from hardware import snapshot_hardware


MODEL = "gpt-6-sol"
EFFORT = "xhigh"
PROMPT = (
    "This is an off-benchmark provider check, not a mathematical task. "
    "Read input.json using a workspace file-reading tool. Return only JSON "
    "with keys integer checksum and string reversed. Set checksum to the sum "
    "of the cubes of the listed integers and reversed to the characterwise "
    "reverse of the listed word."
)
INPUT = {"integers": [2, 3, 5], "word": "PILOT"}
EXPECTED = {"checksum": 160, "reversed": "TOLIP"}


def qualify(*, deployment_path: Path, output_root: Path) -> dict:
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("Pilot 18 provider qualification is one-shot")
    deployment = load_deployment(deployment_path)
    hardware_before = snapshot_hardware(strict=True)
    output_root.mkdir(parents=True, mode=0o700)
    workspace = output_root / "workspace"
    workspace.mkdir(mode=0o700)
    write_bytes_atomic(workspace / "input.json", json.dumps(INPUT).encode("utf-8"), mode=0o400)
    try:
        driver = CodexDriver(
            codex_binary=deployment.codex_binary,
            code_mode_host_sha256=deployment.code_mode_host_sha256,
            model=MODEL, reasoning_effort=EFFORT, state_root=None,
            auth_file=deployment.auth_file, bwrap_binary=deployment.bwrap_binary,
            offline_shell=deployment.offline_shell,
            toolchain_root=deployment.toolchain_root, packages_root=deployment.packages_root,
            workspace_writable=False,
            protected_workspace_paths=[workspace / "input.json"],
        )
        try:
            turn = driver.run_turn(
                prompt=PROMPT, workspace=workspace,
                artifact_dir=output_root / "provider-turn", timeout_seconds=600,
            )
        finally:
            driver.close(artifact_dir=output_root / "session-close")
    except Exception as error:
        write_json_atomic(output_root / "qualification.json", {
            "schema_version": "pilot-18-model-qualification-1",
            "status": "FAIL", "model": MODEL, "reasoning_effort": EFFORT,
            "failure_kind": type(error).__name__, "failure_message": str(error),
            "codex_binary_sha256": sha256_file(deployment.codex_binary),
            "code_mode_host_sha256": deployment.code_mode_host_sha256,
            "qualification_prompt_sha256": hashlib.sha256(PROMPT.encode("utf-8")).hexdigest(),
            "hardware_before": hardware_before,
            "created_at_utc": utc_now(),
        }, mode=0o400)
        raise
    try:
        answer = json.loads(turn.final_message)
    except (TypeError, json.JSONDecodeError):
        answer = None
    passed = (turn.exit_code == 0 and not turn.timed_out and turn.usage_complete
              and answer == EXPECTED)
    record = {
        "schema_version": "pilot-18-model-qualification-1",
        "status": "PASS" if passed else "FAIL",
        "model": MODEL, "reasoning_effort": EFFORT,
        "codex_binary_sha256": sha256_file(deployment.codex_binary),
        "code_mode_host_sha256": deployment.code_mode_host_sha256,
        "qualification_prompt_sha256": hashlib.sha256(PROMPT.encode("utf-8")).hexdigest(),
        "input_sha256": sha256_file(workspace / "input.json"),
        "turn_sha256": sha256_file(output_root / "provider-turn" / "turn.json"),
        "turn_exit_code": turn.exit_code, "failure_kind": turn.failure_kind,
        "usage": turn.usage, "usage_complete": turn.usage_complete,
        "wall_seconds": turn.wall_seconds,
        "hardware_before": hardware_before,
        "hardware_after": snapshot_hardware(strict=True),
        "created_at_utc": utc_now(),
    }
    write_json_atomic(output_root / "qualification.json", record, mode=0o400)
    return record


def main() -> int:
    launched = launch_or_activate(Path(__file__))
    if launched is not None:
        return launched
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    args = parser.parse_args()
    result = qualify(deployment_path=args.deployment, output_root=args.output_root)
    print(json.dumps({key: result[key] for key in
                      ("status", "model", "usage", "wall_seconds", "failure_kind")},
                     sort_keys=True))
    return 0 if result["status"] == "PASS" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot 18 qualification error: {error}", file=sys.stderr)
        raise SystemExit(2)
