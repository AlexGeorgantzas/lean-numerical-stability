#!/usr/bin/env python3
"""Off-benchmark audit of the sealed pilot-5 P01-T2 L submission.

This is an addendum, not a pair continuation. It never invokes the formalizer,
changes a task index, or writes under the deployment or sealed pair. The
deployed (unmodified) release authenticates the pair via its read-only status
command; the checkout containing this script supplies the repaired dossier
helper and the same audit controller.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Any

from audit_controller import AuditController
from common import (
    BenchmarkError, discover_lean_declaration_names, load_json, sha256_file,
    utc_now, write_json_atomic,
)
from deployment import load_deployment
from hardware import snapshot_hardware, verify_frozen_hardware_identity
from lean_sandbox import compiler_command, extractor_command
from prepare_candidate_audit import CandidateAuditError, prepare_candidate_audit
from titan_envelope import COMMAND_CGROUP_VARIABLE, MARKER, prepare_command_cgroup


TASK_ID = "P01-T2"
EXPECTED_CANDIDATE_SHA256 = (
    "2dedb25adbcd33b92b48dd77867210dd82d7b424b75442df4afa2877ade1fcb8"
)
PATCHED_HELPER_SHA256 = (
    "35ccdbdf237a5a269c55a42122126c8cc42c6424d4bea8543b05b408e575d1ec"
)
TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
UNCHANGED_TOOLS = (
    "audit_controller.py", "codex_driver.py", "common.py", "deployment.py",
    "formalization_validator.py", "hardware.py", "lean_sandbox.py",
    "prepare_candidate_audit.py",
)


def _regular(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"{label} is missing or unsafe: {path}")
    return path


def _outside(output: Path, protected: Path, label: str) -> None:
    if output == protected or protected in output.parents or output in protected.parents:
        raise BenchmarkError(f"addendum output overlaps {label}: {output}")


def _deployed_status(release: Path, deployment_path: Path) -> dict[str, Any]:
    launcher = _regular(
        release / "paper_bencmark/formalization_benchmark/tools/run_benchmark.py",
        "deployed status launcher",
    )
    completed = subprocess.run(
        [sys.executable, str(launcher), "--deployment", str(deployment_path),
         "status", "--task-id", TASK_ID],
        cwd=release,
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    if completed.returncode != 0:
        raise BenchmarkError(
            "deployed release could not authenticate sealed status: "
            + completed.stderr[-2000:]
        )
    try:
        value = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise BenchmarkError("deployed status is not JSON") from error
    if not isinstance(value, dict):
        raise BenchmarkError("deployed status is not an object")
    return value


def _sealed_inputs(
    state: dict[str, Any], pair_root: Path
) -> tuple[Path, Path, Path, dict[str, Any]]:
    if (
        state.get("task_id") != TASK_ID
        or state.get("status") != "PAIR_INCIDENT"
        or state.get("measurement_admissible") is not True
        or state.get("dry_run") is not False
        or state.get("incident", {}).get("condition") != "L"
        or Path(str(state.get("pair_root", ""))).resolve() != pair_root
    ):
        raise BenchmarkError("sealed pair is not the expected P01-T2 L incident")
    summary = state.get("conditions", {}).get("L")
    if not isinstance(summary, dict) or summary.get("status") != "INFRASTRUCTURE_FAILURE":
        raise BenchmarkError("L is not a sealed infrastructure-failure condition")
    condition_root = pair_root / "conditions" / "L"
    condition_state_path = _regular(condition_root / "condition_state.json", "L state")
    if sha256_file(condition_state_path) != summary.get("state_sha256"):
        raise BenchmarkError("L condition state hash mismatch")
    condition_state = load_json(condition_state_path)
    attempts = condition_state.get("attempts")
    if not isinstance(attempts, list) or len(attempts) != 1:
        raise BenchmarkError("L does not have exactly one frozen submission")
    attempt = attempts[0]
    if (
        attempt.get("attempt") != 1
        or attempt.get("status") != "INFRASTRUCTURE_FAILURE"
        or attempt.get("validation", {}).get("pass") is not True
        or "pseudonymization left local declaration or module provenance"
        not in str(attempt.get("infrastructure_error", ""))
    ):
        raise BenchmarkError("L attempt is not the diagnosed dossier incident")
    candidate = _regular(condition_root / "attempts/01/Candidate.lean", "sealed candidate")
    binding = attempt.get("candidate")
    if (
        not isinstance(binding, dict)
        or Path(str(binding.get("path", ""))).resolve() != candidate.resolve()
        or binding.get("sha256") != EXPECTED_CANDIDATE_SHA256
        or sha256_file(candidate) != EXPECTED_CANDIDATE_SHA256
        or binding.get("bytes") != candidate.stat().st_size
    ):
        raise BenchmarkError("sealed L candidate identity changed")
    staging = load_json(_regular(condition_root / "staging.json", "L staging"))
    paper = _regular(condition_root / "workspace/source/paper.pdf", "staged PDF")
    packet = _regular(condition_root / "workspace/source/task.md", "staged packet")
    if (
        staging.get("task_id") != TASK_ID
        or staging.get("condition") != "L"
        or sha256_file(paper) != staging.get("paper_sha256")
        or sha256_file(packet) != staging.get("task_packet_render_sha256")
    ):
        raise BenchmarkError("staged L PDF or task packet hash mismatch")
    pair_staging = load_json(_regular(pair_root / "pair_staging.json", "pair staging"))
    for condition in ("N", "L"):
        record = pair_staging.get(condition)
        if (
            not isinstance(record, dict)
            or record.get("paper_sha256") != sha256_file(paper)
            or record.get("packet_sha256") != sha256_file(packet)
        ):
            raise BenchmarkError("N/L frozen PDF or packet identities differ")
    return candidate, paper, packet, attempt


def run(deployment_path: Path, release: Path, output: Path) -> dict[str, Any]:
    if os.environ.get(MARKER) != "1":
        raise BenchmarkError("the fixed Titan hardware envelope is required")
    os.environ[COMMAND_CGROUP_VARIABLE] = str(prepare_command_cgroup())
    deployment_path = _regular(deployment_path.expanduser().absolute(), "deployment")
    release = release.expanduser().resolve(strict=True)
    deployment = load_deployment(deployment_path)
    state = _deployed_status(release, deployment_path)
    pair_root = Path(str(state.get("pair_root", ""))).resolve(strict=True)
    expected_pairs = (deployment.run_root / "pairs").resolve()
    if pair_root.parent != expected_pairs:
        raise BenchmarkError("sealed pair root is outside the deployed run root")
    candidate, paper, packet, attempt = _sealed_inputs(state, pair_root)
    release_manifest = load_json(_regular(
        release / "paper_bencmark/formalization_benchmark/manifest.json",
        "deployed manifest",
    ))
    task_records = [
        item for item in release_manifest.get("tasks", [])
        if isinstance(item, dict) and item.get("task_id") == TASK_ID
    ]
    if len(task_records) != 1:
        raise BenchmarkError("deployed manifest has no unique P01-T2 task")
    task_record = task_records[0]
    if (
        task_record.get("source_pdf", {}).get("sha256") != sha256_file(paper)
        or load_json(_regular(
            release / "paper_bencmark/formalization_benchmark"
            / task_record["source_packet"]["relative_path"],
            "deployed task packet",
        )).get("paper_pdf", {}).get("sha256") != sha256_file(paper)
    ):
        raise BenchmarkError("staged paper differs from the frozen release packet")
    config = load_json(_regular(
        release / "paper_bencmark/formalization_benchmark/config.json",
        "deployed config",
    ))
    output = output.expanduser().absolute()
    if output.is_symlink() or output.exists():
        raise BenchmarkError("addendum output root must be new and unused")
    output = output.resolve(strict=False)
    for protected, label in (
        (pair_root, "sealed pair"),
        (deployment.path.parent.resolve(), "deployment"),
        (deployment.run_root.resolve(), "benchmark run root"),
        (release, "deployed release"),
    ):
        _outside(output, protected, label)
    if not output.parent.is_dir() or output.parent.is_symlink():
        raise BenchmarkError("addendum output parent must be an existing safe directory")

    release_benchmark = release / "paper_bencmark/formalization_benchmark"
    helper = _regular(TOOLS / "declaration_dossier.lean", "patched Lean helper")
    if sha256_file(helper) != PATCHED_HELPER_SHA256:
        raise BenchmarkError("replay helper does not match the tested repair")
    unchanged_code_hashes: dict[str, str] = {}
    for name in UNCHANGED_TOOLS:
        local = _regular(TOOLS / name, "local audit component")
        deployed = _regular(release_benchmark / "tools" / name,
                            "deployed audit component")
        digest = sha256_file(local)
        if digest != sha256_file(deployed):
            raise BenchmarkError(f"audit component changed beyond the helper: {name}")
        unchanged_code_hashes[name] = digest
    prompt_hashes: dict[str, str] = {}
    audit_files = sorted(path for path in (ROOT / "audit").rglob("*") if path.is_file())
    for item in audit_files:
        relative = item.relative_to(ROOT / "audit").as_posix()
        deployed = _regular(release_benchmark / "audit" / relative,
                            "deployed audit prompt/schema")
        digest = sha256_file(_regular(item, "local audit prompt/schema"))
        if digest != sha256_file(deployed):
            raise BenchmarkError(f"audit prompt/schema changed: {relative}")
        prompt_hashes[relative] = digest
    source_hashes = {
        item.name: sha256_file(_regular(item, "replay source"))
        for item in (
            Path(__file__), helper, TOOLS / "prepare_candidate_audit.py",
            TOOLS / "audit_controller.py", TOOLS / "lean_sandbox.py",
            TOOLS / "formalization_validator.py", TOOLS / "codex_driver.py",
        )
    }
    hardware_start = snapshot_hardware(strict=True)
    verify_frozen_hardware_identity(
        hardware_start, load_json(deployment_path).get("hardware_identity")
    )
    output.mkdir(mode=0o700)
    record: dict[str, Any] = {
        "schema_version": "formalization-sealed-audit-addendum-1",
        "official_benchmark_result": False,
        "repair_loop_resumed": False,
        "task_id": TASK_ID,
        "condition": "L",
        "run_id": state.get("run_id"),
        "original_pair_status": "PAIR_INCIDENT",
        "sealed_pair_report": {
            "path": str(pair_root / "pair_report.json"),
            "sha256": sha256_file(_regular(pair_root / "pair_report.json", "pair report")),
        },
        "deployment_sha256": sha256_file(deployment_path),
        "deployed_release_manifest_sha256": sha256_file(
            _regular(release / "paper_bencmark/formalization_benchmark/manifest.json",
                     "deployed manifest")
        ),
        "source_hashes": source_hashes,
        "unchanged_deployed_code_hashes": unchanged_code_hashes,
        "audit_prompt_schema_hashes": prompt_hashes,
        "patched_helper_sha256": PATCHED_HELPER_SHA256,
        "strict_hardware_envelope_enforced": True,
        "sealed_inputs": {
            "candidate_sha256": sha256_file(candidate),
            "paper_sha256": sha256_file(paper),
            "task_packet_sha256": sha256_file(packet),
        },
        "original_measurements": {
            "active_seconds": attempt.get("active_seconds"),
            "active_seconds_cumulative": attempt.get("active_seconds_cumulative"),
            "usage": attempt.get("usage"),
            "usage_complete": attempt.get("usage_complete"),
            "candidate_freeze_seconds": attempt.get("candidate_freeze_seconds"),
            "model_active_seconds": attempt.get("model_active_seconds"),
            "validation": attempt.get("validation"),
        },
        "started_at_utc": utc_now(),
        "hardware_start": hardware_start,
        "status": "PREPARING_DOSSIER",
    }
    write_json_atomic(output / "addendum.json", record, mode=0o400)
    dossier_started = time.perf_counter()
    try:
        (output / "scratch").mkdir(mode=0o700)
        blind, private = prepare_candidate_audit(
            candidate,
            compiler_command=compiler_command(deployment, "L"),
            extractor_command=extractor_command(deployment, "L", helper),
            compiler_environment={},
            extractor_environment={},
            scratch_root=output / "scratch",
            timeout_seconds=600,
        )
        if private.get("candidate", {}).get("sha256") != EXPECTED_CANDIDATE_SHA256:
            raise BenchmarkError("replayed dossier has wrong candidate identity")
        record["dossier_wall_seconds"] = time.perf_counter() - dossier_started
        dossier = output / "blind_semantic_dossier.json"
        write_json_atomic(output / "private_semantic_manifest.json", private, mode=0o400)
        write_json_atomic(dossier, blind, mode=0o400)
        record["candidate_semantic_sha256"] = blind["semantic_sha256"]
        record["status"] = "AUDITING"
        write_json_atomic(output / "addendum.json", record, mode=0o400)
        audit = AuditController(
            codex_binary=deployment.codex_binary,
            code_mode_host_sha256=deployment.code_mode_host_sha256,
            auth_file=deployment.auth_file,
            model=str(config["audit_model"]),
            reasoning_effort=str(config["audit_reasoning_effort"]),
            timeout_seconds=float(config.get("audit_timeout_seconds", 7200)),
            maximum_infrastructure_retries=int(
                config.get("audit_infrastructure_retries", 2)
            ),
            bwrap_binary=deployment.bwrap_binary,
            offline_shell=deployment.offline_shell,
            toolchain_root=deployment.toolchain_root,
            packages_root=deployment.packages_root,
            forbidden_feedback_identifiers=discover_lean_declaration_names(
                deployment.library_source,
                deployment.library_source.parent / "NumStability.lean",
            ),
        )
        decision = audit.run(
            task_id=TASK_ID,
            paper_path=paper,
            paper_sha256=sha256_file(paper),
            source_packet=packet,
            dossier_path=dossier,
            semantic_sha256=blind["semantic_sha256"],
            audit_root=output / "audit",
        )
        record["audit_verdict"] = decision["verdict"]
        record["accepted"] = decision["accepted"]
        record["audit_incident"] = decision["audit_incident"]
        record["status"] = (
            "AUDIT_SYSTEM_INCIDENT"
            if decision["audit_incident"] or decision["verdict"] == "unclear"
            else "AUDIT_COMPLETE"
        )
        record["audit_decision_sha256"] = sha256_file(output / "audit/decision.json")
    except (BenchmarkError, CandidateAuditError, OSError, ValueError) as error:
        record["status"] = "ADDENDUM_INCIDENT"
        record["error"] = str(error)
        raise
    finally:
        record["completed_at_utc"] = utc_now()
        record["hardware_end"] = snapshot_hardware(strict=True)
        write_json_atomic(output / "addendum.json", record, mode=0o400)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--deployed-release", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = run(args.deployment, args.deployed_release, args.output_root)
    except (BenchmarkError, CandidateAuditError, OSError, ValueError,
            subprocess.TimeoutExpired) as error:
        print(f"sealed L audit addendum failed: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
