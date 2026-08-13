#!/usr/bin/env python3
"""Authenticate and render the private, frozen HighamBench P01 checkpoint.

This renderer intentionally accepts only the first complete paper boundary: the
18 scored P01 assignments (three targets, three repetitions, two conditions).
It replays the important provenance links instead of trusting an earlier
analysis file.  In particular, passing Ultra records are tied to the frozen
outer code-mode ``exec`` and its blocked inner ``submit_proof`` request,
immutable candidate snapshot, accepted proof, hidden validation result, and
exact provider-usage ledger.
"""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import datetime as dt
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import random
import re
import stat
import statistics
import subprocess
import sys
from typing import Any, Iterable, Mapping, Sequence

try:
    from . import codex_isolated, preflight, render_report as construction_report, run_matrix, runner, validator
    from . import run_token_control_canary as token_canary
    from . import run_ultra_orchestration_canary as ultra_canary
    from .common import BenchmarkToolError
except ImportError:  # Direct script execution.
    import codex_isolated  # type: ignore
    import preflight  # type: ignore
    import render_report as construction_report  # type: ignore
    import run_matrix  # type: ignore
    import runner  # type: ignore
    import validator  # type: ignore
    import run_token_control_canary as token_canary  # type: ignore
    import run_ultra_orchestration_canary as ultra_canary  # type: ignore
    from common import BenchmarkToolError  # type: ignore


REPORT_SCHEMA_VERSION = 1
EXPECTED_PAPER = "P01"
EXPECTED_TASKS = ("P01-T1", "P01-T2", "P01-T3")
EXPECTED_CONDITIONS = ("N", "L")
EXPECTED_REPETITIONS = ("rep-01", "rep-02", "rep-03")
EXPECTED_FINAL_RUNS = 18
EXPECTED_CONSTRUCTION_RESULTS = 120
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
PROTOCOL_CLAIMS = (
    "fresh_conversation",
    "filesystem_isolated",
    "network_disabled",
    "backend_seed_supplied",
    "seed_enforced_by_agent",
    "token_limit_enforced_by_agent",
    "condition_l_library_available",
)
EXPECTED_PROTOCOL_CLAIMS = {
    "fresh_conversation": True,
    "filesystem_isolated": True,
    "network_disabled": True,
    # The frozen Codex backend has no demonstrated seed input.  These false
    # values are controls, not missing evidence: rep-01..03 are repetitions.
    "backend_seed_supplied": False,
    "seed_enforced_by_agent": False,
    "token_limit_enforced_by_agent": True,
    "condition_l_library_available": True,
}
PROTOCOL_VERIFICATIONS = (
    "fresh_workspace_copy",
    "condition_n_preflight",
    "condition_n_import_probe_complete",
    "network_violation_marker_integrity",
    "authenticated_prompt_release",
    "authenticated_first_valid_proof_boundary",
)
FAILURE_CODES = {
    "TIME_LIMIT",
    "TOKEN_LIMIT",
    "NO_SUBMISSION",
    "RULE_VIOLATION",
    "SYNTAX_OR_ELAB",
    "PROOF_ERROR",
    "SYSTEM_ERROR",
}
FAILURE_PRECEDENCE = (
    "TIME_LIMIT",
    "TOKEN_LIMIT",
    "NO_SUBMISSION",
    "RULE_VIOLATION",
    "SYNTAX_OR_ELAB",
    "PROOF_ERROR",
    "SYSTEM_ERROR",
)
MAX_FAILURE_NOTE_BYTES = 4096
POST_SUBMISSION_VALIDATION_RESERVE_SECONDS = 369.0
UNSEEDED_PROTOCOL_NOTE = (
    "no backend seed was supplied; the repetition ID is not being presented as a seed"
)
SIGNPOSTED_DEVIATION_MARKERS = (
    "signposted-library-v1",
    "user-directed",
    "identical-prompt",
)
ACCOUNTING_TOKEN_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)
FORK_POLICY_CALL_FIELDS = {
    "call_id",
    "parent_thread_id",
    "parent_turn_id",
    "parent_response_id",
    "fork_turns",
    "fork_semantics",
    "hook_run_id",
    "hook_source_path",
    "hook_thread_id",
    "hook_turn_id",
    "hook_started_observed",
    "hook_started_count",
    "hook_completed_observed",
    "hook_completed_count",
    "hook_status",
    "decision",
    "feedback",
    "resolution_status",
    "child_activity_observed",
}


class ReportError(RuntimeError):
    """Raised when a purported checkpoint is incomplete or unauthenticated."""


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ReportError(f"JSON object repeats key {key!r}")
        result[key] = value
    return result


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicate_keys
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ReportError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ReportError(f"JSON document is not an object: {path}")
    return value


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def document_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
    except OSError as error:
        raise ReportError(f"cannot hash {path}: {error}") from error
    return digest.hexdigest()


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ReportError(f"{label} must be an object")
    return value


def _list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReportError(f"{label} must be a list")
    return value


def _hex(value: Any, label: str) -> str:
    if not isinstance(value, str) or HEX64.fullmatch(value) is None:
        raise ReportError(f"{label} must be a lowercase SHA-256")
    return value


def _number(value: Any, label: str, *, nonnegative: bool = True) -> float:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        raise ReportError(f"{label} must be numeric")
    result = float(value)
    if not math.isfinite(result) or (nonnegative and result < 0):
        raise ReportError(f"{label} is outside its allowed range")
    return result


def _integer(value: Any, label: str, *, positive: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < int(positive):
        raise ReportError(f"{label} must be a {'positive' if positive else 'nonnegative'} integer")
    return value


def _iso(value: Any, label: str) -> dt.datetime:
    if not isinstance(value, str):
        raise ReportError(f"{label} must be an ISO timestamp")
    try:
        result = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as error:
        raise ReportError(f"{label} is not an ISO timestamp") from error
    if result.tzinfo is None:
        result = result.replace(tzinfo=dt.timezone.utc)
    return result


def _safe_relative(value: Any, label: str) -> PurePosixPath:
    if not isinstance(value, str) or not value:
        raise ReportError(f"{label} has no path")
    relative = PurePosixPath(value)
    if relative.is_absolute() or ".." in relative.parts:
        raise ReportError(f"{label} path is not safe: {value!r}")
    return relative


def _inside(root: Path, path: Path, label: str) -> Path:
    root = root.resolve()
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise ReportError(f"{label} escapes {root}: {path}") from error
    return path


def _project_root(benchmark_root: Path) -> Path:
    root = benchmark_root.resolve()
    if root.name == "highambench" and root.parent.name == "paper_bencmark":
        return root.parent.parent
    return root


def _resolve_frozen_path(
    benchmark_root: Path, raw: Any, label: str, *, must_exist: bool = True
) -> Path:
    relative = _safe_relative(raw, label)
    project = _project_root(benchmark_root)
    choices = [project / relative, benchmark_root / relative]
    if relative.parts[:2] == ("paper_bencmark", "highambench"):
        choices.insert(0, project / relative)
    seen: set[Path] = set()
    for choice in choices:
        candidate = choice.resolve()
        if candidate in seen:
            continue
        seen.add(candidate)
        allowed = False
        for parent in (project.resolve(), benchmark_root.resolve()):
            try:
                candidate.relative_to(parent)
                allowed = True
            except ValueError:
                pass
        if allowed and (not must_exist or candidate.is_file()):
            return candidate
    raise ReportError(f"{label} does not resolve to a frozen file: {raw!r}")


def _resolve_result_path(results_root: Path, raw: Any, label: str) -> Path:
    if not isinstance(raw, str) or not raw:
        raise ReportError(f"{label} has no path")
    candidate = Path(raw)
    if not candidate.is_absolute():
        candidate = results_root / candidate
    candidate = _inside(results_root, candidate, label)
    if not candidate.is_file() or candidate.is_symlink():
        raise ReportError(f"{label} is missing: {candidate}")
    return candidate


def environment_bundle_sha256(
    config: Mapping[str, Any], environment: Mapping[str, Any]
) -> str:
    config_copy = json.loads(json.dumps(config))
    environment_copy = json.loads(json.dumps(environment))
    frozen = config_copy.get("frozen_environment")
    if isinstance(frozen, dict):
        frozen.pop("environment_id", None)
        frozen.pop("environment_bundle_sha256", None)
    environment_copy.pop("environment_id", None)
    environment_copy.pop("environment_bundle_sha256", None)
    return document_sha256({"config": config_copy, "environment": environment_copy})


def _authenticate_release(
    benchmark_root: Path,
    release: Mapping[str, Any],
    expected_sha256: Any,
) -> dict[str, Any]:
    release_path = benchmark_root / "metadata" / "release_files.json"
    actual_release_sha = file_sha256(release_path)
    if actual_release_sha != _hex(expected_sha256, "frozen release manifest digest"):
        raise ReportError("current release_files.json does not match the frozen digest")
    files = _list(release.get("files"), "release files")
    if not files:
        raise ReportError("release manifest is empty")
    seen: set[str] = set()
    required = {"metadata/manifest.json", "metadata/run_order.json"}
    total_bytes = 0
    for index, raw in enumerate(files):
        entry = _mapping(raw, f"release file {index}")
        relative = _safe_relative(entry.get("path"), f"release file {index}")
        name = relative.as_posix()
        if name in seen:
            raise ReportError(f"release manifest repeats {name}")
        seen.add(name)
        path = _inside(benchmark_root, benchmark_root / relative, f"release file {name}")
        if not path.is_file():
            raise ReportError(f"release file is missing: {name}")
        expected_bytes = _integer(entry.get("bytes"), f"release bytes for {name}")
        if path.stat().st_size != expected_bytes:
            raise ReportError(f"release file size changed: {name}")
        if file_sha256(path) != _hex(entry.get("sha256"), f"release hash for {name}"):
            raise ReportError(f"release file hash changed: {name}")
        total_bytes += expected_bytes
    if not required.issubset(seen):
        raise ReportError("release manifest omits manifest.json or run_order.json")
    return {
        "sha256": actual_release_sha,
        "file_count": len(files),
        "total_bytes": total_bytes,
    }


def _expected_agent(config: Mapping[str, Any]) -> dict[str, Any]:
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    return {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
    }


def _expected_canary_agent(config: Mapping[str, Any]) -> dict[str, Any]:
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    return {
        **_expected_agent(config),
        "binary_sha256": _hex(
            frozen.get("agent_binary_sha256"), "frozen agent binary digest"
        ),
        "ultra_orchestration": frozen.get("ultra_orchestration"),
    }


def _token_canary_prompt_release_summary(
    value: Any,
    *,
    artifact_label_count: int,
) -> dict[str, Any]:
    release = _mapping(value, "token-control canary prompt release")
    expected_fields = {
        "schema_version",
        "protocol_version",
        "status",
        "authenticated",
        "timing_exact",
        "useful_work_basis",
        "startup_timeout_seconds",
        "startup_timeout_triggered",
        "go_minimum_release_window_seconds",
        "artifact_content_verified",
        "artifact_count",
        "artifacts",
        "canonical_encoding",
        "sealed_mode",
        "handshake_nonce",
        "root_thread_id",
        "effective_prompt_sha256",
        "effective_prompt_bytes",
        "turn_start_request_sha256",
        "turn_start_wire_verified",
        "command_binding_verified",
        "root_identity_verified",
        "ready_sha256",
        "go_sha256",
        "release_sha256",
        "measurement_time_origin",
        "released_at_monotonic_ns",
        "deadline_monotonic_ns",
        "deadline_derivation",
        "wall_time_seconds",
        "actual_stop_seconds",
        "token_crossing_within_deadline",
        "first_valid_seconds",
        "submission_boundary",
        "sanitized_provider_gate_crossing",
        "top_level_artifact_count_unchanged",
    }
    artifacts = _mapping(
        release.get("artifacts"), "token-control canary prompt artifacts"
    )
    paths: list[str] = []
    for label in ("ready", "go", "release"):
        descriptor = _mapping(
            artifacts.get(label), f"token-control canary prompt {label}"
        )
        path = descriptor.get("path")
        if (
            set(descriptor) != {"path", "file_sha256", "record_sha256"}
            or not isinstance(path, str)
            or not Path(path).is_absolute()
            or HEX64.fullmatch(str(descriptor.get("file_sha256"))) is None
            or HEX64.fullmatch(str(descriptor.get("record_sha256"))) is None
        ):
            raise ReportError(
                f"token-control canary prompt {label} descriptor is invalid"
            )
        paths.append(path)
    released = release.get("released_at_monotonic_ns")
    deadline = release.get("deadline_monotonic_ns")
    wall = release.get("wall_time_seconds")
    actual_stop = release.get("actual_stop_seconds")
    if (
        set(release) != expected_fields
        or set(artifacts) != {"ready", "go", "release"}
        or len(set(paths)) != 3
        or release.get("schema_version") != 1
        or release.get("protocol_version") != "highambench-prompt-release-v1"
        or release.get("status") != "released_authenticated"
        or release.get("authenticated") is not True
        or release.get("timing_exact") is not True
        or release.get("useful_work_basis") != "authenticated_release"
        or release.get("startup_timeout_seconds") != 120.0
        or release.get("startup_timeout_triggered") is not False
        or release.get("go_minimum_release_window_seconds") != 5.0
        or release.get("artifact_content_verified") is not True
        or release.get("artifact_count") != 3
        or release.get("canonical_encoding")
        != "compact_sorted_key_utf8_json_newline"
        or release.get("sealed_mode") != "0444"
        or HEX64.fullmatch(str(release.get("handshake_nonce"))) is None
        or not isinstance(release.get("root_thread_id"), str)
        or not release["root_thread_id"]
        or type(release.get("effective_prompt_bytes")) is not int
        or release["effective_prompt_bytes"] <= 0
        or release.get("turn_start_wire_verified") is not True
        or release.get("command_binding_verified") is not True
        or release.get("root_identity_verified") is not True
        or release.get("measurement_time_origin")
        != "RELEASED.released_at_monotonic_ns"
        or type(released) is not int
        or released <= 0
        or type(deadline) is not int
        or type(wall) is not int
        or wall <= 0
        or deadline != released + wall * 1_000_000_000
        or release.get("deadline_derivation")
        != "released_at_monotonic_ns + wall_time_seconds*1000000000"
        or not isinstance(actual_stop, (int, float))
        or isinstance(actual_stop, bool)
        or not 0 < actual_stop < wall
        or release.get("token_crossing_within_deadline") is not True
        or release.get("first_valid_seconds") is not None
        or release.get("submission_boundary") is not None
        or release.get("sanitized_provider_gate_crossing") is not True
        or release.get("top_level_artifact_count_unchanged")
        != artifact_label_count
    ):
        raise ReportError(
            "token-control canary prompt release is not an exact provider-gate crossing"
        )
    for field in (
        "effective_prompt_sha256",
        "turn_start_request_sha256",
        "ready_sha256",
        "go_sha256",
        "release_sha256",
    ):
        _hex(release.get(field), f"token-control canary {field}")
    return dict(release)


def _ultra_canary_prompt_release_summary(value: Any) -> dict[str, Any]:
    release = _mapping(value, "Ultra canary prompt release")
    expected_fields = {
        "schema_version",
        "protocol_version",
        "authenticated",
        "timing_exact",
        "elapsed_clock",
        "startup_timeout_seconds",
        "artifact_count",
        "artifacts_reauthenticated",
        "released_at_monotonic_ns",
        "measurement_deadline_monotonic_ns",
        "request_published_at_monotonic_ns",
        "request_publication_timing_verified",
    }
    released = release.get("released_at_monotonic_ns")
    deadline = release.get("measurement_deadline_monotonic_ns")
    published = release.get("request_published_at_monotonic_ns")
    if (
        set(release) != expected_fields
        or release.get("schema_version") != 1
        or release.get("protocol_version") != "highambench-prompt-release-v1"
        or release.get("authenticated") is not True
        or release.get("timing_exact") is not True
        or release.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or release.get("startup_timeout_seconds") != 120.0
        or release.get("artifact_count") != 3
        or release.get("artifacts_reauthenticated") is not True
        or type(released) is not int
        or type(deadline) is not int
        or type(published) is not int
        or released <= 0
        or not released <= published < deadline
        or release.get("request_publication_timing_verified") is not True
    ):
        raise ReportError(
            "Ultra canary prompt release does not authenticate request publication"
        )
    return dict(release)


def _authenticate_canary(
    benchmark_root: Path,
    descriptor_raw: Any,
    *,
    name: str,
    benchmark_id: str,
    agent: Mapping[str, Any],
    token_limit: int,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
) -> dict[str, Any]:
    descriptor = _mapping(descriptor_raw, f"{name} descriptor")
    token_control = name == "token-control canary"
    expected_path = (
        token_canary.FROZEN_EVIDENCE_PATH
        if token_control
        else ultra_canary.FROZEN_EVIDENCE_PATH
    )
    if (
        set(descriptor) != {"path", "sha256", "status"}
        or descriptor.get("path") != expected_path
        or descriptor.get("status") != "passed"
    ):
        raise ReportError(f"{name} is not the exact promoted passed live canary")
    evidence_path = _resolve_frozen_path(benchmark_root, descriptor.get("path"), name)
    digest = file_sha256(evidence_path)
    if digest != _hex(descriptor.get("sha256"), f"{name} descriptor digest"):
        raise ReportError(f"{name} evidence digest does not match its descriptor")
    evidence = read_json(evidence_path)
    project_root = _project_root(benchmark_root)
    try:
        if token_control:
            verified = token_canary.validate_attestation_document(
                evidence,
                project_root=project_root,
                expected_benchmark_id=benchmark_id,
                expected_agent=agent,
                expected_frozen_token_limit=token_limit,
            )
        else:
            verified = ultra_canary.verify_frozen_attestation(
                project_root,
                descriptor,
                expected_benchmark_id=benchmark_id,
                expected_agent=agent,
                expected_token_limit=token_limit,
                expected_prompt_protocol=prompt_protocol,
                expected_execution_components=execution_components,
            )
    except (OSError, RuntimeError, BenchmarkToolError) as error:
        raise ReportError(f"{name} failed canonical authentication: {error}") from error
    summary = {"path": expected_path, "sha256": digest, **dict(verified)}
    artifacts = _mapping(summary.get("artifacts"), f"{name} verified artifacts")
    expected_artifacts = (
        token_canary.ARTIFACT_LABELS
        if token_control
        else ultra_canary.ARTIFACT_LABELS
    )
    if set(artifacts) != set(expected_artifacts):
        raise ReportError(f"{name} canonical artifact set is incomplete")
    raw_artifacts_for_gate = _mapping(
        evidence.get("artifacts"), f"{name} evidence artifacts"
    )
    artifact_root_relative = _safe_relative(
        evidence.get("artifact_root"), f"{name} artifact root"
    )
    artifact_root_path = _inside(
        project_root,
        project_root / artifact_root_relative,
        f"{name} artifact root",
    )

    def canary_artifact_path(artifact_label: str) -> Path:
        raw_descriptor = _mapping(
            raw_artifacts_for_gate.get(artifact_label),
            f"{name} {artifact_label} artifact",
        )
        relative = _safe_relative(
            raw_descriptor.get("path"), f"{name} {artifact_label} artifact"
        )
        path = _inside(
            artifact_root_path,
            artifact_root_path / relative,
            f"{name} {artifact_label} artifact",
        )
        if (
            not path.is_file()
            or path.is_symlink()
            or file_sha256(path)
            != _hex(
                raw_descriptor.get("sha256"),
                f"{name} {artifact_label} digest",
            )
        ):
            raise ReportError(f"{name} {artifact_label} artifact is unauthenticated")
        return path

    canary_runner_path = canary_artifact_path(
        "record" if token_control else "runner_record"
    )
    canary_gate_path = canary_artifact_path("provider_gate")
    canary_runner_record = _mapping(
        read_json(canary_runner_path), f"{name} runner record"
    )
    try:
        gate_authentication = construction_report._authenticate_provider_gate_record(
            canary_runner_record,
            artifact_path=canary_gate_path,
            label=name,
        )
    except construction_report.ReportError as error:
        raise ReportError(f"{name} provider-gate authentication failed: {error}") from error
    if token_control:
        try:
            construction_report._validate_token_canary_provider_gate_shape(
                gate_authentication, name
            )
        except construction_report.ReportError as error:
            raise ReportError(f"{name} provider-gate shape failed: {error}") from error
        summary["prompt_release"] = _token_canary_prompt_release_summary(
            summary.get("prompt_release"),
            artifact_label_count=len(expected_artifacts),
        )
        projection = summary.get("accounting_projection")
        zero = {field: 0 for field in ACCOUNTING_TOKEN_FIELDS}
        expected_projection_fields = {
            "accounting_projection_schema_version",
            "provider_gate_protocol",
            "provider_gate_record_sha256",
            "provider_gate_close_reason",
            "provider_gate_response_ids",
            "provider_gate_deliveries_reconciled",
            "provider_usage_reconciliation",
            "provider_gate_setup_requests_empty",
            "provider_requests_quiescent",
            "adapter_teardown_complete",
            "spawn_binding_source",
            "root_thread_id",
            "root_expected_cumulative_baseline",
            "root_cumulative_projection_status",
            "spawn_linkage_complete",
            "descendant_accounting_complete",
            "cumulative_projection_complete",
            "raw_spawn_call_ids",
            "activity_spawn_call_ids",
            "collab_spawn_call_ids",
            "resolved_spawn_call_ids",
            "failed_spawn_call_ids",
            "policy_blocked_spawn_call_ids",
            "unresolved_spawn_call_ids",
            "unsupported_spawn_call_ids",
            "inference_child_thread_ids",
            "hook_observed_spawn_call_ids",
            "hook_allowed_spawn_call_ids",
            "hook_blocked_spawn_call_ids",
            "hook_invalid_spawn_call_ids",
            "fork_policy_complete",
            "fork_policy",
            "accounting_complete",
            "root_only",
            "projection_payload_sha256",
        }
        expected_policy = {
            **ultra_canary.codex_isolated.ultra_fork_policy_static_record(),
            "call_evidence": [],
            "complete": True,
        }
        if (
            summary.get("status") != "passed"
            or summary.get("canary_limit_tokens")
            != token_canary.DEFAULT_CANARY_TOKEN_LIMIT
            or summary.get("thread_count") != 1
            or type(summary.get("thread_count")) is not int
            or summary.get("observed_child_thread_count") != 0
            or type(summary.get("observed_child_thread_count")) is not int
            or summary.get("response_count") != 2
            or type(summary.get("response_count")) is not int
            or summary.get("drain_complete") is not False
            or summary.get("provider_gate_quiescent") is not True
            or summary.get("measurement_exact") is not True
            or summary.get("synthetic_input") is not True
            or summary.get("matrix_assignment") is not False
            or summary.get("benchmark_task_bytes_used") is not False
            or summary.get("prompt_protocol") != token_canary.PROMPT_PROTOCOL
            or not isinstance(projection, Mapping)
            or set(projection) != expected_projection_fields
            or projection.get("accounting_projection_schema_version")
            != token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
            or projection.get("spawn_binding_source")
            != ultra_canary.SPAWN_BINDING_SOURCE
            or projection.get("root_expected_cumulative_baseline") != zero
            or projection.get("root_cumulative_projection_status")
            not in {"missing_cumulative", "cumulative_projection_mismatch"}
            or projection.get("root_only") is not True
            or projection.get("provider_gate_protocol")
            != runner.PROVIDER_GATE_PROTOCOL
            or projection.get("provider_gate_record_sha256")
            != gate_authentication.get("record_sha256")
            or projection.get("provider_gate_close_reason") != "token_limit"
            or projection.get("provider_gate_response_ids")
            != gate_authentication.get("response_ids")
            or projection.get("provider_gate_deliveries_reconciled")
            is not True
            or projection.get("provider_gate_setup_requests_empty") is not True
            or projection.get("provider_requests_quiescent") is not True
            or projection.get("adapter_teardown_complete") is not True
            or any(
                projection.get(field) is not True
                for field in (
                    "spawn_linkage_complete",
                    "descendant_accounting_complete",
                    "fork_policy_complete",
                )
            )
            or projection.get("cumulative_projection_complete") is not False
            or projection.get("accounting_complete") is not False
            or any(
                projection.get(field) != []
                for field in (
                    "raw_spawn_call_ids",
                    "activity_spawn_call_ids",
                    "collab_spawn_call_ids",
                    "resolved_spawn_call_ids",
                    "failed_spawn_call_ids",
                    "policy_blocked_spawn_call_ids",
                    "unresolved_spawn_call_ids",
                    "unsupported_spawn_call_ids",
                    "inference_child_thread_ids",
                    "hook_observed_spawn_call_ids",
                    "hook_allowed_spawn_call_ids",
                    "hook_blocked_spawn_call_ids",
                    "hook_invalid_spawn_call_ids",
                )
            )
            or projection.get("fork_policy") != expected_policy
            or HEX64.fullmatch(str(projection.get("projection_payload_sha256")))
            is None
            or document_sha256(
                {
                    key: value
                    for key, value in projection.items()
                    if key != "projection_payload_sha256"
                }
            )
            != projection.get("projection_payload_sha256")
            or type(summary.get("first_crossing_tokens")) is not int
            or type(summary.get("final_endpoint_tokens")) is not int
            or summary["first_crossing_tokens"]
            < token_canary.DEFAULT_CANARY_TOKEN_LIMIT
            or summary["final_endpoint_tokens"] != summary["first_crossing_tokens"]
            or summary["first_crossing_tokens"]
            != gate_authentication.get("completed_tokens")
            or summary["final_endpoint_tokens"]
            != gate_authentication.get("completed_tokens")
            or HEX64.fullmatch(str(summary.get("source_separation_audit_sha256")))
            is None
        ):
            raise ReportError(
                "token-control canary lacks the canonical synthetic provider-gate crossing"
            )
        try:
            construction_report._validate_canary_projection_provider_reconciliation(
                projection, canary_runner_record, gate_authentication, name
            )
        except construction_report.ReportError as error:
            raise ReportError(
                f"{name} projection provider reconciliation failed: {error}"
            ) from error
        artifact_root = _safe_relative(
            evidence.get("artifact_root"), "token-control canary artifact root"
        )
        raw_artifacts = _mapping(
            evidence.get("artifacts"), "token-control canary evidence artifacts"
        )
        freeze_descriptor = _mapping(
            raw_artifacts.get("freeze_check"),
            "token-control canary production freeze artifact",
        )
        if set(freeze_descriptor) != {"path", "sha256"}:
            raise ReportError(
                "token-control canary production freeze artifact schema is invalid"
            )
        artifact_relative = _safe_relative(
            freeze_descriptor.get("path"),
            "token-control canary production freeze artifact",
        )
        artifact_root_path = _inside(
            project_root,
            project_root / artifact_root,
            "token-control canary artifact root",
        )
        artifact_path_raw = artifact_root_path / artifact_relative
        if artifact_path_raw.is_symlink():
            raise ReportError(
                "token-control canary production freeze artifact must not be a symlink"
            )
        artifact_path = _inside(
            artifact_root_path,
            artifact_path_raw,
            "token-control canary production freeze artifact",
        )
        if (
            not artifact_path.is_file()
            or file_sha256(artifact_path)
            != _hex(
                freeze_descriptor.get("sha256"),
                "token-control canary production freeze artifact digest",
            )
        ):
            raise ReportError(
                "token-control canary production freeze artifact is unauthenticated"
            )
        production_freeze = read_json(artifact_path)
        if production_freeze.get("prompt_protocol") != dict(prompt_protocol):
            raise ReportError(
                "token-control canary production prompt protocol is stale"
            )
        if production_freeze.get("execution_components") != dict(
            execution_components
        ):
            raise ReportError(
                "token-control canary production execution components are stale"
            )
    else:
        summary["prompt_release"] = _ultra_canary_prompt_release_summary(
            summary.get("prompt_release")
        )
        dependency = _mapping(
            summary.get("dependency_audit"), "Ultra canary dependency audit"
        )
        projection = _mapping(
            summary.get("accounting_projection"),
            "Ultra canary accounting projection",
        )
        calls, fork_sets = _validate_fork_policy_projection(
            projection, "Ultra canary"
        )
        if (
            projection.get("accounting_projection_schema_version")
            != ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
            or projection.get("provider_gate_protocol")
            != runner.PROVIDER_GATE_PROTOCOL
            or projection.get("provider_gate_record_sha256")
            != gate_authentication.get("record_sha256")
            or projection.get("provider_gate_close_reason")
            != "accepted_submission"
            or projection.get("provider_gate_response_ids")
            != gate_authentication.get("response_ids")
            or projection.get("provider_gate_deliveries_reconciled")
            is not True
            or projection.get("provider_gate_setup_requests_empty") is not True
            or projection.get("provider_requests_quiescent") is not True
            or projection.get("adapter_teardown_complete") is not True
            or len(fork_sets["resolved"]) != 1
            or len(fork_sets["blocked"]) != 2
            or fork_sets["failed"] != fork_sets["blocked"]
            or fork_sets["raw"]
            != fork_sets["resolved"] | fork_sets["blocked"]
            or type(summary.get("response_count")) is not int
            or type(summary.get("total_model_tokens")) is not int
            or summary.get("response_count")
            != gate_authentication.get("response_count")
            or summary.get("total_model_tokens")
            != gate_authentication.get("completed_tokens")
        ):
            raise ReportError("Ultra canary has the wrong projection-v6 topology")
        try:
            construction_report._validate_canary_projection_provider_reconciliation(
                projection, canary_runner_record, gate_authentication, name
            )
        except construction_report.ReportError as error:
            raise ReportError(
                f"{name} projection provider reconciliation failed: {error}"
            ) from error
        allowed = calls[next(iter(fork_sets["resolved"]))]
        blocked = [calls[call_id] for call_id in sorted(fork_sets["blocked"])]
        child_ids = _fork_identifier_set(
            projection.get("inference_child_thread_ids"),
            "Ultra canary inference child IDs",
        )
        root_id = allowed.get("parent_thread_id")
        if (
            len(child_ids) != 1
            or allowed.get("fork_turns") != "all"
            or not isinstance(root_id, str)
            or {call.get("parent_thread_id") for call in blocked}
            != {root_id, next(iter(child_ids))}
            or any(call.get("fork_turns") != "3" for call in blocked)
        ):
            raise ReportError("Ultra canary did not prove root and child fork3 denial")
        barrier = _mapping(summary.get("barrier"), "Ultra canary barrier")
        _validate_nested_submission_wire(barrier, "Ultra canary barrier")
        _validate_submission_event_order(
            barrier,
            "Ultra canary barrier",
            require_event_timestamps=True,
        )
        if (
            summary.get("status") != "passed"
            or summary.get("drain_complete") is not False
            or summary.get("measurement_exact") is not True
            or summary.get("submission_boundary_exact") is not True
            or not isinstance(summary.get("positive_usage_descendant_thread_count"), int)
            or summary["positive_usage_descendant_thread_count"] <= 0
            or barrier.get("retained_read_only") is not True
            or barrier.get("outer_raw_item_and_call_ids_pairwise_distinct") is not True
            or barrier.get("inner_dynamic_item_started") is not True
            or barrier.get("inner_submit_invocation_exact") is not True
            or barrier.get("inner_submit_only_nested_tool_call") is not True
            or dependency.get("complete") is not True
            or HEX64.fullmatch(str(dependency.get("helper_sha256"))) is None
            or HEX64.fullmatch(str(dependency.get("command_sha256"))) is None
            or dependency.get("library_use") is not False
            or dependency.get("library_declarations") != []
            or dependency.get("target_seen") is not True
            or dependency.get("semantic_type_equal") is not True
        ):
            raise ReportError(
                "Ultra orchestration canary lacks its canonical nested blocked boundary or production dependency audit"
            )
    summary["artifact_count"] = len(artifacts)
    return summary


def _construction_check(
    benchmark_root: Path, manifest: Mapping[str, Any]
) -> dict[str, Any]:
    path = benchmark_root / "metadata" / "evidence" / "construction_validation_full_current.json"
    certificate = read_json(path)
    certificate_sha = file_sha256(path)
    summary = _mapping(certificate.get("summary"), "construction summary")
    expected_summary = {
        "expected": EXPECTED_CONSTRUCTION_RESULTS,
        "checked": EXPECTED_CONSTRUCTION_RESULTS,
        "passed": EXPECTED_CONSTRUCTION_RESULTS,
        "condition_n_passed": EXPECTED_CONSTRUCTION_RESULTS // 2,
        "condition_l_passed": EXPECTED_CONSTRUCTION_RESULTS // 2,
    }
    if (
        certificate.get("schema_version") != 1
        or certificate.get("kind") != "highambench-private-construction-check"
        or certificate.get("pass") is not True
        or certificate.get("record_status") != "current_final"
        or any(summary.get(field) != wanted for field, wanted in expected_summary.items())
    ):
        raise ReportError("construction certificate is not current final 120/120 evidence")
    results = _list(certificate.get("results"), "construction results")
    if len(results) != EXPECTED_CONSTRUCTION_RESULTS:
        raise ReportError("construction certificate does not contain exactly 120 results")
    manifest_path = benchmark_root / "metadata" / "manifest.json"
    manifest_sha = file_sha256(manifest_path)
    manifest_task_data: dict[str, dict[str, str]] = {}
    manifest_papers: list[str] = []
    for raw_paper in _list(manifest.get("papers"), "manifest papers"):
        paper = _mapping(raw_paper, "manifest paper")
        paper_id = str(paper.get("paper_id"))
        manifest_papers.append(paper_id)
        for raw_target in _list(paper.get("targets"), f"manifest {paper_id} targets"):
            target = _mapping(raw_target, "manifest target")
            task_id = str(target.get("task_id"))
            lean = _mapping(target.get("lean_target"), f"manifest target {task_id}")
            if task_id in manifest_task_data:
                raise ReportError("manifest repeats a construction task")
            manifest_task_data[task_id] = {
                "paper_id": paper_id,
                "tier": str(target.get("tier")),
                "target_theorem": f"HighamBench.{lean.get('declaration')}",
            }
    manifest_tasks = set(manifest_task_data)
    wanted = {(task, condition) for task in manifest_tasks for condition in EXPECTED_CONDITIONS}
    if len(manifest_tasks) != 60 or len(manifest_papers) != 20 or len(set(manifest_papers)) != 20:
        raise ReportError("construction certificate requires the exact 20-paper/60-task manifest")

    scope = _mapping(certificate.get("scope"), "construction scope")
    if (
        scope.get("central_manifest") != "metadata/manifest.json"
        or scope.get("central_manifest_sha256") != manifest_sha
        or scope.get("complete_manifest_scope") is not True
        or scope.get("manifest_available_task_ids") != sorted(manifest_tasks)
        or scope.get("selected_task_ids") != sorted(manifest_tasks)
        or scope.get("manifest_paper_ids") != manifest_papers
        or scope.get("selected_paper_ids") != manifest_papers
    ):
        raise ReportError("construction scope is not bound to the complete current manifest")
    execution = _mapping(certificate.get("execution"), "construction execution")
    if (
        _integer(execution.get("jobs"), "construction jobs", positive=True) <= 0
        or execution.get("result_order") != "central manifest order, N then L per task"
    ):
        raise ReportError("construction execution metadata is incomplete")
    isolation = _mapping(certificate.get("isolation"), "construction isolation")
    required_isolation = {
        "condition_l_numstability_mounts_configured": True,
        "condition_n_numstability_mounts_configured": False,
        "condition_n_preflight_after_complete_controlled_staging": True,
        "controlled_task_staged_under": "task/",
        "fresh_workspace_per_result": True,
        "private_gold_staged_as": "Submission.lean",
        "private_helper_oleans_reused": False,
        "validator_hidden_rebuild": True,
    }
    if any(isolation.get(field) != value for field, value in required_isolation.items()):
        raise ReportError("construction certificate lacks its hidden/isolation controls")

    basis = _mapping(certificate.get("verification_basis"), "construction verification basis")
    tools = _mapping(basis.get("tools"), "construction tools")
    required_tools = {
        "tools/check_construction.py",
        "tools/common.py",
        "tools/dependency_audit.lean",
        "tools/hashes.py",
        "tools/lean_isolated.py",
        "tools/preflight.py",
        "tools/validator.py",
    }
    if set(tools) != required_tools:
        raise ReportError("construction certificate has the wrong validator tool set")
    for relative, raw_digest in tools.items():
        tool_path = _inside(benchmark_root, benchmark_root / relative, f"construction tool {relative}")
        if not tool_path.is_file() or file_sha256(tool_path) != _hex(
            raw_digest, f"construction tool {relative} digest"
        ):
            raise ReportError(f"construction tool changed after certification: {relative}")
    for label, required_flags in (
        (
            "numstability_compiled",
            {"exact_tree": True, "only_numstability_namespace": True},
        ),
        ("numstability_source", {"exact_tree": True}),
        (
            "packages_runtime",
            {
                "exact_tree": True,
                "only_mathlib_source_and_lean_compiled_artifacts": True,
            },
        ),
    ):
        descriptor = _mapping(basis.get(label), f"construction {label}")
        descriptor_path = _resolve_frozen_path(
            benchmark_root, descriptor.get("path"), f"construction {label} descriptor"
        )
        if file_sha256(descriptor_path) != _hex(
            descriptor.get("sha256"), f"construction {label} descriptor digest"
        ):
            raise ReportError(f"construction {label} descriptor changed")
        if any(descriptor.get(field) != value for field, value in required_flags.items()):
            raise ReportError(f"construction {label} did not verify an exact frozen tree")
        if (
            _integer(descriptor.get("file_count"), f"construction {label} file count", positive=True)
            != _integer(descriptor.get("verified"), f"construction {label} verified", positive=True)
        ):
            raise ReportError(f"construction {label} verification count is incomplete")
    packages = _mapping(basis.get("packages_runtime"), "construction packages runtime")
    absence = _mapping(packages.get("condition_n_absence_scan"), "construction package absence scan")
    if (
        absence.get("ok") is not True
        or absence.get("complete") is not True
        or absence.get("matches") != []
        or _integer(absence.get("files_scanned"), "construction package scan count", positive=True)
        != packages.get("file_count")
    ):
        raise ReportError("construction packages did not pass the complete condition-N scan")
    shared = _mapping(basis.get("shared_olean"), "construction shared olean")
    bundles = _mapping(shared.get("bundles"), "construction shared olean bundles")
    if set(bundles) != set(manifest_papers) or shared.get("exact_file_count") != 40:
        raise ReportError("construction shared-olean scope is incomplete")
    for paper_id, raw_bundle in bundles.items():
        bundle = _mapping(raw_bundle, f"construction shared bundle {paper_id}")
        expected_names = {
            "HighamBench/Core.olean",
            f"HighamBench/{paper_id}Definitions.olean",
        }
        if set(bundle) != expected_names:
            raise ReportError(f"construction shared bundle {paper_id} has the wrong files")
        for name, digest in bundle.items():
            _hex(digest, f"construction shared bundle {paper_id} {name}")
    shared_absence = _mapping(
        shared.get("condition_n_absence_scan"), "construction shared absence scan"
    )
    if (
        shared_absence.get("ok") is not True
        or shared_absence.get("complete") is not True
        or shared_absence.get("matches") != []
        or shared_absence.get("files_scanned") != shared.get("exact_file_count")
    ):
        raise ReportError("construction shared files did not pass the condition-N scan")
    executables = _mapping(basis.get("executables"), "construction executables")
    if set(executables) != {"bubblewrap", "python"}:
        raise ReportError("construction executable identity is incomplete")
    for label, raw in executables.items():
        entry = _mapping(raw, f"construction executable {label}")
        _hex(entry.get("sha256"), f"construction executable {label} digest")
        if not isinstance(entry.get("path"), str) or not entry["path"]:
            raise ReportError(f"construction executable {label} has no path")

    observed: set[tuple[str, str]] = set()
    l_library_use = 0
    n_preflight_count = 0
    for raw in results:
        result = _mapping(raw, "construction result")
        identity = (str(result.get("task_id")), str(result.get("condition")))
        task_id, condition = identity
        task = manifest_task_data.get(task_id)
        controlled_path = benchmark_root / "metadata" / "controlled" / f"{task_id}.json"
        if (
            identity in observed
            or task is None
            or result.get("pass") is not True
            or result.get("paper_id") != task["paper_id"]
            or result.get("tier") != task["tier"]
            or result.get("target_theorem") != task["target_theorem"]
            or result.get("manifest_sha256") != file_sha256(controlled_path)
            or not controlled_path.is_file()
            or result.get("reasons") != []
        ):
            raise ReportError("construction certificate has a duplicate or failed result")
        observed.add(identity)
        _hex(result.get("gold_source_sha256"), f"construction gold proof {task_id} {condition}")
        helpers = _list(result.get("helpers"), f"construction helpers {task_id} {condition}")
        for helper_raw in helpers:
            helper = _mapping(helper_raw, f"construction helper {task_id} {condition}")
            build = _mapping(helper.get("build"), f"construction helper build {task_id} {condition}")
            if (
                not isinstance(helper.get("module"), str)
                or not isinstance(helper.get("path"), str)
                or _hex(helper.get("source_sha256"), "construction helper source") is None
                or build.get("exit_code") != 0
                or build.get("olean_created") is not True
                or build.get("timed_out") is not False
                or build.get("system_error") is not None
            ):
                raise ReportError(f"construction helper failed for {task_id}/{condition}")
        validation = _mapping(result.get("validation"), f"construction validation {task_id}/{condition}")
        required_validation = {
            "compile_exit_code": 0,
            "compile_timed_out": False,
            "controlled_after_audit_ok": True,
            "controlled_after_compile_ok": True,
            "controlled_after_expected_compile_ok": True,
            "controlled_before_ok": True,
            "controlled_hidden_ok": True,
            "failure_code": None,
            "pass": True,
            "semantic_statement_equal": True,
            "statement_unchanged": True,
            "static_finding_count": 0,
        }
        if any(validation.get(field) != value for field, value in required_validation.items()):
            raise ReportError(f"construction hidden validation is incomplete for {task_id}/{condition}")
        if not isinstance(validation.get("note"), str) or not validation["note"].strip():
            raise ReportError(f"construction validation has no note for {task_id}/{condition}")
        dependency = _mapping(
            validation.get("dependency_audit"),
            f"construction dependency audit {task_id}/{condition}",
        )
        semantic = _mapping(
            dependency.get("semantic_type_check"),
            f"construction semantic check {task_id}/{condition}",
        )
        declarations = _list(
            dependency.get("library_declarations"),
            f"construction library declarations {task_id}/{condition}",
        )
        if (
            dependency.get("complete") is not True
            or dependency.get("exit_code") != 0
            or dependency.get("format_version") != 2
            or dependency.get("forbidden_dependency_count") != 0
            or dependency.get("missing_helper_modules") != []
            or semantic.get("candidate") != task["target_theorem"]
            or semantic.get("equal") is not True
            or not isinstance(semantic.get("expected"), str)
            or not semantic["expected"]
        ):
            raise ReportError(f"construction dependency/statement audit failed for {task_id}/{condition}")
        if condition == "N":
            preflight = _mapping(result.get("n_preflight"), f"construction N preflight {task_id}")
            controlled = _mapping(
                preflight.get("controlled_files_verified_after_staging"),
                f"construction controlled staging {task_id}",
            )
            probe = _mapping(preflight.get("import_probe"), f"construction N import probe {task_id}")
            if (
                result.get("condition_n_library_arguments_omitted") is not True
                or preflight.get("ok") is not True
                or preflight.get("complete") is not True
                or preflight.get("controlled_manifest_sha256") != result.get("manifest_sha256")
                or preflight.get("filesystem_leaks") != []
                or controlled.get("ok") is not True
                or controlled.get("changed") != []
                or controlled.get("missing") != []
                or controlled.get("verified") != controlled.get("expected")
                or probe.get("attempted") is not True
                or probe.get("reliable") is not True
                or probe.get("importable") is not False
                or probe.get("timed_out") is not False
                or probe.get("system_error") is not None
                or dependency.get("library_use") is not False
                or declarations != []
            ):
                raise ReportError(f"construction condition-N isolation failed for {task_id}")
            n_preflight_count += 1
        else:
            if (
                result.get("condition_n_library_arguments_omitted") is not False
                or result.get("n_preflight") is not None
                or dependency.get("library_use") is not True
                or not declarations
            ):
                raise ReportError(f"construction condition-L dependency audit failed for {task_id}")
            for declaration_raw in declarations:
                declaration = _mapping(
                    declaration_raw, f"construction library declaration {task_id}"
                )
                name = declaration.get("name")
                if not isinstance(name, str) or "NumStability" not in name:
                    raise ReportError(f"construction result {task_id}/L has a non-library declaration")
            l_library_use += 1
    if observed != wanted or len(wanted) != EXPECTED_CONSTRUCTION_RESULTS:
        raise ReportError("construction certificate scope is not the complete 60-task N/L matrix")
    if n_preflight_count != 60 or l_library_use != 60:
        raise ReportError("construction certificate does not certify all N preflights and L dependencies")

    pointer_summaries: list[dict[str, Any]] = []
    pointer_expectations = {
        "condition_n_preflight.json": {
            "kind": "highambench-condition-n-preflight-evidence-pointer",
            "counts": {
                "condition_n_tasks_checked": 60,
                "complete_staged_task_scans_passed": 60,
                "reliable_failed_import_probes": 60,
                "filesystem_leaks": 0,
            },
        },
        "library_dependency_probe.json": {
            "kind": "highambench-library-dependency-evidence-pointer",
            "counts": {
                "proofs_checked": 120,
                "proofs_passed": 120,
                "condition_n_library_use": False,
                "condition_l_passed_proofs_using_numstability": 60,
                "dependency_audit_format": 2,
                "forbidden_dependencies": 0,
            },
        },
    }
    for filename, expected in pointer_expectations.items():
        pointer_path = path.parent / filename
        pointer = read_json(pointer_path)
        if (
            pointer.get("kind") != expected["kind"]
            or pointer.get("status") != "current complete-corpus construction evidence"
            or pointer.get("current_evidence")
            != "paper_bencmark/highambench/metadata/evidence/construction_validation_full_current.json"
            or pointer.get("current_evidence_sha256") != certificate_sha
            or pointer.get("current_result") != expected["counts"]
        ):
            raise ReportError(f"construction evidence pointer is stale: {filename}")
        pointer_summaries.append(
            {
                "path": pointer_path.relative_to(benchmark_root).as_posix(),
                "sha256": file_sha256(pointer_path),
            }
        )
    p02 = sorted(
        f"{task}/{condition}"
        for task, condition in observed
        if task in {"P02-T1", "P02-T2", "P02-T3"}
    )
    if p02 != sorted(
        f"P02-T{tier}/{condition}"
        for tier in (1, 2, 3)
        for condition in EXPECTED_CONDITIONS
    ):
        raise ReportError("P02 T1/T2/T3 construction proof coverage is incomplete")
    return {
        "path": path.relative_to(benchmark_root).as_posix(),
        "sha256": certificate_sha,
        **expected_summary,
        "condition_n_preflights": n_preflight_count,
        "condition_l_library_dependencies": l_library_use,
        "p02_construction_task_conditions": p02,
        "p02_measurement_records": 0,
        "evidence_pointers": pointer_summaries,
    }


def _review_check(
    benchmark_root: Path,
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
) -> dict[str, Any]:
    """Authenticate both fresh-context Codex reviews and the private override."""

    override = _mapping(
        config.get("private_measurement_review_override"),
        "private measurement review override",
    )
    if (
        override.get("enabled") is not True
        or override.get("fresh_context_reviews_required") is not True
        or override.get("source_fidelity_required") is not True
        or override.get("scope") != "exact-target novelty rejections only"
    ):
        raise ReportError("the private novelty override is absent or broader than allowed")
    ignored = override.get("ignored_rejection_task_ids")
    if not isinstance(ignored, list) or len(ignored) != 13 or len(set(ignored)) != 13:
        raise ReportError("private novelty override does not identify exactly 13 retained collisions")
    descriptors = _list(override.get("review_records"), "fresh-context review records")
    if len(descriptors) != 2:
        raise ReportError("exactly two independent fresh-context reviews are required")
    manifest_sha = file_sha256(benchmark_root / "metadata" / "manifest.json")
    expected_task_ids = {
        str(target.get("task_id"))
        for paper in _list(manifest.get("papers"), "manifest papers")
        for target in _list(_mapping(paper, "manifest paper").get("targets"), "paper targets")
        if isinstance(target, Mapping)
    }
    if len(expected_task_ids) != 60:
        raise ReportError("fresh reviews require the exact 60-task manifest")
    descriptor_paths = [str(_mapping(raw, "review descriptor").get("path")) for raw in descriptors]
    descriptor_hashes = [str(_mapping(raw, "review descriptor").get("sha256")) for raw in descriptors]
    if len(set(descriptor_paths)) != 2 or len(set(descriptor_hashes)) != 2:
        raise ReportError("fresh-context review descriptors are not distinct")
    summaries: list[dict[str, Any]] = []
    reviewer_ids: set[str] = set()
    for index, raw in enumerate(descriptors):
        descriptor = _mapping(raw, f"review descriptor {index}")
        if (
            descriptor.get("task_count") != 60
            or descriptor.get("record_status") != "current_with_blocking_defects"
        ):
            raise ReportError("review descriptor does not cover all 60 tasks")
        path = _resolve_frozen_path(
            benchmark_root, descriptor.get("path"), f"review descriptor {index}"
        )
        digest = file_sha256(path)
        if digest != _hex(descriptor.get("sha256"), f"review descriptor {index} digest"):
            raise ReportError("fresh-context review hash does not match the configured descriptor")
        review = read_json(path)
        reviewer = _mapping(review.get("reviewer"), f"reviewer in {path.name}")
        identity_text = " ".join(str(value) for value in reviewer.values()).lower()
        if reviewer.get("fresh_context") is not True or not (
            "codex" in identity_text or "non-human" in identity_text
        ):
            raise ReportError(f"{path.name} is not a fresh-context Codex-agent review")
        reviewer_id = reviewer.get("id")
        if not isinstance(reviewer_id, str) or not reviewer_id or reviewer_id in reviewer_ids:
            raise ReportError("fresh-context reviews do not have distinct reviewer IDs")
        reviewer_ids.add(reviewer_id)
        if review.get("benchmark_manifest_sha256") != manifest_sha:
            raise ReportError(f"{path.name} reviewed a different manifest")
        task_reviews = _list(review.get("task_reviews"), f"task reviews in {path.name}")
        task_ids = [item.get("task_id") for item in task_reviews if isinstance(item, Mapping)]
        if (
            len(task_reviews) != 60
            or len(set(task_ids)) != 60
            or set(task_ids) != expected_task_ids
        ):
            raise ReportError(f"{path.name} does not contain the exact 60-task review set")
        source_faithful = sum(
            item.get("source_faithful") is True
            for item in task_reviews
            if isinstance(item, Mapping)
        )
        collisions = sorted(
            str(item.get("task_id"))
            for item in task_reviews
            if isinstance(item, Mapping)
            and (
                item.get("novelty") is False
                or item.get("exact_target_novel") is False
                or "collision" in str(item.get("novelty_decision", ""))
                or "collision" in str(item.get("decision", ""))
            )
        )
        # The formal review stores the same facts in a normalized summary even
        # when its individual records use nested novelty_evidence.
        summary = _mapping(review.get("summary"), f"review summary in {path.name}")
        summary_source = summary.get("source_faithful")
        if summary_source is None:
            summary_source = summary.get("source_faithful_count")
        summary_novel = summary.get("exact_target_novel")
        if summary_novel is None:
            summary_novel = summary.get("exact_target_absent_from_both_count")
        summary_collisions = summary.get("exact_target_collisions")
        if summary_collisions is None:
            summary_collisions = summary.get("exact_target_collision_count")
        summary_collision_ids = summary.get("collision_task_ids")
        if summary_collision_ids is None:
            summary_collision_ids = summary.get("retained_novelty_rejections")
        if (
            source_faithful != 60
            or summary_source != 60
            or summary_novel != 47
            or summary_collisions != 13
            or sorted(summary_collision_ids or []) != sorted(ignored)
        ):
            raise ReportError(f"{path.name} does not certify 60/60 fidelity and 47/13 novelty")
        if collisions and collisions != sorted(ignored):
            raise ReportError(f"{path.name} task decisions disagree with the retained collisions")
        if review.get("overall_decision") != "fail_exact_target_novelty":
            raise ReportError(f"{path.name} does not retain the collision rejections")
        if review.get("public_release") not in (None, False) or review.get(
            "release_approval"
        ) not in (None, False):
            raise ReportError(f"{path.name} improperly approves public release")
        summaries.append(
            {
                "path": str(descriptor.get("path")),
                "sha256": digest,
                "reviewer_id": reviewer_id,
                "source_faithful": 60,
                "exact_target_novel": 47,
                "retained_collisions": 13,
            }
        )
    return {
        "public_release": False,
        "override_scope": override.get("scope"),
        "source_faithful": 60,
        "exact_target_novel": 47,
        "retained_collisions": 13,
        "collision_task_ids": sorted(ignored),
        "reviews": summaries,
    }


def _manifest_tasks(
    benchmark_root: Path, manifest: Mapping[str, Any]
) -> dict[str, dict[str, Any]]:
    tasks: dict[str, dict[str, Any]] = {}
    papers = _list(manifest.get("papers"), "manifest papers")
    for paper_raw in papers:
        paper = _mapping(paper_raw, "manifest paper")
        paper_id = paper.get("paper_id")
        source = _mapping(paper.get("source"), f"paper {paper_id} source")
        paper_sha = _hex(source.get("sha256"), f"paper {paper_id} digest")
        for target_raw in _list(paper.get("targets"), f"paper {paper_id} targets"):
            target = _mapping(target_raw, "manifest target")
            task_id = target.get("task_id")
            if not isinstance(task_id, str) or task_id in tasks:
                raise ReportError("manifest has an invalid or duplicate task ID")
            lean = _mapping(target.get("lean_target"), f"target {task_id}")
            target_path = _resolve_frozen_path(
                benchmark_root, lean.get("file"), f"target {task_id}"
            )
            target_sha = _hex(lean.get("controlled_file_sha256"), f"target {task_id} digest")
            if file_sha256(target_path) != target_sha:
                raise ReportError(f"target {task_id} has changed since the manifest freeze")
            tasks[task_id] = {
                "task_id": task_id,
                "paper_id": paper_id,
                "paper_sha256": paper_sha,
                "tier": target.get("tier"),
                "title": target.get("title", task_id),
                "target_file": target_path,
                "target_sha256": target_sha,
                "declaration": lean.get("declaration"),
            }
    if set(task for task in tasks if tasks[task]["paper_id"] == EXPECTED_PAPER) != set(EXPECTED_TASKS):
        raise ReportError("current manifest does not have exactly P01-T1, P01-T2, and P01-T3")
    return tasks


def _expected_assignments(
    config: Mapping[str, Any], run_order: Mapping[str, Any], tasks: Mapping[str, Mapping[str, Any]]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    repetitions_raw = _list(config.get("repetitions"), "config repetitions")
    repetitions: dict[str, Any] = {}
    for raw in repetitions_raw:
        item = _mapping(raw, "repetition")
        repetition = item.get("id")
        if not isinstance(repetition, str) or repetition in repetitions:
            raise ReportError("config has an invalid or repeated repetition")
        if set(item) != {"id", "backend_seed"} or item.get("backend_seed") is not None:
            raise ReportError(
                "the frozen repetitions must explicitly record backend_seed=null"
            )
        repetitions[repetition] = None
    if tuple(repetitions) != EXPECTED_REPETITIONS:
        raise ReportError("P01 checkpoint requires exactly rep-01, rep-02, and rep-03")
    method = _mapping(run_order.get("method"), "run-order method")
    salt = method.get("salt")
    if method.get("name") != "sha256_first_byte_parity" or not isinstance(salt, str) or not salt:
        raise ReportError("run order does not use the frozen SHA-256 parity rule")
    expected_all: list[dict[str, Any]] = []
    seen_assignments: set[tuple[str, str, str]] = set()
    seen_ids: set[str] = set()
    for raw in _list(run_order.get("pairs"), "run-order pairs"):
        pair = _mapping(raw, "run-order pair")
        pair_id = pair.get("pair_id")
        task_id = pair.get("task_id")
        repetition = pair.get("repetition_id")
        order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if task_id not in tasks or repetition not in repetitions:
            raise ReportError(f"run-order pair {pair_id!r} names an unknown assignment")
        if order not in (["N", "L"], ["L", "N"]):
            raise ReportError(f"run-order pair {pair_id!r} has an invalid condition order")
        if not isinstance(run_ids, list) or len(run_ids) != 2 or not all(
            isinstance(item, str) and item for item in run_ids
        ):
            raise ReportError(f"run-order pair {pair_id!r} has invalid run IDs")
        digest = hashlib.sha256(f"{salt}|{task_id}|{repetition}".encode()).hexdigest()
        wanted_order = ["N", "L"] if int(digest[:2], 16) % 2 == 0 else ["L", "N"]
        if pair.get("sha256") != digest or order != wanted_order:
            raise ReportError(f"run-order pair {pair_id!r} fails its deterministic hash rule")
        for index, condition in enumerate(order):
            identity = (str(task_id), str(repetition), condition)
            if identity in seen_assignments or run_ids[index] in seen_ids:
                raise ReportError("run order repeats an assignment or run ID")
            seen_assignments.add(identity)
            seen_ids.add(run_ids[index])
            expected_all.append(
                {
                    "pair_id": pair_id,
                    "task_id": task_id,
                    "repetition_id": repetition,
                    "condition": condition,
                    "condition_order": list(order),
                    "pair_order": "N-first" if order[0] == "N" else "L-first",
                    "run_id": run_ids[index],
                    "order_index": index + 1,
                    "backend_seed": repetitions[repetition],
                }
            )
    wanted_all = {
        (task_id, repetition, condition)
        for task_id in tasks
        for repetition in repetitions
        for condition in EXPECTED_CONDITIONS
    }
    if seen_assignments != wanted_all:
        raise ReportError("run order is not the complete frozen task matrix")
    p01 = [item for item in expected_all if tasks[str(item["task_id"])]["paper_id"] == EXPECTED_PAPER]
    if len(p01) != EXPECTED_FINAL_RUNS:
        raise ReportError("run order does not contain exactly 18 P01 assignments")
    return expected_all, p01


def _prompt_source(benchmark_root: Path, descriptor: Mapping[str, Any], label: str) -> tuple[dict[str, Any], str]:
    path = _resolve_frozen_path(benchmark_root, descriptor.get("path"), label)
    payload = path.read_bytes()
    if len(payload) != descriptor.get("bytes") or hashlib.sha256(payload).hexdigest() != descriptor.get("sha256"):
        raise ReportError(f"{label} does not match its frozen prompt descriptor")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ReportError(f"{label} is not UTF-8") from error
    return {
        "path": str(descriptor.get("path")),
        "sha256": descriptor.get("sha256"),
        "bytes": descriptor.get("bytes"),
    }, text


def _specification_check(
    benchmark_root: Path, manifest: Mapping[str, Any]
) -> dict[str, Any]:
    descriptor = _mapping(manifest.get("specification"), "benchmark specification")
    if descriptor.get("version") != "0.2" or descriptor.get("pdf_pages") != 4:
        raise ReportError("manifest does not identify the four-page v0.2 specification")
    path = _resolve_frozen_path(
        benchmark_root, descriptor.get("local_path"), "benchmark specification"
    )
    digest = file_sha256(path)
    if digest != _hex(descriptor.get("sha256"), "benchmark specification digest"):
        raise ReportError("benchmark specification PDF differs from the frozen manifest")
    if not isinstance(descriptor.get("title"), str) or not descriptor["title"].strip():
        raise ReportError("benchmark specification has no title")
    return {
        "path": str(descriptor.get("local_path")),
        "sha256": digest,
        "version": "0.2",
        "pdf_pages": 4,
    }


def _signposted_protocol_check(
    benchmark_root: Path,
    config: Mapping[str, Any],
    environment: Mapping[str, Any],
) -> dict[str, Any]:
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    protocol = _mapping(frozen.get("prompt_protocol"), "prompt protocol")
    if (
        protocol.get("version") != "signposted-library-v1"
        or protocol.get("composition_order")
        != [
            "common_prompt",
            "condition_L_supplement_if_condition_L",
            "task_context",
            "fixed_target",
        ]
        or protocol.get("N_receives_condition_supplement") is not False
        or protocol.get("relevant_theorem_or_module_hints_supplied") is not False
    ):
        raise ReportError("the frozen signposted-library-v1 protocol is malformed")
    supplements = _mapping(protocol.get("condition_supplements"), "condition supplements")
    if set(supplements) != {"L"}:
        raise ReportError("the prompt protocol must contain exactly the L-only supplement")
    common, _common_text = _prompt_source(
        benchmark_root, _mapping(protocol.get("common_prompt"), "common prompt"), "common prompt"
    )
    supplement, supplement_text = _prompt_source(
        benchmark_root, _mapping(supplements.get("L"), "L supplement"), "L supplement"
    )
    lowered = supplement_text.lower()
    required_fragments = (
        "search",
        "numstability",
        "/library/numstability",
        "/library/numstability.lean",
        "/library-olean",
        "rg ",
        "find ",
        "may import and use",
    )
    if any(fragment not in lowered for fragment in required_fragments):
        raise ReportError("the L supplement lacks its frozen search/use instructions or mount paths")
    deviations = _list(
        environment.get("known_reference_protocol_deviations"),
        "known reference protocol deviations",
    )
    matches = [
        item
        for item in deviations
        if isinstance(item, str)
        and all(marker in item for marker in SIGNPOSTED_DEVIATION_MARKERS)
    ]
    if len(matches) != 1:
        raise ReportError(
            "environment does not disclose the user-directed PDF section 3 prompt departure"
        )
    return {
        "version": "signposted-library-v1",
        "common_prompt": common,
        "condition_l_supplement": supplement,
        "condition_n_receives_supplement": False,
        "library_source_path": "/library/NumStability",
        "library_root_path": "/library/NumStability.lean",
        "library_compiled_path": "/library-olean",
        "search_encouraged": True,
        "relevant_theorem_or_module_hints_supplied": False,
        "reference_pdf_section": "3",
        "user_directed_departure": matches[0],
    }


def expected_prompt_provenance(
    benchmark_root: Path,
    config: Mapping[str, Any],
    task: Mapping[str, Any],
    condition: str,
) -> dict[str, Any]:
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    protocol = _mapping(frozen.get("prompt_protocol"), "prompt protocol")
    if (
        protocol.get("version") != "signposted-library-v1"
        or protocol.get("composition_order")
        != [
            "common_prompt",
            "condition_L_supplement_if_condition_L",
            "task_context",
            "fixed_target",
        ]
        or protocol.get("N_receives_condition_supplement") is not False
        or protocol.get("relevant_theorem_or_module_hints_supplied") is not False
    ):
        raise ReportError("P01 report requires the complete frozen signposted-library-v1 protocol")
    common_descriptor, common_text = _prompt_source(
        benchmark_root, _mapping(protocol.get("common_prompt"), "common prompt"), "common prompt"
    )
    supplements = _mapping(protocol.get("condition_supplements"), "condition supplements")
    if set(supplements) != {"L"}:
        raise ReportError("prompt protocol must contain exactly one L-only supplement")
    l_descriptor, l_text = _prompt_source(
        benchmark_root, _mapping(supplements.get("L"), "L supplement"), "L supplement"
    )
    task_id = str(task["task_id"])
    controlled_path = benchmark_root / "metadata" / "controlled" / f"{task_id}.json"
    controlled = read_json(controlled_path)
    entries = {
        str(item.get("path")): item
        for item in _list(controlled.get("files"), f"controlled files for {task_id}")
        if isinstance(item, Mapping)
    }
    target_path = Path(task["target_file"])
    try:
        target_relative = target_path.relative_to(benchmark_root.resolve()).as_posix()
    except ValueError as error:
        raise ReportError(f"target {task_id} is outside the benchmark root") from error
    context_relative = f"tasks/{EXPECTED_PAPER}/{task['tier']}/context.md"
    parts: list[tuple[str, dict[str, Any], str]] = []
    for role, relative in (("task_context", context_relative), ("fixed_target", target_relative)):
        entry = _mapping(entries.get(relative), f"controlled {role} for {task_id}")
        path = _inside(benchmark_root, benchmark_root / relative, f"{task_id} {role}")
        payload = path.read_bytes()
        if len(payload) != entry.get("bytes") or hashlib.sha256(payload).hexdigest() != entry.get("sha256"):
            raise ReportError(f"controlled prompt source changed for {task_id}: {relative}")
        parts.append(
            (
                role,
                {"path": relative, "sha256": entry.get("sha256"), "bytes": entry.get("bytes")},
                payload.decode("utf-8"),
            )
        )
    sections = [common_text.rstrip()]
    selected_supplement: dict[str, Any] | None = None
    if condition == "L":
        sections.append(l_text.rstrip())
        selected_supplement = l_descriptor
    context_descriptor, context_text = parts[0][1], parts[0][2]
    target_descriptor, target_text = parts[1][1], parts[1][2]
    sections.extend(
        (
            "## Task context\n\n" + context_text.rstrip(),
            "## Fixed Lean target\n\n```lean\n" + target_text.rstrip() + "\n```",
        )
    )
    effective = ("\n\n".join(sections) + "\n").encode("utf-8")
    return {
        "protocol_version": "signposted-library-v1",
        "condition": condition,
        "composition_order": [
            "common_prompt",
            "condition_L_supplement_if_condition_L",
            "task_context",
            "fixed_target",
        ],
        "common_prompt": common_descriptor,
        "condition_supplement": selected_supplement,
        "task_context": context_descriptor,
        "fixed_target": target_descriptor,
        "effective_prompt": {
            "sha256": hashlib.sha256(effective).hexdigest(),
            "bytes": len(effective),
            "encoding": "utf-8",
            "composition": "utf8_rstrip_each_section_join_two_newlines_final_newline_v1",
        },
        "authentication": {
            "computed_before_prompt_release": True,
            "frozen_protocol_match": True,
            "controlled_task_sources_match": True,
            "agent_command_match": True,
        },
    }


def _option(command: Any, name: str, label: str) -> str | None:
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        raise ReportError(f"{label} has no auditable agent command")
    positions = [index for index, item in enumerate(command) if item == name]
    if not positions:
        return None
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        raise ReportError(f"{label} has ambiguous command option {name}")
    return command[positions[0] + 1]


def _validate_prompt(
    benchmark_root: Path,
    config: Mapping[str, Any],
    task: Mapping[str, Any],
    run: Mapping[str, Any],
) -> str:
    label = str(run.get("run_id"))
    condition = str(run.get("condition"))
    expected = expected_prompt_provenance(benchmark_root, config, task, condition)
    if run.get("prompt_provenance") != expected:
        raise ReportError(f"{label} has stale or altered effective-prompt provenance")
    command = run.get("agent_command")
    if _option(command, "--condition", label) != condition:
        raise ReportError(f"{label} agent command has the wrong condition")
    prompt_raw = _option(command, "--prompt-file", label)
    context_raw = _option(command, "--context-file", label)
    target_raw = _option(command, "--target-file", label)
    if any(value is None or not Path(str(value)).is_absolute() for value in (prompt_raw, context_raw, target_raw)):
        raise ReportError(f"{label} agent command lacks absolute staged prompt/context/target paths")
    prompt_path = Path(str(prompt_raw)).resolve()
    staged_root = prompt_path.parent
    expected_paths = {
        "common prompt": staged_root / str(expected["common_prompt"]["path"]),
        "task context": staged_root / str(expected["task_context"]["path"]),
        "fixed target": staged_root / str(expected["fixed_target"]["path"]),
    }
    observed_paths = {
        "common prompt": prompt_path,
        "task context": Path(str(context_raw)).resolve(),
        "fixed target": Path(str(target_raw)).resolve(),
    }
    for role, wanted in expected_paths.items():
        if observed_paths[role] != wanted.resolve():
            raise ReportError(f"{label} agent command has the wrong staged {role} path")
    supplement_file = _option(command, "--condition-prompt-file", label)
    supplement_sha = _option(command, "--condition-prompt-sha256", label)
    if condition == "N" and (supplement_file is not None or supplement_sha is not None):
        raise ReportError(f"{label} condition N received the L supplement")
    if condition == "L":
        descriptor = _mapping(expected.get("condition_supplement"), "expected L supplement")
        supplement_path = _resolve_frozen_path(
            benchmark_root, descriptor.get("path"), f"{label} L supplement"
        )
        if (
            supplement_file is None
            or Path(supplement_file).resolve() != supplement_path
            or supplement_sha != descriptor.get("sha256")
        ):
            raise ReportError(f"{label} condition L lacks its authenticated supplement")
    common_path = _resolve_frozen_path(
        benchmark_root, expected["common_prompt"]["path"], f"{label} common prompt"
    )
    context_path = _resolve_frozen_path(
        benchmark_root, expected["task_context"]["path"], f"{label} task context"
    )
    target_path = _resolve_frozen_path(
        benchmark_root, expected["fixed_target"]["path"], f"{label} fixed target"
    )
    condition_path = None
    if condition == "L":
        condition_path = _resolve_frozen_path(
            benchmark_root,
            _mapping(expected["condition_supplement"], "expected L supplement")[
                "path"
            ],
            f"{label} L supplement",
        )
    try:
        effective_prompt = codex_isolated.build_prompt(
            common_path, context_path, target_path, condition_path
        )
    except (OSError, RuntimeError, UnicodeError) as error:
        raise ReportError(f"{label} effective prompt cannot be reconstructed: {error}") from error
    effective_bytes = effective_prompt.encode("utf-8")
    expected_effective = _mapping(expected.get("effective_prompt"), "effective prompt")
    if (
        hashlib.sha256(effective_bytes).hexdigest()
        != expected_effective.get("sha256")
        or len(effective_bytes) != expected_effective.get("bytes")
    ):
        raise ReportError(f"{label} reconstructed effective prompt is stale")
    return effective_prompt


def _validate_matrix_record_authentication(
    run: Mapping[str, Any], label: str
) -> dict[str, Any]:
    attempt = run.get("matrix_attempt")
    recorded = _hex(
        run.get("matrix_record_sha256"), f"{label} matrix-record self-hash"
    )
    unsigned = dict(run)
    unsigned.pop("matrix_record_sha256", None)
    recomputed = document_sha256(unsigned)
    if (
        not isinstance(attempt, int)
        or isinstance(attempt, bool)
        or attempt not in (1, 2)
        or recorded != recomputed
    ):
        raise ReportError(f"{label} has invalid matrix final-record authentication")
    return {
        "matrix_attempt": attempt,
        "matrix_record_sha256": recorded,
        "recomputed_matrix_record_sha256": recomputed,
        "valid": True,
    }


def _prompt_artifact_path(
    results_root: Path, raw: Any, expected: Path, label: str
) -> Path:
    if not isinstance(raw, str) or not raw:
        raise ReportError(f"{label} has no retained path")
    unresolved = Path(raw)
    if not unresolved.is_absolute():
        unresolved = results_root / unresolved
    try:
        details = unresolved.lstat()
    except OSError as error:
        raise ReportError(f"{label} is missing: {error}") from error
    if (
        stat.S_ISLNK(details.st_mode)
        or not stat.S_ISREG(details.st_mode)
        or stat.S_IMODE(details.st_mode) != 0o444
    ):
        raise ReportError(f"{label} is not a sealed 0444 regular non-symlink file")
    path = _inside(results_root, unresolved, label)
    if path != expected.resolve():
        raise ReportError(f"{label} is not the usage-derived prompt artifact")
    return path


def _authenticated_prompt_descriptor(
    results_root: Path,
    descriptor_raw: Any,
    *,
    expected_path: Path,
    expected_common: Mapping[str, Any],
    name: str,
    hash_field: str,
    kind: str,
    variable_fields: set[str],
) -> dict[str, Any]:
    descriptor = _mapping(descriptor_raw, f"{name} descriptor")
    if set(descriptor) != {"path", "file_sha256", "record_sha256", "record"}:
        raise ReportError(f"{name} descriptor has unexpected fields")
    path = _prompt_artifact_path(
        results_root, descriptor.get("path"), expected_path, name
    )
    payload = path.read_bytes()
    if len(payload) > codex_isolated.MAX_PROMPT_HANDSHAKE_BYTES:
        raise ReportError(f"{name} retained file is unexpectedly large")
    record = _mapping(descriptor.get("record"), f"{name} embedded record")
    expected_fields = set(expected_common) | variable_fields | {"kind", hash_field}
    if set(record) != expected_fields or record.get("kind") != kind:
        raise ReportError(f"{name} record has an inexact schema")
    if any(record.get(field) != value for field, value in expected_common.items()):
        raise ReportError(f"{name} record changed its common prompt identity")
    recorded_self_hash = _hex(record.get(hash_field), f"{name} self-hash")
    if (
        descriptor.get("record_sha256") != recorded_self_hash
        or codex_isolated.canonical_record_sha256(record, hash_field)
        != recorded_self_hash
    ):
        raise ReportError(f"{name} record has an invalid canonical self-hash")
    disk = read_json(path)
    canonical_file = canonical_bytes(record) + b"\n"
    if (
        dict(record) != disk
        or payload != canonical_file
        or file_sha256(path)
        != _hex(descriptor.get("file_sha256"), f"{name} file digest")
    ):
        raise ReportError(f"{name} retained file failed exact authentication")
    return dict(record)


def _validate_prompt_release(
    results_root: Path,
    config: Mapping[str, Any],
    run: Mapping[str, Any],
    usage: Mapping[str, Any],
    effective_prompt: str,
    authenticated_boundary: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Independently authenticate the exact READY/GO/RELEASED timing origin."""

    label = str(run.get("run_id"))
    top = _mapping(run.get("prompt_release"), f"{label} prompt release")
    expected_top_fields = {
        "schema_version",
        "protocol_version",
        "required",
        "status",
        "authenticated",
        "timing_exact",
        "useful_work_basis",
        "startup_timeout_seconds",
        "startup_timeout_triggered",
        "go_minimum_release_window_seconds",
        "handshake_nonce",
        "elapsed_clock",
        "artifact_paths",
        "effective_prompt_sha256",
        "effective_prompt_bytes",
        "ready",
        "go",
        "released",
        "stale_artifacts_removed",
        "error",
    }
    limits = _mapping(config.get("limits"), "config limits")
    startup_timeout = _number(
        limits.get("prompt_startup_timeout_seconds"),
        "prompt startup timeout",
    )
    if startup_timeout != 120.0:
        raise ReportError("frozen prompt startup timeout must be exactly 120 seconds")
    encoded_prompt = effective_prompt.encode("utf-8")
    effective_sha = hashlib.sha256(encoded_prompt).hexdigest()
    nonce = _hex(top.get("handshake_nonce"), f"{label} prompt nonce")
    expected_top = {
        "schema_version": codex_isolated.PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
        "required": True,
        "status": "released_authenticated",
        "authenticated": True,
        "timing_exact": True,
        "useful_work_basis": "authenticated_release",
        "startup_timeout_seconds": startup_timeout,
        "startup_timeout_triggered": False,
        "go_minimum_release_window_seconds": runner.PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "effective_prompt_sha256": effective_sha,
        "effective_prompt_bytes": len(encoded_prompt),
        "error": None,
    }
    if set(top) != expected_top_fields or any(
        top.get(field) != value for field, value in expected_top.items()
    ):
        raise ReportError(f"{label} has an inexact authenticated prompt-release summary")
    stale = top.get("stale_artifacts_removed")
    if (
        not isinstance(stale, list)
        or stale != sorted(set(stale))
        or any(not isinstance(item, str) or not Path(item).is_absolute() for item in stale)
    ):
        raise ReportError(f"{label} has invalid stale prompt-artifact evidence")
    for item in stale:
        candidate = Path(item)
        try:
            candidate.parent.resolve().relative_to(results_root.resolve())
        except ValueError as error:
            raise ReportError(f"{label} stale prompt artifact escapes results") from error

    command = run.get("agent_command")
    usage_raw = _option(command, "--usage-output", label)
    if usage_raw is None or not Path(usage_raw).is_absolute():
        raise ReportError(f"{label} has no absolute trusted usage-output command path")
    usage_path = _inside(results_root, Path(usage_raw), f"{label} usage output")
    expected_paths = codex_isolated.prompt_handshake_paths(usage_path)
    path_summary = _mapping(top.get("artifact_paths"), f"{label} prompt artifact paths")
    if set(path_summary) != {"ready", "go", "release"}:
        raise ReportError(f"{label} prompt artifact-path set is incomplete")
    for name, option in (
        ("ready", "--prompt-ready-output"),
        ("go", "--prompt-go-input"),
        ("release", "--prompt-release-output"),
    ):
        raw = _option(command, option, label)
        if (
            raw is None
            or path_summary.get(name) != raw
            or Path(raw) != expected_paths[name]
        ):
            raise ReportError(f"{label} {name} prompt artifact is not command/usage bound")
    if (
        _option(command, "--prompt-handshake-nonce", label) != nonce
        or _option(command, "--prompt-run-id", label) != label
    ):
        raise ReportError(f"{label} prompt handshake command identity is stale")

    root_thread_id = usage.get("root_thread_id")
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise ReportError(f"{label} prompt release has no rooted usage ledger")
    agent = _mapping(run.get("agent"), f"{label} agent")
    common = {
        "schema_version": codex_isolated.PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
        "handshake_nonce": nonce,
        "run_id": label,
        "condition": run.get("condition"),
        "model": agent.get("model"),
        "reasoning_effort": agent.get("reasoning_effort"),
        "root_thread_id": root_thread_id,
        "turn_start_request_id": codex_isolated.TURN_START_REQUEST_ID,
        "effective_prompt_sha256": effective_sha,
        "effective_prompt_bytes": len(encoded_prompt),
        "adapter_name": codex_isolated.PROMPT_RELEASE_ADAPTER_NAME,
        "adapter_version": codex_isolated.PROMPT_RELEASE_ADAPTER_VERSION,
        "app_server_client_name": codex_isolated.APP_SERVER_CLIENT_NAME,
        "app_server_client_version": codex_isolated.APP_SERVER_CLIENT_VERSION,
        "elapsed_clock": "CLOCK_MONOTONIC",
    }
    ready = _authenticated_prompt_descriptor(
        results_root,
        top.get("ready"),
        expected_path=expected_paths["ready"],
        expected_common=common,
        name=f"{label} prompt READY",
        hash_field="ready_sha256",
        kind=codex_isolated.PROMPT_READY_KIND,
        variable_fields={
            "turn_start_write_state",
            "ready_at_monotonic_ns",
            "ready_at_unix_ns",
        },
    )
    go = _authenticated_prompt_descriptor(
        results_root,
        top.get("go"),
        expected_path=expected_paths["go"],
        expected_common=common,
        name=f"{label} prompt GO",
        hash_field="go_sha256",
        kind=codex_isolated.PROMPT_GO_KIND,
        variable_fields={
            "ready_sha256",
            "turn_start_write_authorized",
            "authorized_at_monotonic_ns",
            "authorized_at_unix_ns",
        },
    )
    released = _authenticated_prompt_descriptor(
        results_root,
        top.get("released"),
        expected_path=expected_paths["release"],
        expected_common=common,
        name=f"{label} prompt RELEASED",
        hash_field="release_sha256",
        kind=codex_isolated.PROMPT_RELEASED_KIND,
        variable_fields={
            "ready_sha256",
            "go_sha256",
            "turn_start_write_state",
            "timestamp_capture_point",
            "turn_start_request_sha256",
            "turn_start_request_bytes",
            "released_at_monotonic_ns",
            "released_at_unix_ns",
            "turn_start_flushed_at_monotonic_ns",
            "turn_start_flushed_at_unix_ns",
        },
    )
    timestamps = (
        ready.get("ready_at_monotonic_ns"),
        ready.get("ready_at_unix_ns"),
        go.get("authorized_at_monotonic_ns"),
        go.get("authorized_at_unix_ns"),
        released.get("released_at_monotonic_ns"),
        released.get("released_at_unix_ns"),
        released.get("turn_start_flushed_at_monotonic_ns"),
        released.get("turn_start_flushed_at_unix_ns"),
    )
    if any(
        not isinstance(value, int) or isinstance(value, bool) or value <= 0
        for value in timestamps
    ) or not (
        timestamps[0] <= timestamps[2] <= timestamps[4] <= timestamps[6]
        and timestamps[1] <= timestamps[3] <= timestamps[5] <= timestamps[7]
    ):
        raise ReportError(f"{label} prompt-release timestamp order is invalid")
    if (
        ready.get("turn_start_write_state") != "not_started"
        or go.get("ready_sha256") != ready.get("ready_sha256")
        or go.get("turn_start_write_authorized") is not True
        or released.get("ready_sha256") != ready.get("ready_sha256")
        or released.get("go_sha256") != go.get("go_sha256")
        or released.get("turn_start_write_state") != "flushed"
        or released.get("timestamp_capture_point")
        != "immediately_before_turn_start_write"
    ):
        raise ReportError(f"{label} prompt READY/GO/RELEASED chain is inconsistent")
    wire = codex_isolated.canonical_protocol_wire(
        codex_isolated.prompt_turn_start_request(
            prompt=effective_prompt,
            root_thread_id=root_thread_id,
            model=str(agent.get("model")),
            reasoning_effort=str(agent.get("reasoning_effort")),
        )
    )
    if (
        released.get("turn_start_request_sha256")
        != hashlib.sha256(wire).hexdigest()
        or released.get("turn_start_request_bytes") != len(wire)
    ):
        raise ReportError(f"{label} RELEASED record does not bind the exact turn/start wire")
    if run.get("time_measurement") != (
        "authenticated CLOCK_MONOTONIC turn/start write to authenticated nested "
        "submission-boundary publication after outer exec raw-response completion "
        "with inner submit_proof blocked; hidden validation certifies the immutable "
        "requested bytes"
    ):
        raise ReportError(f"{label} does not state the exact authenticated timing boundary")
    protocol = _mapping(run.get("protocol"), f"{label} protocol")
    verified = _mapping(protocol.get("verified"), f"{label} protocol verification")
    if verified.get("authenticated_prompt_release") is not True:
        raise ReportError(f"{label} protocol does not verify authenticated prompt release")
    release_mono = int(released["released_at_monotonic_ns"])
    deadline = release_mono + int(
        _number(limits.get("wall_clock_seconds"), "wall-clock limit") * 1_000_000_000
    )
    ultra_timing: bool | None = None
    if run.get("first_valid_seconds") is not None:
        boundary = _mapping(usage.get("submission_boundary"), f"{label} usage boundary")
        retained_boundary = (
            authenticated_boundary.get("submission_boundary")
            if isinstance(authenticated_boundary, Mapping)
            else None
        )
        retained_published = (
            retained_boundary.get("request_published_at_monotonic_ns")
            if isinstance(retained_boundary, Mapping)
            else None
        )
        published = _integer(
            retained_published,
            f"{label} request publication timestamp",
            positive=True,
        )
        if boundary.get("request_published_at_monotonic_ns") != published:
            raise ReportError(
                f"{label} usage boundary is not bound to the retained request publication"
            )
        _validate_nested_submission_wire(boundary, f"{label} release-timed boundary")
        outer_exec_observed = _integer(
            boundary.get("outer_raw_item_observed_at_monotonic_ns"),
            f"{label} outer exec observation timestamp",
            positive=True,
        )
        if (
            outer_exec_observed < release_mono
            or outer_exec_observed > published
            or published < release_mono
            or published >= deadline
        ):
            raise ReportError(f"{label} submit request lies outside its release-based wall limit")
        derived = round((published - release_mono) / 1_000_000_000, 6)
        if (
            run.get("first_valid_seconds") != derived
            or (
                run.get("pass") is True
                and run.get("scored_elapsed_seconds") != derived
            )
        ):
            raise ReportError(
                f"{label} first-valid time is not authenticated request publication"
            )
        ultra_timing = True
    return {
        "valid": True,
        "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
        "artifact_set_count": 1,
        "artifact_file_count": 3,
        "released_at_monotonic_ns": release_mono,
        "measurement_deadline_monotonic_ns": deadline,
        "ultra_request_publication_timing_verified": ultra_timing,
        "artifacts": {
            name: Path(str(path_summary[name])).resolve().relative_to(
                results_root.resolve()
            ).as_posix()
            for name in ("ready", "go", "release")
        },
    }


def _validate_protocol(run: Mapping[str, Any], *, ultra: bool) -> None:
    label = str(run.get("run_id"))
    if run.get("scored") is not True:
        raise ReportError(f"final run {label} is not marked scored")
    protocol = _mapping(run.get("protocol"), f"{label} protocol")
    if protocol.get("complete") is not True:
        raise ReportError(f"final run {label} does not have a complete protocol")
    claims = _mapping(protocol.get("claims"), f"{label} protocol claims")
    if set(claims) != set(PROTOCOL_CLAIMS) or dict(claims) != EXPECTED_PROTOCOL_CLAIMS:
        raise ReportError(
            f"final run {label} does not record the frozen unseeded protocol claims"
        )
    verified = _mapping(protocol.get("verified"), f"{label} protocol verification")
    for field in PROTOCOL_VERIFICATIONS[:-1]:
        if verified.get(field) is not True:
            raise ReportError(f"final run {label} failed protocol verification {field}")
    proof_accepted = run.get("first_valid_seconds") is not None
    if ultra and verified.get(PROTOCOL_VERIFICATIONS[-1]) is not proof_accepted:
        raise ReportError(
            f"final Ultra run {label} misstates its authenticated proof-boundary status"
        )
    notes = protocol.get("notes")
    if not isinstance(notes, list) or not all(isinstance(note, str) for note in notes):
        raise ReportError(f"final run {label} has malformed protocol notes")
    if UNSEEDED_PROTOCOL_NOTE not in notes:
        raise ReportError(f"final run {label} omits the frozen no-backend-seed disclosure")


def _fork_identifier_set(value: Any, label: str) -> set[str]:
    if (
        not isinstance(value, list)
        or value != sorted(set(value))
        or any(not isinstance(item, str) or not item for item in value)
    ):
        raise ReportError(f"{label} is not a sorted identifier set")
    return set(value)


def _validate_fork_policy_projection(
    projection: Mapping[str, Any], label: str
) -> tuple[dict[str, Mapping[str, Any]], dict[str, set[str]]]:
    """Authenticate every final spawn against the frozen PreToolUse policy."""

    sets = {
        name: _fork_identifier_set(projection.get(field), f"{label} {field}")
        for name, field in (
            ("raw", "raw_spawn_call_ids"),
            ("activity", "activity_spawn_call_ids"),
            ("collab", "collab_spawn_call_ids"),
            ("resolved", "resolved_spawn_call_ids"),
            ("failed", "failed_spawn_call_ids"),
            ("blocked", "policy_blocked_spawn_call_ids"),
            ("unresolved", "unresolved_spawn_call_ids"),
            ("unsupported", "unsupported_spawn_call_ids"),
            ("hook_observed", "hook_observed_spawn_call_ids"),
            ("hook_allowed", "hook_allowed_spawn_call_ids"),
            ("hook_blocked", "hook_blocked_spawn_call_ids"),
            ("hook_invalid", "hook_invalid_spawn_call_ids"),
        )
    }
    allowed_failed = sets["failed"] - sets["blocked"]
    allowed_terminal = sets["resolved"] | allowed_failed
    if (
        projection.get("fork_policy_complete") is not True
        or sets["raw"] != sets["resolved"] | sets["failed"]
        or sets["resolved"] & sets["failed"]
        or not sets["blocked"] <= sets["failed"]
        or sets["activity"] != sets["resolved"]
        or sets["collab"] & sets["blocked"]
        or not sets["collab"] <= allowed_terminal
        or sets["unresolved"]
        or sets["unsupported"]
        or sets["hook_observed"] != sets["raw"]
        or sets["hook_allowed"] != allowed_terminal
        or sets["hook_blocked"] != sets["blocked"]
        or sets["hook_invalid"]
    ):
        raise ReportError(f"{label} fork-policy identifier projections disagree")

    expected_static = codex_isolated.ultra_fork_policy_static_record()
    policy = _mapping(projection.get("fork_policy"), f"{label} fork policy")
    if set(policy) != set(expected_static) | {"call_evidence", "complete"}:
        raise ReportError(f"{label} fork-policy fields are not exact")
    static = dict(policy)
    raw_calls = static.pop("call_evidence")
    complete = static.pop("complete")
    if static != expected_static or complete is not True:
        raise ReportError(f"{label} fork-policy freeze is stale")
    calls_list = _list(raw_calls, f"{label} fork-policy calls")
    calls: dict[str, Mapping[str, Any]] = {}
    for call in calls_list:
        item = _mapping(call, f"{label} fork-policy call")
        call_id = item.get("call_id")
        if (
            set(item) != FORK_POLICY_CALL_FIELDS
            or not isinstance(call_id, str)
            or not call_id
            or call_id in calls
        ):
            raise ReportError(f"{label} fork-policy call evidence is malformed")
        calls[call_id] = item
    if list(calls) != sorted(calls) or set(calls) != sets["raw"]:
        raise ReportError(f"{label} fork-policy calls are not canonical")

    raw_threads = projection.get("thread_accounting")
    known_threads = {
        str(thread.get("thread_id"))
        for thread in raw_threads
        if isinstance(thread, Mapping)
        and isinstance(thread.get("thread_id"), str)
        and thread.get("thread_id")
    } if isinstance(raw_threads, list) else set()
    raw_responses = projection.get("response_ids")
    known_responses = (
        set(raw_responses)
        if isinstance(raw_responses, list)
        and all(isinstance(item, str) and item for item in raw_responses)
        else None
    )
    for call_id, call in calls.items():
        parent = call.get("parent_thread_id")
        turn_id = call.get("parent_turn_id")
        response_id = call.get("parent_response_id")
        if (
            not isinstance(parent, str)
            or not parent
            or not isinstance(turn_id, str)
            or not turn_id
            or not isinstance(response_id, str)
            or not response_id
            or (known_threads and parent not in known_threads)
            or (known_responses is not None and response_id not in known_responses)
            or call.get("hook_run_id")
            != f"pre-tool-use:0:{expected_static['source_path']}:{call_id}"
            or call.get("hook_source_path") != expected_static["source_path"]
            or call.get("hook_thread_id") != parent
            or call.get("hook_turn_id") != turn_id
            or call.get("hook_started_observed") is not True
            or call.get("hook_started_count") != 1
            or call.get("hook_completed_observed") is not True
            or call.get("hook_completed_count") != 1
            or call.get("child_activity_observed")
            is not (call_id in sets["resolved"])
        ):
            raise ReportError(f"{label} hook binding for {call_id} is inexact")
        fork_turns = call.get("fork_turns")
        if call_id in sets["blocked"]:
            if (
                fork_turns in ("all", "none")
                or call.get("fork_semantics")
                not in (
                    "invalid_arguments",
                    "invalid_fork_turns",
                    "unsupported_positive_turn_suffix",
                )
                or call.get("hook_status")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
                or call.get("decision")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
                or call.get("feedback")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
                or call.get("resolution_status")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
            ):
                raise ReportError(f"{label} blocked call {call_id} is inconsistent")
            continue
        semantics = {
            "all": "full_history_parent_pre_response",
            "none": "no_history_zero",
        }.get(fork_turns)
        resolution = (
            "resolved_child"
            if call_id in sets["resolved"]
            else "failed_without_child"
        )
        if (
            semantics is None
            or call.get("fork_semantics") != semantics
            or call.get("hook_status")
            != codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
            or call.get("decision")
            != codex_isolated.ULTRA_FORK_POLICY_ALLOW_DECISION
            or call.get("feedback") is not None
            or call.get("resolution_status") != resolution
        ):
            raise ReportError(f"{label} allowed call {call_id} is inconsistent")
    return calls, sets


def _validate_raw_usage(
    results_root: Path,
    run: Mapping[str, Any],
    *,
    token_limit: int,
) -> tuple[dict[str, Any], Path]:
    label = str(run.get("run_id"))
    raw_usage = _option(run.get("agent_command"), "--usage-output", label)
    usage_path = _resolve_result_path(results_root, raw_usage, f"{label} usage ledger")
    try:
        parsed = runner.read_token_usage(usage_path)
    except Exception as error:
        raise ReportError(f"{label} has an invalid trusted usage ledger: {error}") from error
    if parsed is None or run.get("token_usage") != parsed:
        raise ReportError(f"{label} record does not equal its parsed trusted usage ledger")
    token_endpoint = run.get("failure_code") == "TOKEN_LIMIT"
    if (
        parsed.get("usage_scope") != runner.ULTRA_USAGE_SCOPE
        or parsed.get("measurement_source") != runner.ULTRA_USAGE_MEASUREMENT_SOURCE
        or parsed.get("accounting_projection_schema_version")
        != ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or parsed.get("spawn_binding_source")
        != "raw_function_call.call_id=subAgentActivity.id"
        or parsed.get("measurement_exact") is not True
        or (
            not token_endpoint
            and any(
                parsed.get(field) is not True
                for field in (
                    "spawn_linkage_complete",
                    "descendant_accounting_complete",
                    "cumulative_projection_complete",
                    "fork_policy_complete",
                    "accounting_complete",
                )
            )
        )
    ):
        raise ReportError(f"{label} does not have an exact complete Ultra accounting projection")
    try:
        derived_projection = construction_report._rederive_ultra_accounting_evidence(
            parsed
        )
    except construction_report.ReportError as error:
        raise ReportError(
            f"{label} provider-bound projection-v6 replay failed: {error}"
        ) from error
    accepted_endpoint = parsed.get("submission_boundary_exact") is True and isinstance(
        parsed.get("submission_boundary"), Mapping
    )
    expected_projection_outcome = (
        "accepted_boundary"
        if accepted_endpoint
        else "token_gate_crossing"
        if token_endpoint
        else "natural_drain"
    )
    if derived_projection.get("outcome") != expected_projection_outcome:
        raise ReportError(f"{label} projection-v6 endpoint disagrees with its outcome")
    for field in (
        "raw_spawn_call_ids",
        "activity_spawn_call_ids",
        "collab_spawn_call_ids",
        "resolved_spawn_call_ids",
        "failed_spawn_call_ids",
        "policy_blocked_spawn_call_ids",
        "unresolved_spawn_call_ids",
        "unsupported_spawn_call_ids",
        "inference_child_thread_ids",
        "hook_observed_spawn_call_ids",
        "hook_allowed_spawn_call_ids",
        "hook_blocked_spawn_call_ids",
        "hook_invalid_spawn_call_ids",
    ):
        identifiers = parsed.get(field)
        if not isinstance(identifiers, list) or identifiers != sorted(set(identifiers)):
            raise ReportError(f"{label} has a malformed accounting identifier set {field}")
    if not token_endpoint:
        _validate_fork_policy_projection(parsed, label)
    if parsed["model_tokens"] >= token_limit and run.get("pass") is True:
        raise ReportError(f"passing run {label} reached the fixed token limit")
    measurement = _mapping(run.get("token_measurement"), f"{label} token measurement")
    if (
        measurement.get("source") != runner.ULTRA_TOKEN_MEASUREMENT_SOURCE
        or measurement.get("provider_cumulative_total_exact") is not True
        or measurement.get("cached_input_counted_once") is not True
        or measurement.get("measurement_error") is not None
        or measurement.get("trusted_usage_path_outside_workspace") is not True
        or measurement.get("usage_scope") != runner.ULTRA_USAGE_SCOPE
        or measurement.get("thread_count") != parsed.get("thread_count")
        or measurement.get("response_count") != parsed.get("response_count")
        or measurement.get("tree_drain_complete") != parsed.get("drain_complete")
    ):
        raise ReportError(f"{label} token measurement is not exact and trusted")
    enforcement = _mapping(measurement.get("limit_enforcement"), f"{label} token enforcement")
    if (
        enforcement.get("mode") != runner.ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE
        or enforcement.get("notification") != runner.ULTRA_USAGE_NOTIFICATION
        or enforcement.get("configured_limit_tokens") != token_limit
        or enforcement.get("checked_before_submission_validation") is not True
        or not isinstance(enforcement.get("triggered"), bool)
        or enforcement.get("one_response_overshoot_possible") is not True
        or enforcement.get("concurrent_inflight_overshoot_possible") is not False
    ):
        raise ReportError(f"{label} has invalid token-limit enforcement metadata")
    first_crossing = parsed.get("first_crossing")
    expected_trigger = parsed["model_tokens"] >= token_limit
    if enforcement.get("triggered") is not expected_trigger:
        raise ReportError(f"{label} token-cap trigger disagrees with its exact ledger")
    if expected_trigger:
        crossing = _mapping(first_crossing, f"{label} first token crossing")
        observed = _integer(crossing.get("tokens"), f"{label} crossing tokens")
        if (
            observed < token_limit
            or enforcement.get("observed_tokens") != observed
            or enforcement.get("first_crossing_tokens") != observed
            or enforcement.get("overshoot_tokens") != observed - token_limit
            or enforcement.get("first_crossing_overshoot_tokens") != observed - token_limit
            or enforcement.get("final_endpoint_tokens") != parsed["model_tokens"]
            or enforcement.get("final_overshoot_tokens")
            != max(0, parsed["model_tokens"] - token_limit)
        ):
            raise ReportError(f"{label} token-cap crossing metadata is inconsistent")
    elif (
        first_crossing is not None
        or any(
            enforcement.get(field) is not None
            for field in (
                "observed_tokens",
                "overshoot_tokens",
                "first_crossing_tokens",
                "first_crossing_overshoot_tokens",
                "final_endpoint_tokens",
                "final_overshoot_tokens",
            )
        )
    ):
        raise ReportError(f"{label} records a token crossing below the cap")
    if run.get("first_valid_seconds") is not None and measurement.get(
        "post_submission_usage_established"
    ) is not True:
        raise ReportError(f"accepted-proof run {label} lacks a final submission usage boundary")
    return parsed, usage_path


def _validate_submission_event_order(
    value: Mapping[str, Any],
    label: str,
    *,
    require_event_timestamps: bool,
) -> str:
    """Require one schema-v5 order with strict JSON types and clocks."""

    try:
        return construction_report._validate_submission_event_order_v5(
            value,
            label,
            require_event_timestamps=require_event_timestamps,
        )
    except construction_report.ReportError as error:
        raise ReportError(str(error)) from error


def _validate_nested_submission_wire(value: Mapping[str, Any], label: str) -> None:
    """Authenticate the exact schema-v5 outer-exec/inner-submit identity."""

    try:
        construction_report._validate_nested_submission_wire_v5(value, label)
    except construction_report.ReportError as error:
        raise ReportError(str(error)) from error


def _authenticated_barrier_artifacts(
    results_root: Path,
    usage_path: Path,
    run: Mapping[str, Any],
    usage: Mapping[str, Any],
    accepted_path: Path,
) -> dict[str, Any]:
    label = str(run.get("run_id"))
    boundary = _mapping(usage.get("submission_boundary"), f"{label} submission boundary")
    if usage.get("submission_boundary_exact") is not True:
        raise ReportError(f"{label} submission boundary is not exact")
    sequence = _integer(boundary.get("sequence"), f"{label} boundary sequence", positive=True)
    paths = codex_isolated.submission_barrier_paths(usage_path, sequence)
    authenticated: dict[str, dict[str, Any]] = {}
    for artifact, hash_field in (
        ("challenge", "challenge_sha256"),
        ("call", "call_sha256"),
        ("request", "request_sha256"),
        ("ack", "ack_sha256"),
    ):
        path = _inside(results_root, paths[artifact], f"{label} {artifact}")
        if not path.is_file() or path.is_symlink():
            raise ReportError(f"{label} protected {artifact} artifact is missing")
        try:
            value = codex_isolated.verify_authenticated_record(read_json(path), hash_field)
        except Exception as error:
            raise ReportError(f"{label} protected {artifact} artifact is invalid: {error}") from error
        authenticated[artifact] = value
    challenge = authenticated["challenge"]
    call = authenticated["call"]
    request = authenticated["request"]
    ack = authenticated["ack"]
    for record_name, record in (
        ("captured call", call),
        ("published request", request),
        ("accepted boundary", boundary),
    ):
        _validate_nested_submission_wire(record, f"{label} {record_name}")
    request_event_order = _validate_submission_event_order(
        request,
        f"{label} published request",
        require_event_timestamps=True,
    )
    boundary_event_order = _validate_submission_event_order(
        boundary,
        f"{label} accepted boundary",
        require_event_timestamps=False,
    )
    if boundary_event_order != request_event_order:
        raise ReportError(f"{label} request and boundary event orders disagree")
    if (
        challenge.get("schema_version") != codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or call.get("schema_version")
        != codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or request.get("schema_version")
        != codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or ack.get("schema_version")
        != codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or challenge.get("kind") != "highambench_submission_challenge"
        or call.get("kind") != "highambench_submission_call"
        or request.get("kind") != "highambench_submission_request"
        or ack.get("kind") != "highambench_submission_ack"
        or call.get("sequence") != sequence
        or request.get("sequence") != sequence
        or ack.get("sequence") != sequence
    ):
        raise ReportError(f"{label} retained barrier records use the wrong schema")
    expected_yield = codex_isolated.nested_submission_exec_yield_record()
    if any(
        challenge.get(field) != expected
        for field, expected in expected_yield.items()
    ):
        raise ReportError(f"{label} challenge has the wrong anti-yield envelope")
    common = (
        "attempt_nonce",
        "run_id",
        "validator_contract_sha256",
        *expected_yield,
    )
    if any(request.get(field) != challenge.get(field) for field in common):
        raise ReportError(f"{label} request is not bound to its challenge")
    if any(call.get(field) != challenge.get(field) for field in common):
        raise ReportError(f"{label} dynamic call is not bound to its challenge")
    if request.get("challenge_sha256") != challenge.get("challenge_sha256"):
        raise ReportError(f"{label} request has the wrong challenge digest")
    if request.get("call_sha256") != call.get("call_sha256"):
        raise ReportError(f"{label} request has the wrong call digest")
    call_bound_fields = (
        "jsonrpc_request_id",
        "call_id",
        "submission_transport",
        "outer_raw_item_id",
        "outer_raw_item_type",
        "outer_exec_name",
        "outer_exec_call_id",
        "outer_exec_program",
        "outer_exec_program_bytes",
        "outer_exec_program_sha256",
        "outer_exec_yield_time_ms",
        "outer_exec_yield_envelope_basis",
        "outer_exec_yield_attempt_wall_seconds",
        "outer_exec_yield_post_submission_validation_reserve_seconds",
        "outer_exec_yield_envelope_ms",
        "outer_exec_yield_margin_ms",
        "outer_exec_timer_starts_at_or_after_prompt_release",
        "outer_exec_yield_exceeds_envelope",
        "outer_raw_item_observed_at_monotonic_ns",
        "inner_dynamic_item_started_at_monotonic_ns",
        "outer_raw_item_observed_before_inner_dynamic_call",
        "inner_dynamic_call_id",
        "inner_dynamic_tool_name",
        "inner_dynamic_arguments",
        "thread_id",
        "turn_id",
        "candidate_path",
        "candidate_sha256",
        "candidate_size_bytes",
        "snapshot_name",
        "captured_at_unix_ns",
        "captured_at_monotonic_ns",
    )
    if any(request.get(field) != call.get(field) for field in call_bound_fields):
        raise ReportError(f"{label} request does not bind its captured dynamic call")
    request_truth_flags = (
        "raw_response_completed_before_boundary_publication",
        "candidate_captured_at_dynamic_call",
        "root_only",
        "descendants_quiescent",
        "sole_model_tool_call_in_response",
        "outer_exec_final_raw_item",
        "inner_dynamic_call_observed",
        "inner_dynamic_item_started",
        "inner_submit_invocation_exact",
        "inner_submit_only_nested_tool_call",
    )
    if any(
        request.get(field) is not True or boundary.get(field) is not True
        for field in request_truth_flags
    ) or any(
        boundary.get(field) is not value
        for field, value in (
            ("inner_dynamic_call_left_blocked", True),
            ("inner_dynamic_tool_response_sent", False),
            ("outer_exec_output_emitted", False),
            ("later_model_response_possible", False),
        )
    ):
        raise ReportError(f"{label} retained nested boundary semantics are false")
    gate_close = boundary.get("provider_gate_close")
    if (
        not isinstance(gate_close, Mapping)
        or set(gate_close)
        != {"won", "requested_reason", "effective_reason", "phase", "sequence"}
        or gate_close.get("won") is not True
        or gate_close.get("requested_reason") != "accepted_submission"
        or gate_close.get("effective_reason") != "accepted_submission"
        or gate_close.get("phase") != "CLOSED"
        or type(gate_close.get("sequence")) is not int
        or gate_close["sequence"] <= 0
    ):
        raise ReportError(f"{label} lacks its schema-v5 provider-gate close")
    if (
        ack.get("decision") != "accept"
        or ack.get("request_sha256") != request.get("request_sha256")
        or ack.get("candidate_sha256") != request.get("candidate_sha256")
    ):
        raise ReportError(f"{label} has no authenticated acceptance acknowledgement")
    bindings = {
        "sequence": sequence,
        "request_sha256": request.get("request_sha256"),
        "ack_sha256": ack.get("ack_sha256"),
        "challenge_sha256": challenge.get("challenge_sha256"),
        "call_sha256": call.get("call_sha256"),
        "candidate_sha256": request.get("candidate_sha256"),
        "candidate_size_bytes": request.get("candidate_size_bytes"),
        "run_id": label,
        "attempt_nonce": request.get("attempt_nonce"),
        "validator_contract_sha256": request.get("validator_contract_sha256"),
        "jsonrpc_request_id": request.get("jsonrpc_request_id"),
        "call_id": request.get("call_id"),
        "submission_transport": request.get("submission_transport"),
        "outer_raw_item_id": request.get("outer_raw_item_id"),
        "outer_raw_item_type": request.get("outer_raw_item_type"),
        "outer_exec_name": request.get("outer_exec_name"),
        "outer_exec_call_id": request.get("outer_exec_call_id"),
        "outer_exec_program": request.get("outer_exec_program"),
        "outer_exec_program_bytes": request.get("outer_exec_program_bytes"),
        "outer_exec_program_sha256": request.get("outer_exec_program_sha256"),
        **{
            field: request.get(field)
            for field in codex_isolated.nested_submission_exec_yield_record()
        },
        "outer_raw_item_observed_at_monotonic_ns": request.get(
            "outer_raw_item_observed_at_monotonic_ns"
        ),
        "inner_dynamic_item_started_at_monotonic_ns": request.get(
            "inner_dynamic_item_started_at_monotonic_ns"
        ),
        "outer_raw_item_observed_before_inner_dynamic_call": request.get(
            "outer_raw_item_observed_before_inner_dynamic_call"
        ),
        "inner_dynamic_call_id": request.get("inner_dynamic_call_id"),
        "inner_dynamic_tool_name": request.get("inner_dynamic_tool_name"),
        "inner_dynamic_arguments": request.get("inner_dynamic_arguments"),
        "thread_id": request.get("thread_id"),
        "turn_id": request.get("turn_id"),
        "response_id": request.get("response_id"),
        "raw_response_notification_sequence": request.get(
            "raw_response_notification_sequence"
        ),
        "submission_event_order": request.get("submission_event_order"),
        "dynamic_call_observed_before_raw_response_completed": request.get(
            "dynamic_call_observed_before_raw_response_completed"
        ),
        "raw_response_completed_before_dynamic_call_observed": request.get(
            "raw_response_completed_before_dynamic_call_observed"
        ),
        "candidate_path": request.get("candidate_path"),
        "request_published_at_unix_ns": request.get("request_published_at_unix_ns"),
        "request_published_at_monotonic_ns": request.get(
            "request_published_at_monotonic_ns"
        ),
        "validator_accepted_at_unix_ns": ack.get("validator_accepted_at_unix_ns"),
        "validator_accepted_elapsed_seconds": ack.get(
            "validator_accepted_elapsed_seconds"
        ),
    }
    if any(boundary.get(field) != wanted for field, wanted in bindings.items()):
        raise ReportError(f"{label} final usage boundary is not bound to request/ack artifacts")
    snapshot_path = _inside(results_root, paths["snapshot"], f"{label} candidate snapshot")
    if not snapshot_path.is_file() or snapshot_path.is_symlink():
        raise ReportError(f"{label} immutable candidate snapshot is missing")
    candidate_sha = _hex(request.get("candidate_sha256"), f"{label} candidate digest")
    candidate_bytes = _integer(request.get("candidate_size_bytes"), f"{label} candidate size")
    if snapshot_path.stat().st_size != candidate_bytes or file_sha256(snapshot_path) != candidate_sha:
        raise ReportError(f"{label} candidate snapshot hash/size is inconsistent")
    if file_sha256(accepted_path) != candidate_sha:
        raise ReportError(f"{label} accepted proof differs from the immutable candidate snapshot")
    expected_boundary_usage = {
        "input_tokens": usage["input_tokens"],
        "cached_input_tokens": usage["cached_input_tokens"],
        "cache_write_input_tokens": usage.get("cache_write_input_tokens", 0),
        "output_tokens": usage["output_tokens"],
        "reasoning_output_tokens": usage.get("reasoning_output_tokens", 0),
        "total_tokens": usage["model_tokens"],
        "response_count": usage["response_count"],
        "thread_count": usage["thread_count"],
        "notification_sequence": usage["notification_sequence"],
        "response_ids": usage["response_ids"],
        "appserver_response_count": usage["appserver_response_count"],
        "appserver_response_ids": usage["appserver_response_ids"],
    }
    if request.get("boundary_usage") != expected_boundary_usage:
        raise ReportError(f"{label} request usage snapshot differs from the final proof boundary")
    for field in (
        "captured_at_unix_ns",
        "captured_at_monotonic_ns",
        "request_published_at_unix_ns",
        "request_published_at_monotonic_ns",
        "raw_response_observed_at_unix_ns",
        "raw_response_observed_at_monotonic_ns",
    ):
        _integer(request.get(field), f"{label} request {field}", positive=True)
    for field in (
        "validator_accepted_at_unix_ns",
        "published_at_unix_ns",
        "published_at_monotonic_ns",
    ):
        _integer(ack.get(field), f"{label} acknowledgement {field}", positive=True)
    first_valid = _number(run.get("first_valid_seconds"), f"{label} first-valid time")
    validator_elapsed = _number(
        ack.get("validator_accepted_elapsed_seconds"),
        f"{label} validator acceptance time",
    )
    actual_stop = _number(run.get("actual_stop_seconds"), f"{label} actual stop time")
    if first_valid > validator_elapsed + 1e-6 or validator_elapsed > actual_stop + 1e-3:
        raise ReportError(
            f"{label} scored call/validator/stop times are not monotonically bound"
        )
    summary = _mapping(run.get("ultra_submission_boundary"), f"{label} boundary summary")
    if (
        summary.get("verified") is not True
        or summary.get("sequence") != sequence
        or summary.get("request_sha256") != request.get("request_sha256")
        or summary.get("ack_sha256") != ack.get("ack_sha256")
    ):
        raise ReportError(f"{label} run record has a stale submission-boundary summary")
    artifact_summary = _mapping(summary.get("artifacts"), f"{label} retained barrier artifacts")
    if set(artifact_summary) != {"challenge", "call", "request", "ack", "snapshot"}:
        raise ReportError(f"{label} retained barrier artifact map is incomplete")
    for name in ("challenge", "call", "request", "ack", "snapshot"):
        entry = _mapping(artifact_summary.get(name), f"{label} retained {name}")
        expected_entry_keys = (
            {"path", "file_sha256", "size_bytes"}
            if name == "snapshot"
            else {"path", "record_sha256", "file_sha256"}
        )
        if set(entry) != expected_entry_keys:
            raise ReportError(f"{label} retained {name} descriptor has unexpected fields")
        path = _resolve_result_path(results_root, entry.get("path"), f"{label} retained {name}")
        if path != paths[name].resolve():
            raise ReportError(f"{label} retained {name} path does not name the protected artifact")
        if path.stat().st_mode & 0o777 != 0o444:
            raise ReportError(f"{label} retained {name} artifact is not sealed mode 0444")
        if _hex(entry.get("file_sha256"), f"{label} retained {name} file digest") != file_sha256(path):
            raise ReportError(f"{label} retained {name} file hash is stale")
        if name == "snapshot":
            if entry.get("size_bytes") != candidate_bytes:
                raise ReportError(f"{label} retained snapshot size is stale")
        else:
            hash_field = f"{name}_sha256"
            if _hex(
                entry.get("record_sha256"), f"{label} retained {name} record digest"
            ) != authenticated[name].get(hash_field):
                raise ReportError(f"{label} retained {name} record hash is stale")
    return {
        "schema_version": boundary.get("schema_version"),
        "sequence": sequence,
        "request_sha256": request.get("request_sha256"),
        "ack_sha256": ack.get("ack_sha256"),
        "candidate_sha256": candidate_sha,
        "candidate_size_bytes": candidate_bytes,
        "validator_contract_sha256": request.get("validator_contract_sha256"),
        "submission_transport": request.get("submission_transport"),
        "outer_exec_program_bytes": request.get("outer_exec_program_bytes"),
        "outer_exec_program_sha256": request.get("outer_exec_program_sha256"),
        **{
            field: request.get(field)
            for field in codex_isolated.nested_submission_exec_yield_record()
        },
        "outer_raw_item_and_call_ids_pairwise_distinct": True,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "inner_dynamic_item_started": True,
        "inner_submit_invocation_exact": True,
        "inner_submit_only_nested_tool_call": True,
        "submission_event_order": request_event_order,
        "dynamic_call_observed_before_raw_response_completed": request.get(
            "dynamic_call_observed_before_raw_response_completed"
        ),
        "raw_response_completed_before_dynamic_call_observed": request.get(
            "raw_response_completed_before_dynamic_call_observed"
        ),
        "request_published_at_monotonic_ns": request.get(
            "request_published_at_monotonic_ns"
        ),
        "provider_gate_close": dict(gate_close),
    }


def _authenticate_validation_log(
    benchmark_root: Path,
    results_root: Path,
    run: Mapping[str, Any],
    task: Mapping[str, Any],
    validation_path: Path,
    validation: Mapping[str, Any],
    *,
    candidate_sha256: str | None,
    boundary: Mapping[str, Any] | None,
) -> dict[str, Any]:
    label = str(run.get("run_id"))
    file_digest = file_sha256(validation_path)
    if file_digest != _hex(run.get("validation_log_sha256"), f"{label} validation-log digest"):
        raise ReportError(f"{label} validation log does not match its run-record digest")
    record_digest = _hex(
        validation.get("record_sha256"), f"{label} validation record self-hash"
    )
    unsigned = dict(validation)
    unsigned.pop("record_sha256")
    if document_sha256(unsigned) != record_digest or run.get(
        "validation_record_sha256"
    ) != record_digest:
        raise ReportError(f"{label} validation log has a stale canonical self-hash")
    controlled = benchmark_root / "metadata" / "controlled" / f"{task['task_id']}.json"
    target_theorem = f"HighamBench.{task['declaration']}"
    authentication = _mapping(
        validation.get("authentication"), f"{label} validation authentication"
    )
    if set(authentication) != {
        "schema_version",
        "run_id",
        "task_id",
        "candidate_sha256",
        "target_theorem",
        "controlled_manifest_sha256",
        "validator_contract_sha256",
        "submission_request_sha256",
        "submission_sequence",
    }:
        raise ReportError(f"{label} validation authentication has unexpected fields")
    authenticated_candidate = _hex(
        authentication.get("candidate_sha256"), f"{label} authenticated candidate digest"
    )
    if candidate_sha256 is not None and authenticated_candidate != candidate_sha256:
        raise ReportError(f"{label} validation candidate disagrees with retained bytes")
    if (
        authentication.get("schema_version") != 1
        or authentication.get("run_id") != label
        or authentication.get("task_id") != task["task_id"]
        or authentication.get("target_theorem") != target_theorem
        or authentication.get("controlled_manifest_sha256") != file_sha256(controlled)
        or validation.get("target_theorem") != target_theorem
        or validation.get("condition") != run.get("condition")
    ):
        raise ReportError(f"{label} validation log is not bound to its task/candidate/target")
    validator_digest = _hex(
        authentication.get("validator_contract_sha256"),
        f"{label} validator-contract digest",
    )
    request_digest = _hex(
        authentication.get("submission_request_sha256"),
        f"{label} validation request digest",
    )
    sequence = _integer(
        authentication.get("submission_sequence"),
        f"{label} validation submission sequence",
        positive=True,
    )
    if boundary is not None and (
        validator_digest != boundary.get("validator_contract_sha256")
        or request_digest != boundary.get("request_sha256")
        or sequence != boundary.get("sequence")
    ):
        raise ReportError(f"{label} validation authentication disagrees with the accepted boundary")
    return {
        "file_sha256": file_digest,
        "record_sha256": record_digest,
        "candidate_sha256": authenticated_candidate,
        "validator_contract_sha256": validator_digest,
        "submission_request_sha256": request_digest,
        "submission_sequence": sequence,
    }


def _validation_controlled_checkpoint(
    value: Any,
    label: str,
    *,
    expected_files: int,
) -> tuple[Mapping[str, Any], bool]:
    checkpoint = _mapping(value, label)
    expected = _integer(checkpoint.get("expected"), f"{label} expected count", positive=True)
    verified = _integer(checkpoint.get("verified"), f"{label} verified count")
    missing = _list(checkpoint.get("missing"), f"{label} missing files")
    changed = _list(checkpoint.get("changed"), f"{label} changed files")
    ok = checkpoint.get("ok")
    if not isinstance(ok, bool) or expected != expected_files or verified > expected:
        raise ReportError(f"{label} has an incoherent controlled-file inventory")
    if not all(isinstance(item, str) and item for item in missing + changed):
        raise ReportError(f"{label} has malformed controlled-file findings")
    derived_ok = verified == expected and not missing and not changed
    if ok is not derived_ok:
        raise ReportError(f"{label} Boolean disagrees with its controlled-file findings")
    return checkpoint, derived_ok


def _validation_command_result(value: Any, label: str) -> Mapping[str, Any]:
    result = _mapping(value, label)
    command = _list(result.get("command"), f"{label} command")
    if not command or not all(isinstance(item, str) and item for item in command):
        raise ReportError(f"{label} has no concrete command")
    if not isinstance(result.get("display"), str) or not result["display"]:
        raise ReportError(f"{label} has no command display")
    if not isinstance(result.get("output"), str):
        raise ReportError(f"{label} output is not text")
    if not isinstance(result.get("output_truncated"), bool):
        raise ReportError(f"{label} has no output-truncation classification")
    _number(result.get("seconds"), f"{label} elapsed seconds")
    exit_code = result.get("exit_code")
    if exit_code is not None and (
        not isinstance(exit_code, int) or isinstance(exit_code, bool)
    ):
        raise ReportError(f"{label} exit code is malformed")
    if not isinstance(result.get("timed_out"), bool):
        raise ReportError(f"{label} timeout flag is malformed")
    system_error = result.get("system_error")
    if system_error is not None and (
        not isinstance(system_error, str) or not system_error
    ):
        raise ReportError(f"{label} system error is malformed")
    timed_out = result["timed_out"]
    if (
        (exit_code is None and timed_out is False and system_error is None)
        or (exit_code is not None and (timed_out is True or system_error is not None))
        or (timed_out is True and system_error is not None)
    ):
        raise ReportError(f"{label} has an impossible command outcome tri-state")
    return result


def _validation_candidate_inventory(
    validation: Mapping[str, Any],
    label: str,
    *,
    expected_files: int,
) -> tuple[Mapping[str, Any], list[Any]]:
    inventory = _mapping(validation.get("candidate_inventory"), f"{label} candidate inventory")
    if inventory.get("controlled_file_count") != expected_files:
        raise ReportError(f"{label} candidate inventory has the wrong controlled-file count")
    for field in (
        "scanned_sources",
        "candidate_oleans",
        "ignored_build_roots",
        "local_modules",
        "protected_modules",
    ):
        entries = _list(inventory.get(field), f"{label} candidate inventory {field}")
        if not all(isinstance(item, str) and item for item in entries):
            raise ReportError(f"{label} candidate inventory {field} is malformed")
        if entries != sorted(set(entries)):
            raise ReportError(f"{label} candidate inventory {field} is not canonical")
    submission = validation.get("submission")
    if submission not in inventory["scanned_sources"]:
        raise ReportError(f"{label} candidate inventory omitted the submitted source")
    inventory_findings = _list(
        inventory.get("findings"), f"{label} candidate inventory findings"
    )
    static_findings = _list(validation.get("static_findings"), f"{label} static findings")
    if any(item not in static_findings for item in inventory_findings):
        raise ReportError(f"{label} static scan omits candidate-inventory findings")
    source_stems = {
        PurePosixPath(item).with_suffix("") for item in inventory["scanned_sources"]
    }
    for olean in inventory["candidate_oleans"]:
        olean_path = PurePosixPath(olean)
        if olean_path.suffix != ".olean":
            raise ReportError(f"{label} candidate inventory contains a non-olean")
        if olean_path.with_suffix("") in source_stems:
            continue
        expected_finding = {
            "path": olean,
            "kind": "candidate olean without scanned source",
            "detail": (
                "candidate-created compiled Lean modules require a source file "
                "with the exact same workspace-relative module path"
            ),
        }
        if expected_finding not in inventory_findings:
            raise ReportError(
                f"{label} candidate inventory omits an unmatched-olean finding"
            )
    if any(PurePosixPath(item).suffix != ".lean" for item in inventory["scanned_sources"]):
        raise ReportError(f"{label} candidate inventory contains a non-source entry")
    return inventory, static_findings


def _validation_dependency_audit(
    validation: Mapping[str, Any],
    run: Mapping[str, Any],
    target_theorem: str,
    label: str,
    *,
    require_success: bool,
) -> tuple[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any] | None]:
    audit = _validation_command_result(
        validation.get("dependency_audit"), f"{label} dependency audit"
    )
    if audit.get("output_truncated") is not False:
        raise ReportError(f"{label} dependency audit output is not complete")
    parsed = _mapping(audit.get("parsed"), f"{label} parsed dependency audit")
    raw_parsed = validator.parse_dependency_audit(str(audit.get("output")))
    for field, wanted in raw_parsed.items():
        if parsed.get(field) != wanted:
            raise ReportError(f"{label} parsed dependency audit disagrees with its output")
    inventory = _mapping(
        validation.get("candidate_inventory"), f"{label} candidate inventory"
    )
    submission_module = PurePosixPath(str(validation.get("submission"))).with_suffix("")
    if len(submission_module.parts) == 0:
        raise ReportError(f"{label} submission module cannot be derived")
    submission_name = ".".join(submission_module.parts)
    local_modules = _list(inventory.get("local_modules"), f"{label} local modules")
    expected_helpers = sorted(set(local_modules) - {submission_name})
    parsed_helpers = _list(
        parsed.get("expected_helper_modules"), f"{label} expected helper modules"
    )
    missing_helpers = _list(
        parsed.get("missing_helper_modules"), f"{label} missing helper modules"
    )
    if parsed_helpers != expected_helpers:
        raise ReportError(f"{label} dependency audit has the wrong helper-module inventory")
    parsed_local = _list(parsed.get("local_modules"), f"{label} audited local modules")
    derived_missing = sorted(set(expected_helpers) - set(parsed_local))
    if missing_helpers != derived_missing:
        raise ReportError(f"{label} dependency audit has stale missing-helper findings")
    semantic_raw = validation.get("semantic_statement_check")
    semantic = (
        _mapping(semantic_raw, f"{label} semantic statement check")
        if semantic_raw is not None
        else None
    )
    if semantic is not None and parsed.get("type_check") != semantic:
        raise ReportError(f"{label} semantic statement check disagrees with the audit")
    if require_success:
        if (
            audit.get("exit_code") != 0
            or audit.get("timed_out") is not False
            or audit.get("system_error") is not None
            or parsed.get("format_version") != 2
            or parsed.get("ok") is not True
            or parsed.get("target_seen") is not True
            or parsed.get("malformed_lines") != []
            or parsed.get("forbidden_dependencies") != []
            or missing_helpers
            or semantic is None
            or semantic.get("candidate") != target_theorem
            or semantic.get("equal") is not True
            or not isinstance(semantic.get("expected"), str)
            or not semantic.get("expected")
        ):
            raise ReportError(f"{label} dependency/semantic audit is incomplete")
    declarations = _list(
        parsed.get("library_declarations"), f"{label} audited library declarations"
    )
    for declaration in declarations:
        item = _mapping(declaration, f"{label} audited library declaration")
        if (
            not isinstance(item.get("name"), str)
            or not item.get("name")
            or not isinstance(item.get("module"), str)
            or not item.get("module")
            or not isinstance(item.get("distance"), int)
            or isinstance(item.get("distance"), bool)
            or item.get("distance") < 0
        ):
            raise ReportError(f"{label} has a malformed library declaration")
    if require_success:
        if validation.get("library_declarations") != declarations:
            raise ReportError(f"{label} top-level library declarations disagree with the audit")
        if runner.library_declaration_names(declarations) != run.get("library_declarations"):
            raise ReportError(f"{label} audited library declarations disagree with the run")
        library_use = bool(declarations)
        if (
            validation.get("library_use") is not library_use
            or run.get("library_use") is not library_use
        ):
            raise ReportError(f"{label} library-use classification disagrees with its audit")
    return audit, parsed, semantic


def _validate_hidden_validation_semantics(
    benchmark_root: Path,
    run: Mapping[str, Any],
    task: Mapping[str, Any],
    validation: Mapping[str, Any],
    *,
    accepted: bool,
) -> dict[str, Any]:
    """Replay the hidden validator's ordered stages, not just its pass bit."""

    label = str(run.get("run_id"))
    target_theorem = f"HighamBench.{task['declaration']}"
    controlled_path = benchmark_root / "metadata" / "controlled" / f"{task['task_id']}.json"
    controlled = read_json(controlled_path)
    expected_files = len(_list(controlled.get("files"), f"{label} controlled manifest files"))
    if expected_files <= 0:
        raise ReportError(f"{label} controlled manifest is empty")
    if (
        validation.get("condition") != run.get("condition")
        or validation.get("target_theorem") != target_theorem
        or validation.get("submission") != "Submission.lean"
        or validation.get("reject_workspace_local_module_imports") is not True
        or not isinstance(validation.get("note"), str)
        or not validation.get("note")
    ):
        raise ReportError(f"{label} hidden validation has an invalid fixed contract")
    validation_command_authentication = _authenticate_validation_commands(
        benchmark_root, run, task, validation
    )

    def rejected(code: str, stage: str) -> dict[str, Any]:
        if accepted or validation.get("pass") is not False:
            raise ReportError(f"{label} accepted validation failed at {stage}")
        if validation.get("failure_code") != code:
            raise ReportError(
                f"{label} rejected validation failure does not match first failed stage {stage}"
            )
        tail_by_stage = {
            "controlled_before": (
                "candidate_inventory",
                "statement_check",
                "controlled_hidden",
                "compile",
                "controlled_after_compile",
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "candidate_inventory_and_static_scan": (
                "statement_check",
                "controlled_hidden",
                "compile",
                "controlled_after_compile",
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "statement_check": (
                "controlled_hidden",
                "compile",
                "controlled_after_compile",
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "controlled_hidden": (
                "compile",
                "controlled_after_compile",
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "candidate_compile": (
                "controlled_after_compile",
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "controlled_after_compile": (
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "candidate_compile_system_error": (
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "candidate_compile_timeout": (
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "candidate_compile_rejection": (
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "candidate_compile_sorry_dependency": (
                "expected_statement_compile",
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "expected_statement_compile": (
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "expected_statement_compile_missing": (
                "controlled_after_expected_compile",
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "controlled_after_expected_compile": (
                "local_modules_side_channel",
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "local_modules_side_channel": (
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "dependency_audit_setup": (
                "controlled_after_audit",
                "dependency_audit",
                "semantic_statement_check",
            ),
            "controlled_after_audit": (
                "dependency_audit",
                "semantic_statement_check",
            ),
            "dependency_audit_missing": ("semantic_statement_check",),
        }
        populated_tail = [
            field
            for field in tail_by_stage.get(stage, ())
            if validation.get(field) is not None
        ]
        if populated_tail:
            raise ReportError(
                f"{label} rejected validation populates impossible post-{stage} stages: "
                + ", ".join(populated_tail)
            )
        return {
            "status": "rejected",
            "derived_failure_code": code,
            "first_failed_stage": stage,
            "validator_command_authentication": validation_command_authentication,
        }

    controlled_before_raw = validation.get("controlled_before")
    if controlled_before_raw is None:
        return rejected("SYSTEM_ERROR", "controlled_before")
    _, controlled_before_ok = _validation_controlled_checkpoint(
        controlled_before_raw,
        f"{label} controlled-before checkpoint",
        expected_files=expected_files,
    )
    if not controlled_before_ok:
        return rejected("RULE_VIOLATION", "controlled_before")

    _inventory, static_findings = _validation_candidate_inventory(
        validation, label, expected_files=expected_files
    )
    if static_findings:
        return rejected("RULE_VIOLATION", "candidate_inventory_and_static_scan")

    statement_raw = validation.get("statement_check")
    if statement_raw is None:
        return rejected("SYSTEM_ERROR", "statement_check")
    statement = _mapping(statement_raw, f"{label} textual statement check")
    if statement.get("ok") is not True:
        return rejected("RULE_VIOLATION", "statement_check")
    if (
        not isinstance(statement.get("submitted"), str)
        or not statement.get("submitted")
        or statement.get("submitted") != statement.get("canonical")
    ):
        raise ReportError(f"{label} successful textual statement check is incoherent")

    controlled_hidden_raw = validation.get("controlled_hidden")
    if controlled_hidden_raw is None:
        return rejected("SYSTEM_ERROR", "controlled_hidden")
    _, controlled_hidden_ok = _validation_controlled_checkpoint(
        controlled_hidden_raw,
        f"{label} controlled-hidden checkpoint",
        expected_files=expected_files,
    )
    if not controlled_hidden_ok:
        return rejected("RULE_VIOLATION", "controlled_hidden")

    compile_raw = validation.get("compile")
    if compile_raw is None:
        return rejected("SYSTEM_ERROR", "candidate_compile")
    compile_result = _validation_command_result(compile_raw, f"{label} candidate compile")
    controlled_after_compile_raw = validation.get("controlled_after_compile")
    if controlled_after_compile_raw is None:
        return rejected("SYSTEM_ERROR", "controlled_after_compile")
    _, controlled_after_compile_ok = _validation_controlled_checkpoint(
        controlled_after_compile_raw,
        f"{label} controlled-after-compile checkpoint",
        expected_files=expected_files,
    )
    if not controlled_after_compile_ok:
        return rejected("RULE_VIOLATION", "controlled_after_compile")
    if compile_result.get("system_error") is not None:
        return rejected("SYSTEM_ERROR", "candidate_compile_system_error")
    if compile_result.get("timed_out") is True:
        return rejected("SYSTEM_ERROR", "candidate_compile_timeout")
    if compile_result.get("exit_code") != 0:
        return rejected(
            validator.classify_lean_failure(str(compile_result.get("output"))),
            "candidate_compile_rejection",
        )
    if "sorryAx" in str(compile_result.get("output")) or "declaration uses 'sorry'" in str(
        compile_result.get("output")
    ):
        return rejected("RULE_VIOLATION", "candidate_compile_sorry_dependency")

    expected_compile_raw = validation.get("expected_statement_compile")
    if expected_compile_raw is None:
        return rejected("SYSTEM_ERROR", "expected_statement_compile_missing")
    expected_compile = _validation_command_result(
        expected_compile_raw, f"{label} expected-statement compile"
    )
    controlled_after_expected_raw = validation.get("controlled_after_expected_compile")
    if controlled_after_expected_raw is None:
        return rejected("SYSTEM_ERROR", "controlled_after_expected_compile")
    _, controlled_after_expected_ok = _validation_controlled_checkpoint(
        controlled_after_expected_raw,
        f"{label} controlled-after-expected-compile checkpoint",
        expected_files=expected_files,
    )
    if not controlled_after_expected_ok:
        return rejected("RULE_VIOLATION", "controlled_after_expected_compile")
    if (
        expected_compile.get("system_error") is not None
        or expected_compile.get("timed_out") is True
        or expected_compile.get("exit_code") != 0
    ):
        return rejected("SYSTEM_ERROR", "expected_statement_compile")

    side_channel_raw = validation.get("local_modules_side_channel")
    if side_channel_raw is None:
        return rejected("SYSTEM_ERROR", "dependency_audit_setup")
    side_channel = _mapping(side_channel_raw, f"{label} local-module side channel")
    if side_channel.get("created_after_candidate_compilation") is not True:
        raise ReportError(f"{label} local-module side channel was created at the wrong stage")
    if side_channel.get("candidate_recompiled_during_audit") is not False:
        raise ReportError(f"{label} dependency audit recompiled candidate source")
    if side_channel.get("unchanged_after_audit") is not True:
        return rejected("RULE_VIOLATION", "local_modules_side_channel")

    controlled_after_audit_raw = validation.get("controlled_after_audit")
    if controlled_after_audit_raw is None:
        return rejected("SYSTEM_ERROR", "controlled_after_audit")
    _, controlled_after_audit_ok = _validation_controlled_checkpoint(
        controlled_after_audit_raw,
        f"{label} controlled-after-audit checkpoint",
        expected_files=expected_files,
    )
    if not controlled_after_audit_ok:
        return rejected("RULE_VIOLATION", "controlled_after_audit")

    dependency_raw = validation.get("dependency_audit")
    if dependency_raw is None:
        return rejected("SYSTEM_ERROR", "dependency_audit_missing")
    audit, parsed, semantic = _validation_dependency_audit(
        validation,
        run,
        target_theorem,
        label,
        require_success=False,
    )
    if isinstance(semantic, Mapping) and semantic.get("equal") is False:
        return rejected("RULE_VIOLATION", "semantic_statement_check")
    if (
        semantic is None
        or semantic.get("candidate") != target_theorem
        or not isinstance(semantic.get("expected"), str)
        or not semantic.get("expected")
        or semantic.get("equal") is not True
    ):
        return rejected("SYSTEM_ERROR", "semantic_statement_check")
    if parsed.get("forbidden_dependencies"):
        return rejected("RULE_VIOLATION", "forbidden_dependency_audit")
    if (
        parsed.get("format_version") != 2
        or parsed.get("missing_helper_modules")
    ):
        return rejected("SYSTEM_ERROR", "helper_dependency_coverage")
    if (
        audit.get("system_error") is not None
        or audit.get("timed_out") is True
        or audit.get("exit_code") != 0
        or parsed.get("ok") is not True
        or parsed.get("target_seen") is not True
        or parsed.get("malformed_lines")
    ):
        return rejected("SYSTEM_ERROR", "dependency_audit")
    if run.get("condition") == "N" and validation.get("library_declarations"):
        return rejected("RULE_VIOLATION", "condition_n_library_dependency")

    if not accepted or validation.get("pass") is not True or validation.get("failure_code") is not None:
        raise ReportError(f"{label} rejected validation has no derived failed validator stage")
    if validation.get("library_audit_complete") is not True:
        raise ReportError(f"{label} accepted validation lacks a complete dependency audit")
    _validation_dependency_audit(
        validation,
        run,
        target_theorem,
        label,
        require_success=True,
    )
    return {
        "status": "accepted",
        "derived_failure_code": None,
        "first_failed_stage": None,
        "validator_command_authentication": validation_command_authentication,
    }


def _validate_proof(
    benchmark_root: Path,
    results_root: Path,
    task: Mapping[str, Any],
    run: Mapping[str, Any],
    usage: Mapping[str, Any],
    usage_path: Path,
    *,
    ultra: bool,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, Mapping[str, Any] | None]:
    label = str(run.get("run_id"))
    accepted_raw = run.get("accepted_submission_log")
    validation_raw = run.get("validation_log")
    submission_raw = run.get("submission_sha256")
    final_raw = run.get("final_submission_sha256")
    if accepted_raw is None:
        if run.get("pass") is True:
            raise ReportError(f"passing run {label} has no retained accepted proof")
        if submission_raw is not None:
            submission_sha = _hex(submission_raw, f"{label} submitted bytes digest")
            if final_raw != submission_sha or run.get("submission_changed_after_acceptance") is not False:
                raise ReportError(f"{label} has incoherent retained unauthorized/rejected bytes")
        elif final_raw is not None:
            raise ReportError(f"{label} has a final submission digest without submitted bytes")
        if validation_raw is not None:
            validation_path = _resolve_result_path(
                results_root, validation_raw, f"{label} rejected validation log"
            )
            validation = read_json(validation_path)
            if validation.get("pass") is not False:
                raise ReportError(f"{label} has an accepted validation without an accepted proof")
            if validation.get("condition") != run.get("condition"):
                raise ReportError(f"{label} rejected validation has the wrong condition")
            validation_auth = _authenticate_validation_log(
                benchmark_root,
                results_root,
                run,
                task,
                validation_path,
                validation,
                candidate_sha256=(submission_sha if submission_raw is not None else None),
                boundary=None,
            )
            validation_auth["hidden_validation_semantics"] = (
                _validate_hidden_validation_semantics(
                    benchmark_root,
                    run,
                    task,
                    validation,
                    accepted=False,
                )
            )
        else:
            if run.get("validation_log_sha256") is not None or run.get(
                "validation_record_sha256"
            ) is not None:
                raise ReportError(f"{label} has validation digests without a validation log")
            validation = None
            validation_auth = None
        if usage.get("submission_boundary_exact") is True:
            raise ReportError(f"{label} exact accepted boundary has no retained accepted proof")
        return None, validation_auth, validation

    # An accepted proof can still lose to a higher-priority, authenticated
    # network RULE_VIOLATION.  In that case it remains valuable audit evidence
    # but the outcome is correctly a charged failure rather than a pass.
    if run.get("pass") is not True:
        network = _mapping(run.get("network_violation"), f"{label} network evidence")
        if run.get("failure_code") != "RULE_VIOLATION" or network.get("detected") is not True:
            raise ReportError(f"failed run {label} improperly claims an accepted proof")
    submission_sha = _hex(submission_raw, f"{label} accepted proof digest")
    if final_raw != submission_sha or run.get("submission_changed_after_acceptance") is not False:
        raise ReportError(f"{label} final proof changed after acceptance")
    accepted = _resolve_result_path(results_root, accepted_raw, f"{label} accepted proof")
    if file_sha256(accepted) != submission_sha:
        raise ReportError(f"{label} accepted proof hash does not match its record")
    validation_path = _resolve_result_path(
        results_root, validation_raw, f"{label} hidden validation log"
    )
    validation = read_json(validation_path)
    validation_declaration_names = runner.library_declaration_names(
        validation.get("library_declarations")
    )
    if (
        validation.get("pass") is not True
        or validation.get("condition") != run.get("condition")
        or validation.get("library_use") != run.get("library_use")
        or validation_declaration_names != run.get("library_declarations")
        or validation.get("library_audit_complete") is not True
    ):
        raise ReportError(f"{label} hidden validation log does not certify the record")
    boundary = None
    if ultra:
        boundary = _authenticated_barrier_artifacts(results_root, usage_path, run, usage, accepted)
    validation_auth = _authenticate_validation_log(
        benchmark_root,
        results_root,
        run,
        task,
        validation_path,
        validation,
        candidate_sha256=submission_sha,
        boundary=boundary,
    )
    validation_auth["hidden_validation_semantics"] = _validate_hidden_validation_semantics(
        benchmark_root,
        run,
        task,
        validation,
        accepted=True,
    )
    return {
        "submission_sha256": submission_sha,
        "accepted_path": accepted.relative_to(results_root).as_posix(),
        "validation_path": validation_path.relative_to(results_root).as_posix(),
        "submission_boundary": boundary,
        "validation_authentication": validation_auth,
    }, validation_auth, validation


def _validate_failure_semantics(
    run: Mapping[str, Any],
    usage: Mapping[str, Any],
    validation: Mapping[str, Any] | None,
    *,
    wall_limit: float,
    token_limit: int,
    scored_failure_seconds: float,
) -> None:
    """Authenticate stopping/accounting facts and the frozen failure priority."""

    label = str(run.get("run_id"))
    passed = run.get("pass") is True
    failure = run.get("failure_code")
    first_valid = run.get("first_valid_seconds")
    actual = _number(run.get("actual_stop_seconds"), f"{label} actual stop time")
    scored = _number(run.get("scored_elapsed_seconds"), f"{label} scored time")
    if run.get("failure_precedence") != ",".join(FAILURE_PRECEDENCE):
        raise ReportError(f"{label} does not record the frozen failure-code priority")
    if run.get("time_measurement") != (
        "authenticated CLOCK_MONOTONIC turn/start write to authenticated nested "
        "submission-boundary publication after outer exec raw-response completion "
        "with inner submit_proof blocked; hidden validation certifies the immutable "
        "requested bytes"
    ):
        raise ReportError(f"{label} does not use the frozen Ultra timing boundary")
    note = run.get("failure_note")
    if not isinstance(note, str) or len(note.encode("utf-8")) > MAX_FAILURE_NOTE_BYTES:
        raise ReportError(f"{label} failure note is missing or exceeds the bounded record size")
    if passed:
        if note != "" or failure is not None:
            raise ReportError(f"{label} passing outcome has failure metadata")
    elif not note.strip() or abs(scored - scored_failure_seconds) > 1e-6:
        raise ReportError(f"{label} failure is not nonempty and charged at the frozen value")

    trigger = usage.get("model_tokens", 0) >= token_limit
    boundary = first_valid is not None
    if boundary:
        boundary_record = _mapping(
            usage.get("submission_boundary"), f"{label} accepted submission boundary"
        )
        if (
            usage.get("submission_boundary_exact") is not True
            or usage.get("drain_complete") is not False
            or usage.get("tree_quiescent") is not False
            or usage.get("active_thread_ids") != [usage.get("root_thread_id")]
            or usage.get("unresolved_thread_ids") != []
            or usage.get("invalid_reasons") != []
            or usage.get("interrupt_requested") is not False
            or usage.get("stop_reason") != "first_valid_proof"
            or boundary_record.get("authenticated") is not True
            or boundary_record.get("status") != "accepted"
            or boundary_record.get("exact") is not True
            or trigger
        ):
            raise ReportError(f"{label} accepted proof is not an exact blocked Ultra boundary")
        first = _number(first_valid, f"{label} first-valid time")
        if first >= wall_limit:
            raise ReportError(f"{label} submitted its accepted proof at or after the time cap")
        if passed and abs(scored - first) > 1e-6:
            raise ReportError(f"{label} pass is not scored at authenticated call observation")
        if not passed and failure != "RULE_VIOLATION":
            raise ReportError(f"{label} accepted proof can fail only for a later network rule event")
        return

    # The frozen app-server contract exposes exact usage only when an upstream
    # response completes.  A wall-clock stop can cancel an in-flight response,
    # so even a resealed record claiming a clean, projection-complete natural
    # drain is only a completed-response lower bound and is not reportable as a
    # scored Ultra outcome.
    if failure == "TIME_LIMIT":
        raise ReportError(
            f"{label} Ultra TIME_LIMIT cannot be an exact natural-drain final"
        )

    if failure == "TOKEN_LIMIT":
        gate = usage.get("provider_token_gate")
        terminal = gate.get("terminal") if isinstance(gate, Mapping) else None
        crossing = terminal.get("crossing") if isinstance(terminal, Mapping) else None
        first_crossing_record = usage.get("first_crossing")
        if (
            not trigger
            or usage.get("submission_boundary_exact") is not False
            or usage.get("submission_boundary") is not None
            or usage.get("drain_complete") is not False
            or usage.get("tree_quiescent") is not False
            or usage.get("invalid_reasons") != []
            or usage.get("interrupt_requested") is not False
            or usage.get("pending_interrupt_response_count") != 0
            or type(usage.get("pending_interrupt_response_count")) is not int
            or usage.get("stop_reason") != "token_limit"
            or not isinstance(terminal, Mapping)
            or terminal.get("phase") != "CLOSED"
            or terminal.get("close_reason") != "token_limit"
            or terminal.get("open_request_ids") != []
            or terminal.get("handlers_quiescent") is not True
            or not isinstance(crossing, Mapping)
            or crossing.get("sole_inflight") is not True
            or crossing.get("release_kind")
            not in {
                runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
                runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            }
            or not isinstance(first_crossing_record, Mapping)
            or first_crossing_record.get("response_id")
            != crossing.get("response_id")
            or first_crossing_record.get("tokens")
            != crossing.get("completed_tokens")
        ):
            raise ReportError(
                f"{label} TOKEN_LIMIT lacks an exact sanitized provider-gate crossing"
            )
        return

    if (
        usage.get("submission_boundary_exact") is not False
        or usage.get("submission_boundary") is not None
        or usage.get("drain_complete") is not True
        or usage.get("tree_quiescent") is not True
        or usage.get("active_thread_ids") != []
        or usage.get("unresolved_thread_ids") != []
        or usage.get("invalid_reasons") != []
        or usage.get("interrupt_requested") is not False
        or usage.get("spawn_linkage_complete") is not True
        or usage.get("descendant_accounting_complete") is not True
        or usage.get("cumulative_projection_complete") is not True
        or usage.get("accounting_complete") is not True
    ):
        raise ReportError(f"{label} failure lacks an exact naturally drained accounting ledger")
    expected_stop_reason = None
    if usage.get("stop_reason") != expected_stop_reason:
        raise ReportError(f"{label} natural stop reason disagrees with its exact ledger")
    validation_failure = validation.get("failure_code") if validation is not None else None
    submission_present = run.get("submission_sha256") is not None or validation is not None
    detected = _mapping(run.get("network_violation"), f"{label} network evidence").get(
        "detected"
    ) is True
    direct_violation = note == (
        "Ultra agents may not create or modify runner-owned Submission.lean"
    )
    system_signal = (
        run.get("agent_exit_code") not in (None, 0)
        or validation_failure == "SYSTEM_ERROR"
        or "system" in note.lower()
        or "adapter" in note.lower()
    )

    # Reconstruct the first applicable observable class in the frozen order.
    if actual >= wall_limit - 1e-3:
        expected_failure = "TIME_LIMIT"
    elif trigger:
        expected_failure = "TOKEN_LIMIT"
    elif not submission_present and not (direct_violation or system_signal):
        expected_failure = "NO_SUBMISSION"
    elif direct_violation or detected or validation_failure == "RULE_VIOLATION":
        expected_failure = "RULE_VIOLATION"
    elif validation_failure in {"SYNTAX_OR_ELAB", "PROOF_ERROR", "SYSTEM_ERROR"}:
        expected_failure = str(validation_failure)
    elif system_signal:
        expected_failure = "SYSTEM_ERROR"
    else:
        raise ReportError(f"{label} failure code has no authenticated causal evidence")
    if failure != expected_failure:
        raise ReportError(
            f"{label} failure code {failure!r} violates priority; expected {expected_failure!r}"
        )
    if failure == "TIME_LIMIT" and actual < wall_limit - 1e-3:
        raise ReportError(f"{label} TIME_LIMIT was recorded before the cap")
    if failure == "TOKEN_LIMIT" and not trigger:
        raise ReportError(f"{label} TOKEN_LIMIT lacks an exact threshold crossing")


def _validate_n_preflight(
    benchmark_root: Path,
    task: Mapping[str, Any],
    run: Mapping[str, Any],
) -> None:
    label = str(run.get("run_id"))
    value = _mapping(run.get("n_preflight"), f"{label} N preflight")
    controlled_path = benchmark_root / "metadata" / "controlled" / f"{task['task_id']}.json"
    controlled = read_json(controlled_path)
    expected_files = len(_list(controlled.get("files"), f"{label} controlled files"))
    if expected_files <= 0:
        raise ReportError(f"{label} controlled task staging is empty")
    staging = _mapping(
        value.get("controlled_task_staging"), f"{label} controlled task staging"
    )
    if set(staging) != {
        "manifest_sha256",
        "verified_files",
        "expected_files",
        "complete",
    }:
        raise ReportError(f"{label} controlled task staging has unexpected fields")
    if (
        staging.get("manifest_sha256") != file_sha256(controlled_path)
        or staging.get("expected_files") != expected_files
        or staging.get("verified_files") != expected_files
        or staging.get("complete") is not True
    ):
        raise ReportError(f"{label} does not authenticate complete controlled task staging")
    if value.get("filesystem_leaks") != []:
        raise ReportError(f"{label} N preflight found a filesystem leak")
    scan = _mapping(value.get("filesystem_scan"), f"{label} N filesystem scan")
    markers = _list(scan.get("markers"), f"{label} N filesystem markers")
    if (
        scan.get("root") != "."
        or markers != list(preflight.DEFAULT_MARKERS)
        or _integer(scan.get("regular_file_count"), f"{label} scanned regular files")
        < expected_files
        or _integer(scan.get("directory_count"), f"{label} scanned directories") < 0
        or scan.get("symlink_count") != 0
        or _integer(
            scan.get("content_limit_bytes"), f"{label} preflight content limit", positive=True
        )
        != 4 * 1024 * 1024
    ):
        raise ReportError(f"{label} N filesystem scan is incomplete")
    probe = _mapping(value.get("import_probe"), f"{label} N import probe")
    command = _list(probe.get("command"), f"{label} N import-probe command")
    expected_probe_options = (
        "--condition",
        "N",
        "--workspace",
        "--toolchain-root",
        "--packages-root",
        "--shared-olean-root",
        "--source",
    )
    agent_command = _list(run.get("agent_command"), f"{label} agent command")
    expected_executable = agent_command[0] if agent_command else None
    expected_workspace = _option(agent_command, "--workspace", label)
    expected_roots = tuple(
        _option(agent_command, option, label)
        for option in ("--toolchain-root", "--packages-root", "--shared-olean-root")
    )
    command_shape_ok = False
    if len(command) == 15 and all(isinstance(item, str) and item for item in command):
        executable = Path(command[0])
        adapter = Path(command[1])
        workspace = Path(command[6])
        probe_source = Path(command[14])
        roots = (Path(command[8]), Path(command[10]), Path(command[12]))
        command_shape_ok = (
            executable.is_absolute()
            and command[0] == expected_executable
            and adapter.resolve()
            == (benchmark_root / "tools" / "lean_isolated.py").resolve()
            and command[2] == "probe"
            and command[3] == expected_probe_options[0]
            and command[4] == expected_probe_options[1]
            and command[5] == expected_probe_options[2]
            and command[7] == expected_probe_options[3]
            and command[9] == expected_probe_options[4]
            and command[11] == expected_probe_options[5]
            and command[13] == expected_probe_options[6]
            and workspace.is_absolute()
            and command[6] == expected_workspace
            and workspace.name.startswith("highambench-run-")
            and probe_source.is_absolute()
            and probe_source.parent == workspace
            and probe_source.name.startswith("HighamBenchNoLibraryProbe_")
            and probe_source.suffix == ".lean"
            and all(root.is_absolute() for root in roots)
            and tuple(command[index] for index in (8, 10, 12)) == expected_roots
        )
    output = probe.get("output")
    if not isinstance(output, str):
        raise ReportError(f"{label} N import-probe output is not text")
    lowered = output.lower()
    recognizable_missing_import = "numstability" in lowered and any(
        marker in lowered for marker in preflight.MISSING_IMPORT_MARKERS
    )
    exit_code = probe.get("exit_code")
    if (
        value.get("ok") is not True
        or value.get("complete") is not True
        or probe.get("attempted") is not True
        or probe.get("reliable") is not True
        or probe.get("importable") is not False
        or probe.get("timed_out") is not False
        or probe.get("system_error") is not None
        or not isinstance(exit_code, int)
        or isinstance(exit_code, bool)
        or exit_code == 0
        or not command_shape_ok
        or not isinstance(probe.get("output_truncated"), bool)
        or probe.get("conclusion")
        != "compiler reported that the forbidden module is absent"
        or not recognizable_missing_import
    ):
        raise ReportError(f"{label} does not prove a reliable failed NumStability import")


def _verify_frozen_manifest_root(
    project_root: Path,
    root: Path,
    descriptor_path: Any,
    descriptor_sha256: Any,
    label: str,
    cache: dict[tuple[str, str], bool],
) -> None:
    root = root.resolve()
    key = (label, str(root))
    if cache.get(key):
        return
    if not root.is_dir() or root.is_symlink():
        raise ReportError(f"{label} root is not a regular directory")
    manifest_path = _resolve_frozen_path(project_root, descriptor_path, f"{label} manifest")
    if file_sha256(manifest_path) != _hex(descriptor_sha256, f"{label} manifest digest"):
        raise ReportError(f"{label} manifest digest is stale")
    manifest = read_json(manifest_path)
    entries = _list(manifest.get("files"), f"{label} manifest files")
    expected_paths: set[str] = set()
    for index, raw in enumerate(entries):
        entry = _mapping(raw, f"{label} manifest entry {index}")
        relative = _safe_relative(entry.get("path"), f"{label} manifest entry {index}")
        name = relative.as_posix()
        if name in expected_paths:
            raise ReportError(f"{label} manifest repeats {name}")
        expected_paths.add(name)
        path = root / relative
        if (
            not path.is_file()
            or path.is_symlink()
            or path.stat().st_size
            != _integer(entry.get("bytes"), f"{label} bytes for {name}")
            or file_sha256(path) != _hex(entry.get("sha256"), f"{label} digest for {name}")
        ):
            raise ReportError(f"{label} root differs at {name}")
    actual_paths: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ReportError(f"{label} root contains a symlink")
        if path.is_file():
            actual_paths.add(path.relative_to(root).as_posix())
        elif not path.is_dir():
            raise ReportError(f"{label} root contains a special file")
    if actual_paths != expected_paths:
        raise ReportError(f"{label} root is not the exact frozen manifest projection")
    cache[key] = True


def _verify_frozen_library_source(
    project_root: Path,
    source_root: Path,
    root_file: Path,
    descriptor_path: Any,
    descriptor_sha256: Any,
    cache: dict[tuple[str, str], bool],
) -> int:
    project_root = project_root.resolve()
    expected_source = project_root / "NumStability"
    expected_root_file = project_root / "NumStability.lean"
    if (
        not source_root.is_absolute()
        or not root_file.is_absolute()
        or source_root.resolve() != expected_source
        or root_file.resolve() != expected_root_file
        or not source_root.is_dir()
        or source_root.is_symlink()
        or not root_file.is_file()
        or root_file.is_symlink()
    ):
        raise ReportError("condition L does not expose the frozen NumStability source paths")
    manifest_path = _resolve_frozen_path(
        project_root, descriptor_path, "NumStability source manifest"
    )
    if file_sha256(manifest_path) != _hex(
        descriptor_sha256, "NumStability source manifest digest"
    ):
        raise ReportError("NumStability source manifest digest is stale")
    manifest = read_json(manifest_path)
    entries = _list(manifest.get("files"), "NumStability source manifest files")
    key = ("NumStability source", str(project_root))
    if cache.get(key):
        return len(entries)
    expected_paths: set[str] = set()
    for index, raw in enumerate(entries):
        entry = _mapping(raw, f"NumStability source manifest entry {index}")
        relative = _safe_relative(entry.get("path"), f"NumStability source entry {index}")
        name = relative.as_posix()
        if name != "NumStability.lean" and relative.parts[:1] != ("NumStability",):
            raise ReportError("NumStability source manifest contains an out-of-scope path")
        if name in expected_paths:
            raise ReportError(f"NumStability source manifest repeats {name}")
        expected_paths.add(name)
        path = project_root / relative
        if (
            not path.is_file()
            or path.is_symlink()
            or path.stat().st_size
            != _integer(entry.get("bytes"), f"NumStability source bytes for {name}")
            or file_sha256(path)
            != _hex(entry.get("sha256"), f"NumStability source digest for {name}")
        ):
            raise ReportError(f"NumStability source differs at {name}")
    actual_paths = {"NumStability.lean"}
    for path in source_root.rglob("*"):
        if path.is_symlink():
            raise ReportError("NumStability source tree contains a symlink")
        if path.is_file():
            actual_paths.add(path.relative_to(project_root).as_posix())
        elif not path.is_dir():
            raise ReportError("NumStability source tree contains a special file")
    if actual_paths != expected_paths:
        raise ReportError("NumStability source is not the exact frozen manifest tree")
    cache[key] = True
    return len(entries)


def _authenticate_execution_roots(
    benchmark_root: Path,
    config: Mapping[str, Any],
    environment: Mapping[str, Any],
    freeze: Mapping[str, Any],
    task: Mapping[str, Any],
    run: Mapping[str, Any],
    cache: dict[tuple[str, str], bool],
) -> dict[str, str]:
    label = str(run.get("run_id"))
    command = _list(run.get("agent_command"), f"{label} agent command")
    if len(command) < 2 or not all(isinstance(item, str) and item for item in command):
        raise ReportError(f"{label} agent command is malformed")
    adapter = (benchmark_root / "tools" / "codex_isolated.py").resolve()
    if Path(command[1]).resolve() != adapter:
        raise ReportError(f"{label} does not use the frozen filesystem adapter")
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    runtime = _mapping(environment.get("runtime"), "environment runtime")
    freeze_python = _mapping(freeze.get("python"), "freeze Python")
    runtime_python = _mapping(runtime.get("python"), "environment Python")
    python_digest = _hex(frozen.get("python_binary_sha256"), "frozen Python digest")
    if (
        freeze_python.get("binary_sha256") != python_digest
        or runtime_python.get("binary_sha256") != python_digest
    ):
        raise ReportError("Python binary digest disagrees across the production freeze")
    executable = Path(command[0])
    if (
        not executable.is_absolute()
        or not executable.is_file()
        or file_sha256(executable) != python_digest
    ):
        raise ReportError(f"{label} agent Python executable is not freeze-bound")

    toolchain = Path(str(_option(command, "--toolchain-root", label)))
    packages = Path(str(_option(command, "--packages-root", label)))
    shared = Path(str(_option(command, "--shared-olean-root", label)))
    for root, name in ((toolchain, "toolchain"), (packages, "packages"), (shared, "shared olean")):
        if not root.is_absolute() or not root.is_dir() or root.is_symlink():
            raise ReportError(f"{label} {name} root is not a frozen absolute directory")

    lean_binary = toolchain / "bin" / "lean"
    lean_digest = _hex(frozen.get("lean_binary_sha256"), "frozen Lean binary digest")
    if (
        not lean_binary.is_file()
        or file_sha256(lean_binary) != lean_digest
    ):
        raise ReportError(f"{label} toolchain root has the wrong Lean binary")
    compiled_path = frozen.get("compiled_environment_summary")
    compiled_sha = frozen.get("compiled_environment_summary_sha256")
    lean_environment = _mapping(environment.get("lean"), "environment Lean")
    if (
        lean_environment.get("compiled_environment_summary") != compiled_path
        or lean_environment.get("compiled_environment_summary_sha256") != compiled_sha
    ):
        raise ReportError("compiled-environment descriptor disagrees across metadata")
    compiled_summary_path = _resolve_frozen_path(
        benchmark_root, compiled_path, "compiled environment summary"
    )
    if file_sha256(compiled_summary_path) != _hex(compiled_sha, "compiled environment digest"):
        raise ReportError("compiled-environment summary digest is stale")
    toolchain_key = ("toolchain", str(toolchain.resolve()))
    if not cache.get(toolchain_key):
        compiled_summary = read_json(compiled_summary_path)
        expected_toolchain = _mapping(
            compiled_summary.get("toolchain"), "compiled environment toolchain"
        )
        actual_toolchain = {"relative_root": ".", **run_matrix.exact_tree_digest(toolchain)}
        if dict(expected_toolchain) != actual_toolchain:
            raise ReportError(f"{label} toolchain root differs from the frozen tree")
        cache[toolchain_key] = True

    packages_path = frozen.get("packages_runtime_manifest")
    packages_sha = frozen.get("packages_runtime_manifest_sha256")
    frozen_packages = _mapping(freeze.get("packages_runtime"), "freeze packages runtime")
    if (
        runtime.get("packages_runtime_manifest") != packages_path
        or runtime.get("packages_runtime_manifest_sha256") != packages_sha
        or frozen_packages.get("path") != packages_path
        or frozen_packages.get("sha256") != packages_sha
    ):
        raise ReportError("packages-runtime descriptor disagrees across the production freeze")
    _verify_frozen_manifest_root(
        _project_root(benchmark_root),
        packages,
        packages_path,
        packages_sha,
        "packages runtime",
        cache,
    )

    bundles = _mapping(
        lean_environment.get("shared_olean_bundles"), "shared olean bundles"
    )
    bundle = _mapping(bundles.get(task["paper_id"]), f"shared olean {task['paper_id']}")
    expected_shared = set(bundle)
    actual_shared: set[str] = set()
    for path in shared.rglob("*"):
        if path.is_symlink():
            raise ReportError(f"{label} shared olean root contains a symlink")
        if path.is_file():
            relative = path.relative_to(shared).as_posix()
            actual_shared.add(relative)
            if file_sha256(path) != _hex(bundle.get(relative), f"shared olean {relative}"):
                raise ReportError(f"{label} shared olean root differs at {relative}")
    if actual_shared != expected_shared:
        raise ReportError(f"{label} shared olean root is not the frozen paper bundle")

    library_options = ("--library-source", "--library-root-file", "--library-olean")
    if run.get("condition") == "N":
        if any(_option(command, option, label) is not None for option in library_options):
            raise ReportError(f"{label} condition N command exposes a library mount")
    else:
        library_values = {
            option: _option(command, option, label) for option in library_options
        }
        if any(value is None for value in library_values.values()):
            raise ReportError(f"{label} condition L command omits a library mount")
        source_manifest_path = frozen.get("numstability_source_manifest")
        source_manifest_sha = frozen.get("numstability_source_manifest_sha256")
        compiled_manifest_path = frozen.get("numstability_compiled_manifest")
        compiled_manifest_sha = frozen.get("numstability_compiled_manifest_sha256")
        if (
            lean_environment.get("numstability_source_manifest")
            != source_manifest_path
            or lean_environment.get("numstability_source_manifest_sha256")
            != source_manifest_sha
            or lean_environment.get("numstability_compiled_manifest")
            != compiled_manifest_path
            or lean_environment.get("numstability_compiled_manifest_sha256")
            != compiled_manifest_sha
        ):
            raise ReportError("NumStability manifest descriptors disagree across metadata")
        source_count = _verify_frozen_library_source(
            _project_root(benchmark_root),
            Path(str(library_values["--library-source"])),
            Path(str(library_values["--library-root-file"])),
            source_manifest_path,
            source_manifest_sha,
            cache,
        )
        compiled_root = Path(str(library_values["--library-olean"]))
        _verify_frozen_manifest_root(
            _project_root(benchmark_root),
            compiled_root,
            compiled_manifest_path,
            compiled_manifest_sha,
            "NumStability compiled",
            cache,
        )
        compiled_manifest = read_json(
            _resolve_frozen_path(
                benchmark_root,
                compiled_manifest_path,
                "NumStability compiled manifest",
            )
        )
        compiled_count = len(
            _list(compiled_manifest.get("files"), "NumStability compiled manifest files")
        )
        freeze_lean = _mapping(freeze.get("lean"), "freeze Lean")
        if (
            freeze_lean.get("source_files_verified") != source_count
            or freeze_lean.get("compiled_files_verified") != compiled_count
        ):
            raise ReportError("NumStability mounts disagree with the authenticated freeze")
    return {
        "python": command[0],
        "toolchain": str(toolchain),
        "packages": str(packages),
        "shared": str(shared),
    }


def _validation_command_contract(
    benchmark_root: Path,
    run: Mapping[str, Any],
    task: Mapping[str, Any],
) -> tuple[str, list[str], list[str]]:
    label = str(run.get("run_id"))
    condition = str(run.get("condition"))
    agent_command = _list(run.get("agent_command"), f"{label} agent command")
    lean_base = [
        agent_command[0],
        str((benchmark_root / "tools" / "lean_isolated.py").resolve()),
        "--condition",
        condition,
        "--workspace",
        "{workspace}",
        "--toolchain-root",
        str(_option(agent_command, "--toolchain-root", label)),
        "--packages-root",
        str(_option(agent_command, "--packages-root", label)),
        "--shared-olean-root",
        str(_option(agent_command, "--shared-olean-root", label)),
    ]
    library_options = ("--library-source", "--library-root-file", "--library-olean")
    if condition == "L":
        for option in library_options:
            lean_base.extend((option, str(_option(agent_command, option, label))))
    elif any(option in agent_command for option in library_options):
        raise ReportError(f"{label} condition N command exposes a library mount")
    compile_template = lean_base[:2] + ["olean"] + lean_base[2:] + [
        "--source",
        "{checked_submission}",
    ]
    target_theorem = f"HighamBench.{task['declaration']}"
    audit_template = lean_base[:2] + ["audit"] + lean_base[2:] + [
        "--source",
        "{checked_submission}",
        "--audit-helper",
        str((benchmark_root / "tools" / "dependency_audit.lean").resolve()),
        "--submission-module",
        "{submission_module}",
        "--target-theorem",
        target_theorem,
        "--expected-module",
        "{expected_module}",
        "--expected-theorem",
        "{expected_theorem}",
        "--local-modules-file",
        "{local_modules_file}",
    ]
    target_relative = Path(task["target_file"]).resolve().relative_to(
        benchmark_root.resolve()
    ).as_posix()
    controlled_path = benchmark_root / "metadata" / "controlled" / f"{task['task_id']}.json"
    contract = {
        "condition": condition,
        "submission_relative": "Submission.lean",
        "canonical_relative": f"task/{target_relative}",
        "target_theorem": target_theorem,
        "compile_command": compile_template,
        "audit_command": audit_template,
        "controlled_manifest_sha256": file_sha256(controlled_path),
        "reject_workspace_local_module_imports": True,
    }
    return document_sha256(contract), compile_template, audit_template


def _authenticate_validation_commands(
    benchmark_root: Path,
    run: Mapping[str, Any],
    task: Mapping[str, Any],
    validation: Mapping[str, Any],
) -> dict[str, Any]:
    label = str(run.get("run_id"))
    contract_digest, compile_template, audit_template = _validation_command_contract(
        benchmark_root, run, task
    )
    authentication = _mapping(
        validation.get("authentication"), f"{label} validation authentication"
    )
    if authentication.get("validator_contract_sha256") != contract_digest:
        raise ReportError(f"{label} validation uses a forged validator-command contract")
    compile_raw = validation.get("compile")
    if compile_raw is None:
        return {
            "validator_contract_sha256": contract_digest,
            "checked_id": None,
        }
    compile_result = _mapping(compile_raw, f"{label} candidate compile")
    compile_command = _list(compile_result.get("command"), f"{label} candidate command")
    checked_source = Path(str(_option(compile_command, "--source", label)))
    match = re.fullmatch(r"HighamBenchChecked_([0-9a-f]{32})\.lean", checked_source.name)
    if match is None or not checked_source.is_absolute():
        raise ReportError(f"{label} candidate compile does not name the generated checked source")
    generated_id = match.group(1)
    workspace = checked_source.parent
    expected_source = workspace / f"HighamBenchExpected_{generated_id}.lean"
    values = {
        "{workspace}": str(workspace),
        "{checked_submission}": str(checked_source),
        "{submission_module}": f"HighamBenchChecked_{generated_id}",
        "{expected_module}": f"HighamBenchExpected_{generated_id}",
        "{expected_theorem}": f"HighamBench.highamBenchExpected_{generated_id}",
        "{local_modules_file}": str(
            workspace / f"{validator.LOCAL_MODULES_FILENAME}-{generated_id}"
        ),
    }

    def rendered(template: Sequence[str], *, expected: bool = False) -> list[str]:
        replacements = dict(values)
        if expected:
            replacements["{checked_submission}"] = str(expected_source)
        return [replacements.get(item, item) for item in template]

    if compile_command != rendered(compile_template):
        raise ReportError(f"{label} candidate compile command is not contract-derived")
    expected_raw = validation.get("expected_statement_compile")
    if expected_raw is not None and "command" in _mapping(
        expected_raw, f"{label} expected compile"
    ):
        expected_command = _list(
            expected_raw.get("command"),
            f"{label} expected compile command",
        )
        if expected_command != rendered(compile_template, expected=True):
            raise ReportError(f"{label} expected compile command is not contract-derived")
    audit_raw = validation.get("dependency_audit")
    if audit_raw is not None and "command" in _mapping(audit_raw, f"{label} dependency audit"):
        audit_command = _list(audit_raw.get("command"), f"{label} dependency-audit command")
        if audit_command != rendered(audit_template):
            raise ReportError(f"{label} dependency-audit command is not contract-derived")
    return {
        "validator_contract_sha256": contract_digest,
        "checked_id": generated_id,
    }


def _validate_record(
    benchmark_root: Path,
    results_root: Path,
    config: Mapping[str, Any],
    environment: Mapping[str, Any],
    freeze: Mapping[str, Any],
    task: Mapping[str, Any],
    planned: Mapping[str, Any],
    run: Mapping[str, Any],
    hardware_records: Mapping[str, Mapping[str, Any]],
    runtime_binding_cache: dict[tuple[str, str], bool],
) -> dict[str, Any]:
    label = str(planned["run_id"])
    if run.get("schema_version") != 1 or run.get("kind") != "highambench-run":
        raise ReportError(f"{label} is not a supported final run record")
    matrix_authentication = _validate_matrix_record_authentication(run, label)
    exact = {
        "run_id": planned["run_id"],
        "pair_id": planned["pair_id"],
        "task_id": planned["task_id"],
        "paper_id": EXPECTED_PAPER,
        "paper_sha256": task["paper_sha256"],
        "tier": task["tier"],
        "condition": planned["condition"],
        "repetition_id": planned["repetition_id"],
        "backend_seed": planned["backend_seed"],
        "pair_order": planned["pair_order"],
        "order_index": planned["order_index"],
    }
    for field, wanted in exact.items():
        if run.get(field) != wanted:
            raise ReportError(f"{label} has {field}={run.get(field)!r}; expected {wanted!r}")
    expected_agent = _expected_agent(config)
    if run.get("agent") != expected_agent:
        raise ReportError(f"{label} does not use the frozen agent/model/effort")
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    if run.get("environment_id") != frozen.get("environment_id"):
        raise ReportError(f"{label} has the wrong environment ID")
    _authenticate_execution_roots(
        benchmark_root,
        config,
        environment,
        freeze,
        task,
        run,
        runtime_binding_cache,
    )
    hardware = _mapping(run.get("allocation_hardware"), f"{label} allocation hardware")
    if set(hardware) != {"path", "sha256", "record_sha256", "job_id"}:
        raise ReportError(f"{label} has a malformed allocation-hardware descriptor")
    hardware_path = str(hardware.get("path"))
    authenticated_hardware = hardware_records.get(hardware_path)
    if authenticated_hardware is None or any(
        hardware.get(field) != authenticated_hardware.get(field)
        for field in ("path", "sha256", "record_sha256", "job_id")
    ):
        raise ReportError(f"{label} is not linked to an authenticated allocation record")
    wrapper = _mapping(run.get("frozen_run_verification"), f"{label} freeze wrapper")
    if wrapper.get("freeze_check") != freeze or wrapper.get("freeze_check_sha256") != document_sha256(freeze):
        raise ReportError(f"{label} does not embed the current authenticated freeze check")
    limits = _mapping(config.get("limits"), "config limits")
    run_limits = _mapping(run.get("limits"), f"{label} limits")
    if (
        run_limits.get("time_seconds") != limits.get("wall_clock_seconds")
        or run_limits.get("model_tokens") != limits.get("total_model_tokens")
        or run_limits.get("prompt_startup_seconds")
        != limits.get("prompt_startup_timeout_seconds")
    ):
        raise ReportError(f"{label} used different resource limits")
    started = _iso(run.get("started_at_utc"), f"{label} start")
    finished = _iso(run.get("finished_at_utc"), f"{label} finish")
    if finished < started:
        raise ReportError(f"{label} finishes before it starts")
    passed = run.get("pass")
    if not isinstance(passed, bool) or run.get("useful_work_started") is not True:
        raise ReportError(f"{label} is not a usable final measurement record")
    if not (
        type(run.get("agent_exit_code")) is int
        and run.get("agent_exit_code") == 0
    ):
        raise ReportError(f"{label} does not have a clean adapter exit")
    failure = run.get("failure_code")
    if (passed and failure is not None) or (not passed and failure not in FAILURE_CODES):
        raise ReportError(f"{label} has an incoherent outcome/failure code")
    actual = _number(run.get("actual_stop_seconds"), f"{label} actual time")
    scored_time = _number(run.get("scored_elapsed_seconds"), f"{label} scored time")
    wall_limit = _number(limits.get("wall_clock_seconds"), "wall-clock limit")
    validation_reserve = _number(
        limits.get("post_submission_validation_reserve_seconds"),
        "post-submission validation reserve",
    )
    if validation_reserve != POST_SUBMISSION_VALIDATION_RESERVE_SECONDS:
        raise ReportError(f"{label} does not use the frozen post-submission validation reserve")
    if actual > wall_limit + validation_reserve or scored_time > wall_limit:
        raise ReportError(f"{label} exceeds the frozen run plus hidden-validation allowance")
    first_valid = run.get("first_valid_seconds")
    if passed:
        first = _number(first_valid, f"{label} first-valid time")
        if abs(scored_time - first) > 1e-6:
            raise ReportError(f"{label} scored time is not first-valid-proof time")
        if actual - first > validation_reserve + 1e-6:
            raise ReportError(
                f"{label} exceeds the frozen post-submission validation reserve"
            )
    else:
        if scored_time != float(limits.get("failure_scored_time_seconds")):
            raise ReportError(f"{label} failed run is not charged the fixed failure time")
        if first_valid is not None:
            first = _number(first_valid, f"{label} first-valid time")
            if actual - first > validation_reserve + 1e-6:
                raise ReportError(
                    f"{label} exceeds the frozen post-submission validation reserve"
                )
    network = _mapping(run.get("network_violation"), f"{label} network evidence")
    detected = network.get("detected")
    events = network.get("event_count")
    if not isinstance(detected, bool) or network.get("integrity_ok") is not True or not isinstance(
        events, int
    ) or isinstance(events, bool) or events < 0:
        raise ReportError(f"{label} has malformed or unauthenticated network evidence")
    if passed and (detected or events != 0):
        raise ReportError(f"passing run {label} contains a network violation")
    if detected:
        if passed or events <= 0 or failure not in {
            "TIME_LIMIT",
            "TOKEN_LIMIT",
            "NO_SUBMISSION",
            "RULE_VIOLATION",
        }:
            raise ReportError(f"{label} network event contradicts the frozen failure priority")
        marker = _resolve_result_path(
            results_root, network.get("saved_marker_log"), f"{label} saved network marker"
        )
        if file_sha256(marker) != _hex(network.get("marker_sha256"), f"{label} network marker digest"):
            raise ReportError(f"{label} saved network marker failed authentication")
    elif events != 0:
        raise ReportError(f"{label} says no network violation but records events")
    library_use = run.get("library_use")
    declarations = run.get("library_declarations")
    if not isinstance(declarations, list) or not all(
        isinstance(item, str) and item for item in declarations
    ):
        raise ReportError(f"{label} has incomplete library-use evidence")
    if library_use not in (True, False, None):
        raise ReportError(f"{label} has an invalid library-use classification")
    if isinstance(library_use, bool) and (library_use is True) != bool(declarations):
        raise ReportError(f"{label} library-use Boolean disagrees with declarations")
    if library_use is None and declarations:
        raise ReportError(f"{label} has declarations without a completed library audit")
    if run.get("condition") == "N":
        if library_use is not False or declarations:
            raise ReportError(f"{label} does not prove condition-N library absence")
        _validate_n_preflight(benchmark_root, task, run)
    elif run.get("n_preflight") is not None:
        raise ReportError(f"{label} condition L unexpectedly carries an N preflight")
    elif passed and not isinstance(library_use, bool):
        raise ReportError(f"passing L run {label} lacks a completed library-use classification")
    if first_valid is not None and not passed and not (
        failure == "RULE_VIOLATION" and detected is True
    ):
        raise ReportError(f"failed run {label} has an unexplained accepted-proof timestamp")
    _validate_protocol(run, ultra=expected_agent["reasoning_effort"] == "ultra")
    effective_prompt = _validate_prompt(benchmark_root, config, task, run)
    usage, usage_path = _validate_raw_usage(
        results_root, run, token_limit=_integer(limits.get("total_model_tokens"), "token limit", positive=True)
    )
    proof, validation_auth, validation = _validate_proof(
        benchmark_root,
        results_root,
        task,
        run,
        usage,
        usage_path,
        ultra=expected_agent["reasoning_effort"] == "ultra",
    )
    prompt_release = _validate_prompt_release(
        results_root,
        config,
        run,
        usage,
        effective_prompt,
        proof,
    )
    provider_gate = construction_report._authenticate_provider_gate_record(
        run,
        artifact_path=runner.provider_gate_paths(usage_path.resolve())["final"],
        label=label,
    )
    _validate_failure_semantics(
        run,
        usage,
        validation,
        wall_limit=wall_limit,
        token_limit=_integer(limits.get("total_model_tokens"), "token limit", positive=True),
        scored_failure_seconds=_number(
            limits.get("failure_scored_time_seconds"), "fixed failure scored time"
        ),
    )
    return {
        "run_id": label,
        "pair_id": run["pair_id"],
        "task_id": run["task_id"],
        "tier": run["tier"],
        "condition": run["condition"],
        "repetition_id": run["repetition_id"],
        "pass": passed,
        "failure_code": failure,
        "failure_note": str(run.get("failure_note", "")),
        "actual_stop_seconds": actual,
        "scored_elapsed_seconds": scored_time,
        "model_tokens": usage["model_tokens"],
        "input_tokens": usage["input_tokens"],
        "cached_input_tokens": usage["cached_input_tokens"],
        "output_tokens": usage["output_tokens"],
        "thread_count": usage.get("thread_count", 1),
        "response_count": usage.get("response_count", usage.get("call_count")),
        "provider_gate_endpoint": provider_gate["endpoint"],
        "provider_gate_record_sha256": provider_gate["record_sha256"],
        "provider_requests_quiescent": provider_gate[
            "provider_requests_quiescent"
        ],
        "tree_quiescent": provider_gate["tree_quiescent"],
        "library_use": library_use,
        "library_declarations": list(declarations),
        "started_at_utc": run["started_at_utc"],
        "finished_at_utc": run["finished_at_utc"],
        "allocation_hardware": dict(hardware),
        "matrix_attempt": matrix_authentication["matrix_attempt"],
        "matrix_record_sha256": matrix_authentication["matrix_record_sha256"],
        "prompt_release_authentication": prompt_release,
        "proof": proof,
        "validation_authentication": validation_auth,
    }


def _freeze_check(
    benchmark_root: Path,
    results_root: Path,
    config: Mapping[str, Any],
    environment: Mapping[str, Any],
    manifest: Mapping[str, Any],
    run_order: Mapping[str, Any],
    release_summary: Mapping[str, Any],
    canaries: Mapping[str, Mapping[str, Any]],
) -> tuple[dict[str, Any], dict[str, str]]:
    freeze_path = results_root / "freeze_check.json"
    freeze = read_json(freeze_path)
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    metadata_hashes = {
        "config": document_sha256(config),
        "environment": document_sha256(environment),
        "manifest": document_sha256(manifest),
        "run_order": document_sha256(run_order),
    }
    if (
        freeze.get("schema_version") != 1
        or freeze.get("kind") != "highambench-frozen-run-verification"
        or freeze.get("ok") is not True
        or freeze.get("benchmark_id") != config.get("benchmark_id")
        or freeze.get("environment_id") != frozen.get("environment_id")
        or freeze.get("environment_bundle_sha256") != frozen.get("environment_bundle_sha256")
        or freeze.get("metadata_document_sha256") != metadata_hashes
    ):
        raise ReportError("results freeze_check.json is stale or incomplete")
    freeze_release = _mapping(freeze.get("release_manifest"), "freeze release manifest")
    verification = _mapping(freeze_release.get("verification"), "freeze release verification")
    if (
        freeze_release.get("sha256") != release_summary["sha256"]
        or freeze_release.get("file_count") != release_summary["file_count"]
        or verification.get("ok") is not True
        or verification.get("expected") != release_summary["file_count"]
        or verification.get("verified") != release_summary["file_count"]
        or verification.get("missing") != []
        or verification.get("changed") != []
    ):
        raise ReportError("freeze check does not contain a complete current release verification")
    if freeze.get("agent") != {
        **_expected_agent(config),
        "binary_sha256": frozen.get("agent_binary_sha256"),
        **({"ultra_orchestration": frozen.get("ultra_orchestration")} if frozen.get("ultra_orchestration") is not None else {}),
    }:
        raise ReportError("freeze check agent identity is not current")
    limits = _mapping(config.get("limits"), "config limits")
    if freeze.get("limits") != {
        "wall_clock_seconds": limits.get("wall_clock_seconds"),
        "total_model_tokens": limits.get("total_model_tokens"),
        "prompt_startup_timeout_seconds": limits.get(
            "prompt_startup_timeout_seconds"
        ),
        "post_submission_validation_reserve_seconds": limits.get(
            "post_submission_validation_reserve_seconds"
        ),
    }:
        raise ReportError("freeze check has different resource limits")
    if freeze.get("host_class") != environment.get("host_class"):
        raise ReportError("freeze check hardware class differs from environment.json")
    if freeze.get("token_control") != config.get("token_control"):
        raise ReportError("freeze check token-control contract is stale")
    for field, key in (
        ("token_control_canary", "token_control"),
        ("ultra_orchestration_canary", "ultra_orchestration"),
    ):
        summary = _mapping(freeze.get(field), f"freeze {field}")
        expected = canaries[key]
        if any(summary.get(name) != expected[name] for name in ("path", "sha256", "status")):
            raise ReportError(f"freeze check has stale {field} evidence")
    return freeze, metadata_hashes


GPU_ENVIRONMENT_KEYS = (
    "SLURM_GPUS_ON_NODE",
    "SLURM_JOB_GPUS",
    "CUDA_VISIBLE_DEVICES",
)


def _validate_zero_gpu_alloc_tres(value: Any, label: str) -> str:
    """Authenticate a raw Slurm AllocTRES string as an unambiguous zero-GPU grant."""
    if not isinstance(value, str) or not value:
        raise ReportError(f"{label} must be a nonempty raw AllocTRES string")
    seen: set[str] = set()
    for raw_token in value.split(","):
        if raw_token.count("=") != 1:
            raise ReportError(f"{label} has a malformed key=count token")
        key, count = raw_token.split("=", 1)
        if (
            not key
            or not count
            or re.fullmatch(r"[^,\s=]+", key) is None
            or re.fullmatch(r"[^,\s=]+", count) is None
            or key in seen
        ):
            raise ReportError(f"{label} has a malformed or duplicate key=count token")
        seen.add(key)
        lowered = key.lower()
        if lowered.startswith("gres/gpu") and not key.startswith("gres/gpu"):
            raise ReportError(f"{label} has a malformed GPU TRES key")
        if key.startswith("gres/gpu"):
            if re.fullmatch(
                r"gres/gpu(?::[A-Za-z0-9][A-Za-z0-9_.+-]*)?", key
            ) is None:
                raise ReportError(f"{label} has a malformed GPU TRES key")
            if re.fullmatch(r"(?:0|[1-9][0-9]*)", count) is None:
                raise ReportError(f"{label} has a malformed GPU TRES count")
            if int(count) != 0:
                raise ReportError(f"{label} records a nonzero GPU allocation")
    return value


def _validate_zero_gpu_environment(value: Any, label: str) -> dict[str, Any]:
    environment = _mapping(value, label)
    if set(environment) != set(GPU_ENVIRONMENT_KEYS):
        raise ReportError(f"{label} does not contain the exact GPU environment keys")
    for key in GPU_ENVIRONMENT_KEYS:
        observed = environment.get(key)
        if observed is not None and not isinstance(observed, str):
            raise ReportError(f"{label} {key} is neither JSON null nor a string")
        allowed = (None, "", "0") if key == "SLURM_GPUS_ON_NODE" else (None, "")
        if observed not in allowed:
            raise ReportError(f"{label} {key} does not authenticate a zero-GPU environment")
    return dict(environment)


def _validate_hardware_records(
    results_root: Path,
    environment: Mapping[str, Any],
    release_sha: str,
    freeze_sha: str,
) -> dict[str, dict[str, Any]]:
    directory = results_root / "allocation_hardware"
    if not directory.is_dir():
        raise ReportError("results root has no authenticated allocation_hardware records")
    records: dict[str, dict[str, Any]] = {}
    expected_top_keys = {
        "schema_version",
        "kind",
        "job_id",
        "hostname",
        "measurement_environment",
        "host_class",
        "host",
        "allocation",
        "slurm",
        "scheduler_sharing",
        "record_sha256",
    }
    frozen_host = dict(_mapping(environment.get("host_class"), "frozen host class"))
    for path in sorted(directory.glob("*.json")):
        value = read_json(path)
        if (
            set(value) != expected_top_keys
            or value.get("schema_version") != 1
            or value.get("kind") != "highambench-allocation-hardware-record"
        ):
            raise ReportError(f"unexpected hardware record kind: {path}")
        self_hash = _hex(value.get("record_sha256"), f"hardware record {path.name} self-hash")
        unsigned = dict(value)
        unsigned.pop("record_sha256")
        if document_sha256(unsigned) != self_hash:
            raise ReportError(f"hardware record {path.name} has a stale canonical self-hash")
        measurement = _mapping(value.get("measurement_environment"), f"hardware record {path.name}")
        expected_measurement = {
            "environment_id": environment.get("environment_id"),
            "environment_bundle_sha256": environment.get("environment_bundle_sha256"),
            "release_manifest_sha256": release_sha,
            "freeze_check_sha256": freeze_sha,
        }
        if dict(measurement) != expected_measurement:
            raise ReportError(f"hardware record {path.name} has stale environment provenance")
        if value.get("host_class") != frozen_host:
            raise ReportError(f"hardware record {path.name} has the wrong frozen host class")
        job_id = value.get("job_id")
        hostname = value.get("hostname")
        if not isinstance(job_id, str) or not job_id or not isinstance(hostname, str) or not hostname:
            raise ReportError(f"hardware record {path.name} has no allocation identity")
        host = _mapping(value.get("host"), f"hardware host {path.name}")
        allocation = _mapping(value.get("allocation"), f"hardware allocation {path.name}")
        slurm = _mapping(value.get("slurm"), f"hardware Slurm allocation {path.name}")
        scheduler = _mapping(
            value.get("scheduler_sharing"), f"hardware scheduler sharing {path.name}"
        )
        expected_host = {
            "hostname": hostname,
            "kernel": frozen_host.get("kernel"),
            "virtualization": frozen_host.get("virtualization"),
            "cpu_vendor": frozen_host.get("cpu_vendor"),
            "processor": frozen_host.get("processor"),
            "cpu_family": frozen_host.get("cpu_family"),
            "cpu_model": frozen_host.get("cpu_model"),
            "cpu_stepping": frozen_host.get("cpu_stepping"),
            "benchmark_process_visible_memory_bytes": frozen_host.get("visible_memory_bytes"),
        }
        expected_allocation = {
            "cpu_affinity_logical_cpus": allocation.get("cpu_affinity_logical_cpus"),
            "online_logical_cpus": frozen_host.get("online_logical_cpus"),
            "allocated_physical_cores": frozen_host.get("allocated_physical_cores"),
            "allocated_sockets": frozen_host.get("allocated_sockets"),
            "allocated_threads_per_core": frozen_host.get("allocated_threads_per_core"),
            "cgroup_memory_limit_bytes": frozen_host.get("allocation_memory_limit_bytes"),
        }
        expected_slurm = {
            "job_id": job_id,
            "node_list": hostname,
            "num_nodes": frozen_host.get("slurm_num_nodes"),
            "num_cpus": frozen_host.get("slurm_num_cpus"),
            "num_tasks": frozen_host.get("slurm_num_tasks"),
            "cpus_per_task": frozen_host.get("slurm_cpus_per_task"),
            "allocated_memory_bytes": frozen_host.get("slurm_allocated_memory_bytes"),
            "alloc_tres": slurm.get("alloc_tres"),
            "allocated_gpu_count": slurm.get("allocated_gpu_count"),
            "gpu_environment": slurm.get("gpu_environment"),
        }
        alloc_tres = _validate_zero_gpu_alloc_tres(
            slurm.get("alloc_tres"), f"hardware record {path.name} AllocTRES"
        )
        allocated_gpu_count = slurm.get("allocated_gpu_count")
        if (
            not isinstance(allocated_gpu_count, int)
            or isinstance(allocated_gpu_count, bool)
            or allocated_gpu_count != 0
        ):
            raise ReportError(
                f"hardware record {path.name} does not have normalized allocated_gpu_count=0"
            )
        gpu_environment = _validate_zero_gpu_environment(
            slurm.get("gpu_environment"),
            f"hardware record {path.name} GPU environment",
        )
        affinity = allocation.get("cpu_affinity_logical_cpus")
        if (
            not isinstance(affinity, list)
            or any(not isinstance(cpu, int) or isinstance(cpu, bool) or cpu < 0 for cpu in affinity)
            or affinity != sorted(set(affinity))
            or len(affinity) != frozen_host.get("online_logical_cpus")
        ):
            raise ReportError(f"hardware record {path.name} has an invalid CPU-affinity set")
        if set(scheduler) != {
            "partition",
            "job_oversubscribe",
            "partition_oversubscribe",
            "node_list",
            "exclusive",
            "sharing_policy",
            "dynamic_co_tenant_count_recorded",
        } or (
            not isinstance(scheduler.get("partition"), str)
            or not scheduler.get("partition")
            or scheduler.get("job_oversubscribe") != "OK"
            or not isinstance(scheduler.get("partition_oversubscribe"), str)
            or not scheduler["partition_oversubscribe"].startswith("FORCE:")
            or scheduler.get("node_list") != hostname
            or scheduler.get("exclusive") is not False
            or scheduler.get("sharing_policy") != "partition_forced_oversubscription"
            or scheduler.get("dynamic_co_tenant_count_recorded") is not False
        ):
            raise ReportError(f"hardware record {path.name} lacks exact forced-sharing provenance")
        if (
            dict(host) != expected_host
            or dict(allocation) != expected_allocation
            or dict(slurm) != expected_slurm
        ):
            raise ReportError(f"hardware record {path.name} differs from the frozen allocation")
        relative = path.relative_to(results_root).as_posix()
        records[relative] = {
            "path": relative,
            "sha256": file_sha256(path),
            "record_sha256": self_hash,
            "job_id": job_id,
            "hostname": hostname,
            "cpu_affinity_logical_cpus": list(affinity),
            "partition": scheduler.get("partition"),
            "job_oversubscribe": scheduler.get("job_oversubscribe"),
            "partition_oversubscribe": scheduler.get("partition_oversubscribe"),
            "exclusive": False,
            "sharing_policy": "partition_forced_oversubscription",
            "alloc_tres": alloc_tres,
            "allocated_gpu_count": 0,
            "gpu_environment": gpu_environment,
        }
    if not records:
        raise ReportError("allocation_hardware contains no authenticated CPU/RAM/GPU record")
    return records


def _planned_incident_identity(
    planned: Mapping[str, Any], final: Mapping[str, Any]
) -> dict[str, Any]:
    return {
        "run_id": planned["run_id"],
        "pair_id": planned["pair_id"],
        "task_id": planned["task_id"],
        "paper_id": EXPECTED_PAPER,
        "paper_sha256": final.get("paper_sha256"),
        "tier": final.get("tier"),
        "condition": planned["condition"],
        "repetition_id": planned["repetition_id"],
        "backend_seed": planned["backend_seed"],
        "pair_order": planned["pair_order"],
        "order_index": planned["order_index"],
    }


def _authenticate_startup_incident(
    results_root: Path,
    path: Path,
    incident: Mapping[str, Any],
    source: Mapping[str, Any],
    planned: Mapping[str, Any],
    final: Mapping[str, Any],
    *,
    attempt: int,
) -> dict[str, Any]:
    run_id = str(planned["run_id"])
    recorded = _hex(
        incident.get("matrix_incident_sha256"),
        f"{run_id} matrix-incident self-hash",
    )
    unsigned = dict(incident)
    unsigned.pop("matrix_incident_sha256", None)
    if recorded != document_sha256(unsigned):
        raise ReportError(f"{run_id} matrix incident has a stale canonical self-hash")
    control = _mapping(incident.get("matrix_incident"), f"{run_id} incident control")
    expected_controls = {
        "retryable_pre_prompt_system_error": True,
        "terminal_pre_prompt_system_error": False,
        "aborted_after_unscorable_useful_work": False,
    }
    status = control.get("status")
    if (
        set(control)
        != {"status", "retry_allowed", "scored", "final_assignment_record_written"}
        or status not in expected_controls
        or control.get("retry_allowed") is not expected_controls[status]
        or control.get("scored") is not False
        or control.get("final_assignment_record_written") is not False
    ):
        raise ReportError(f"{run_id} matrix incident has an invalid retry/control policy")
    if attempt not in (1, 2) or incident.get("matrix_attempt") != attempt:
        raise ReportError(f"{run_id} matrix incident has the wrong attempt")
    if status == "retryable_pre_prompt_system_error" and attempt != 1:
        raise ReportError(f"{run_id} retryable incident is not attempt 1")
    if status == "terminal_pre_prompt_system_error" and attempt != 2:
        raise ReportError(f"{run_id} terminal startup incident is not attempt 2")
    suffix = "unscorable" if status == "aborted_after_unscorable_useful_work" else "system"
    incident_run_id = f"{run_id}-{suffix}-attempt-{attempt}"
    if (
        incident.get("planned_run_id") != run_id
        or incident.get("run_id") != incident_run_id
    ):
        raise ReportError(f"{run_id} matrix incident has a forged run identity")

    identity = _planned_incident_identity(planned, final)
    provenance = _mapping(
        incident.get("incident_provenance"), f"{run_id} incident provenance"
    )
    if (
        set(provenance)
        != {
            "schema_version",
            "planned_assignment",
            "matrix_attempt",
            "source_attempt",
            "transcript",
        }
        or provenance.get("schema_version") != 1
        or provenance.get("planned_assignment") != identity
        or provenance.get("matrix_attempt") != attempt
    ):
        raise ReportError(f"{run_id} matrix incident has stale assignment provenance")
    expected_source = f"attempts/{run_id}.attempt-{attempt}.json"
    expected_transcript = f"attempts/{run_id}.attempt-{attempt}.jsonl"
    source_descriptor = _mapping(
        provenance.get("source_attempt"), f"{run_id} incident source attempt"
    )
    transcript_descriptor = _mapping(
        provenance.get("transcript"), f"{run_id} incident transcript"
    )
    if set(source_descriptor) != {"path", "sha256"} or set(transcript_descriptor) != {
        "path",
        "sha256",
    }:
        raise ReportError(f"{run_id} incident source descriptors have unexpected fields")
    source_path = _resolve_result_path(
        results_root, source_descriptor.get("path"), f"{run_id} incident source attempt"
    )
    transcript_path = _resolve_result_path(
        results_root, transcript_descriptor.get("path"), f"{run_id} incident transcript"
    )
    if (
        source_descriptor.get("path") != expected_source
        or transcript_descriptor.get("path") != expected_transcript
        or source_path != (results_root / expected_source).resolve()
        or transcript_path != (results_root / expected_transcript).resolve()
        or source_descriptor.get("sha256") != file_sha256(source_path)
        or transcript_descriptor.get("sha256") != file_sha256(transcript_path)
        or transcript_path.stat().st_size <= 0
    ):
        raise ReportError(f"{run_id} incident source attempt/transcript is not authenticated")
    if read_json(source_path) != source:
        raise ReportError(f"{run_id} incident source attempt changed after loading")
    reserved = {
        "matrix_record_sha256",
        "matrix_incident_sha256",
        "planned_run_id",
        "matrix_incident",
        "incident_provenance",
    }
    if reserved.intersection(source):
        raise ReportError(f"{run_id} incident source attempt contains reserved matrix fields")
    if any(source.get(field) != value for field, value in identity.items()):
        raise ReportError(f"{run_id} incident source attempt has the wrong assignment")
    if (
        source.get("schema_version") != 1
        or source.get("kind") != "highambench-run"
        or source.get("matrix_attempt") != attempt
        or source.get("agent") != final.get("agent")
        or source.get("environment_id") != final.get("environment_id")
        or source.get("frozen_run_verification") != final.get("frozen_run_verification")
        or source.get("limits") != final.get("limits")
        or source.get("allocation_hardware") != final.get("allocation_hardware")
    ):
        raise ReportError(f"{run_id} incident source has stale agent/environment/hardware provenance")
    if status in {
        "retryable_pre_prompt_system_error",
        "terminal_pre_prompt_system_error",
    } and not (
        source.get("pass") is False
        and source.get("scored") is False
        and source.get("failure_code") == "SYSTEM_ERROR"
        and source.get("useful_work_started") is False
        and source.get("token_usage") is None
        and source.get("first_valid_seconds") is None
        and source.get("submission_sha256") is None
        and source.get("accepted_submission_log") is None
        and source.get("validation_log") is None
    ):
        raise ReportError(f"{run_id} incident is not a pre-prompt no-work SYSTEM_ERROR")

    expected_incident = json.loads(json.dumps(source))
    expected_incident.update(
        {
            "planned_run_id": run_id,
            "run_id": incident_run_id,
            "scored": False,
            "matrix_incident": dict(control),
            "incident_provenance": json.loads(json.dumps(provenance)),
        }
    )
    for field in ("agent_log", "validation_log"):
        raw = source.get(field)
        digest_field = f"{field}_sha256"
        if raw is None:
            if source.get(digest_field) is not None:
                raise ReportError(
                    f"{run_id} incident source has {digest_field} without {field}"
                )
            continue
        expected_frozen_log = f"attempts/{run_id}.attempt-{attempt}.{field}.artifact"
        if raw != expected_frozen_log:
            raise ReportError(f"{run_id} incident source {field} is not attempt-specific")
        source_log = _resolve_result_path(results_root, raw, f"{run_id} source {field}")
        if source_log != (results_root / expected_frozen_log).resolve():
            raise ReportError(f"{run_id} incident source {field} path is stale")
        source_log_digest = file_sha256(source_log)
        if _hex(
            source.get(digest_field), f"{run_id} incident source {digest_field}"
        ) != source_log_digest:
            raise ReportError(f"{run_id} incident source {field} digest is invalid")
        destination = path.parent / f"{incident_run_id}.attempt-{attempt}.{source_log.name}"
        copied = _resolve_result_path(results_root, str(destination), f"{run_id} copied {field}")
        if copied != destination.resolve() or file_sha256(copied) != source_log_digest:
            raise ReportError(f"{run_id} copied incident {field} is not byte-identical")
        expected_incident[field] = copied.relative_to(results_root).as_posix()
    expected_incident["matrix_incident_sha256"] = document_sha256(expected_incident)
    if dict(incident) != expected_incident:
        raise ReportError(f"{run_id} matrix incident is not exactly derived from its source")
    reason = incident.get("failure_note")
    if not isinstance(reason, str) or not reason.strip() or len(reason.encode("utf-8")) > MAX_FAILURE_NOTE_BYTES:
        raise ReportError(f"{run_id} matrix incident has no bounded recorded reason")
    return {
        "planned_run_id": run_id,
        "matrix_attempt": attempt,
        "status": status,
        "matrix_incident_sha256": recorded,
        "source_attempt_sha256": source_descriptor["sha256"],
        "transcript_sha256": transcript_descriptor["sha256"],
        "failure_code": incident.get("failure_code"),
        "reason": reason,
    }


def _load_records(
    results_root: Path, expected: Sequence[Mapping[str, Any]]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    active_marker = results_root / "active_run.json"
    if active_marker.exists() or active_marker.is_symlink():
        raise ReportError("results root retains an active-run marker; the checkpoint is incomplete")
    records_dir = results_root / "records"
    if not records_dir.is_dir() or records_dir.is_symlink():
        raise ReportError("results root has no records directory")
    json_paths = sorted(records_dir.glob("*.json"))
    expected_ids = {str(item["run_id"]) for item in expected}
    if {path.stem for path in json_paths} != expected_ids or len(json_paths) != EXPECTED_FINAL_RUNS:
        raise ReportError("records directory is not exactly the 18 expected P01 final records")
    if any(not path.is_file() or path.is_symlink() for path in json_paths):
        raise ReportError("final record ledger contains a non-regular or symlinked JSON file")
    by_id = {path.stem: read_json(path) for path in json_paths}
    ordered = [by_id[str(item["run_id"])] for item in expected]
    attempts_dir = results_root / "attempts"
    attempts_by_id: dict[str, dict[int, dict[str, Any]]] = {
        run_id: {} for run_id in expected_ids
    }
    attempt_pattern = re.compile(r"^(.+)\.attempt-([12])\.json$")
    if not attempts_dir.is_dir() or attempts_dir.is_symlink():
        raise ReportError("results root has no attempts directory")
    json_attempt_paths = sorted(attempts_dir.glob("*.json"))
    jsonl_attempt_paths = sorted(attempts_dir.glob("*.jsonl"))
    matched_transcripts: set[Path] = set()
    for path in json_attempt_paths:
        if not path.is_file() or path.is_symlink():
            raise ReportError(f"attempt record is non-regular or symlinked: {path.name}")
        match = attempt_pattern.fullmatch(path.name)
        if match is None or match.group(1) not in expected_ids:
            raise ReportError(f"unmatched or P02+ attempt record is included: {path.name}")
        planned_id, attempt_text = match.groups()
        attempt = int(attempt_text)
        if attempt in attempts_by_id[planned_id]:
            raise ReportError(f"attempt ledger repeats {planned_id} attempt {attempt}")
        record = read_json(path)
        if record.get("kind") != "highambench-run" or record.get("paper_id") != EXPECTED_PAPER:
            raise ReportError(f"unsupported or P02+ attempt record is included: {path.name}")
        transcript = path.with_suffix(".jsonl")
        if not transcript.is_file() or transcript.is_symlink() or transcript.stat().st_size == 0:
            raise ReportError(f"attempt {path.name} has no nonempty raw protocol transcript")
        matched_transcripts.add(transcript.resolve())
        attempts_by_id[planned_id][attempt] = record
    if {path.resolve() for path in jsonl_attempt_paths} != matched_transcripts:
        raise ReportError("attempts directory contains an unmatched raw protocol transcript")
    incidents_dir = results_root / "incidents"
    incident_pattern = re.compile(r"^(.+)\.attempt-([12])\.json$")
    incidents_by_id: dict[str, dict[int, dict[str, Any]]] = {
        run_id: {} for run_id in expected_ids
    }
    if incidents_dir.is_symlink():
        raise ReportError("incident ledger directory must not be a symlink")
    incident_paths = sorted(incidents_dir.glob("*.json")) if incidents_dir.is_dir() else []
    incident_path_by_id: dict[tuple[str, int], Path] = {}
    for path in incident_paths:
        if not path.is_file() or path.is_symlink():
            raise ReportError(f"incident record is non-regular or symlinked: {path.name}")
        match = incident_pattern.fullmatch(path.name)
        if match is None or match.group(1) not in expected_ids:
            raise ReportError(f"unmatched or P02+ incident is included: {path.name}")
        planned_id, attempt_text = match.groups()
        attempt = int(attempt_text)
        if attempt in incidents_by_id[planned_id]:
            raise ReportError(f"incident ledger repeats {planned_id} attempt {attempt}")
        incident = read_json(path)
        if incident.get("kind") != "highambench-run" or incident.get("paper_id") != EXPECTED_PAPER:
            raise ReportError(f"unsupported or P02+ benchmark incident is included: {path.name}")
        incidents_by_id[planned_id][attempt] = incident
        incident_path_by_id[(planned_id, attempt)] = path

    expected_stream: list[dict[str, Any]] = []
    authenticated_incidents: list[dict[str, Any]] = []
    planned_by_id = {str(item["run_id"]): item for item in expected}
    for record in ordered:
        run_id = str(record.get("run_id"))
        planned = planned_by_id[run_id]
        attempts = attempts_by_id[run_id]
        incidents = incidents_by_id[run_id]
        if set(attempts) not in ({1}, {1, 2}):
            raise ReportError(f"{run_id} does not follow the one-startup-retry attempt policy")
        final_attempt = attempts[max(attempts)]
        if final_attempt != record or final_attempt.get("run_id") != run_id:
            raise ReportError(f"{run_id} final record is not its last authenticated attempt")
        if final_attempt.get("matrix_attempt") != max(attempts):
            raise ReportError(f"{run_id} matrix attempt does not name its final ledger attempt")
        if set(attempts) == {1}:
            if incidents:
                raise ReportError(f"{run_id} has an incident without a permitted retry")
        else:
            startup = attempts[1]
            incident = incidents.get(1)
            if set(incidents) != {1} or incident is None:
                raise ReportError(f"{run_id} startup incident is not a qualifying no-work retry")
            incident_summary = _authenticate_startup_incident(
                results_root,
                incident_path_by_id[(run_id, 1)],
                incident,
                startup,
                planned,
                record,
                attempt=1,
            )
            if incident_summary["status"] != "retryable_pre_prompt_system_error":
                raise ReportError(
                    f"{run_id} terminal/unscorable incident cannot coexist with a final checkpoint"
                )
            if _iso(
                incident.get("finished_at_utc"), f"{run_id} startup incident finish"
            ) > _iso(record.get("started_at_utc"), f"{run_id} replacement start"):
                raise ReportError(f"{run_id} replacement started before its startup incident ended")
            authenticated_incidents.append(incident_summary)
            expected_stream.append(incident)
        expected_stream.append(record)
        agent_log = _resolve_result_path(
            results_root, record.get("agent_log"), f"{run_id} agent log"
        )
        if agent_log.stat().st_size == 0:
            raise ReportError(f"{run_id} agent log is empty")

    stream_path = results_root / "runs.jsonl"
    if not stream_path.is_file() or stream_path.is_symlink():
        raise ReportError("runs.jsonl must be a regular non-symlinked ledger")
    try:
        lines = [line for line in stream_path.read_text(encoding="utf-8").splitlines() if line.strip()]
        stream = [json.loads(line, object_pairs_hook=_reject_duplicate_keys) for line in lines]
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ReportError(f"cannot read runs.jsonl: {error}") from error
    if stream != expected_stream:
        raise ReportError("runs.jsonl is not the exact incident/final P01 checkpoint ledger")
    return ordered, authenticated_incidents


def _validate_boundary_status(
    results_root: Path,
    expected_all: Sequence[Mapping[str, Any]],
    expected_p01: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    status = read_json(results_root / "last_chunk_status.json")
    last = expected_p01[-1]
    next_items = [item for item in expected_all if item not in expected_p01]
    if not next_items:
        raise ReportError("P01 checkpoint metadata has no later paper boundary")
    following = next_items[0]
    wanted = {
        "schema_version": 1,
        "kind": "highambench-matrix-chunk-status",
        "status": "stopped_after_requested_paper",
        "requested_paper_id": EXPECTED_PAPER,
        "last_run_id": last["run_id"],
        "last_pair_id": last["pair_id"],
        "completed_runs_through_boundary": EXPECTED_FINAL_RUNS,
        "planned_runs_through_boundary": EXPECTED_FINAL_RUNS,
        "next_run_id": following["run_id"],
        "next_pair_id": following["pair_id"],
        "next_paper_id": "P02",
        "matrix_planned_runs": len(expected_all),
    }
    if status != wanted:
        raise ReportError("last_chunk_status.json is not the exact frozen P01 stop boundary")
    return status


def _summary(
    rows: Sequence[Mapping[str, Any]], pairs: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    def group(items: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
        times = [float(item["scored_elapsed_seconds"]) for item in items]
        tokens = [int(item["model_tokens"]) for item in items]
        passed = sum(item["pass"] is True for item in items)
        audited_l_passes = [
            item
            for item in items
            if item["condition"] == "L"
            and item["pass"] is True
            and isinstance(item["library_use"], bool)
        ]
        library_numerator = sum(item["library_use"] is True for item in audited_l_passes)
        failure_counts = {
            code: sum(item.get("failure_code") == code for item in items)
            for code in FAILURE_PRECEDENCE
        }
        return {
            "runs": len(items),
            "passes": passed,
            "failures": len(items) - passed,
            "pass_rate": passed / len(items) if items else None,
            "median_scored_seconds": statistics.median(times) if times else None,
            "mean_scored_seconds": statistics.mean(times) if times else None,
            "median_model_tokens": statistics.median(tokens) if tokens else None,
            "mean_model_tokens": statistics.mean(tokens) if tokens else None,
            "failure_code_counts": failure_counts,
            "library_use_numerator_among_passing_l": library_numerator,
            "library_use_denominator_passing_l": len(audited_l_passes),
            "library_use_rate_among_l_passes": (
                library_numerator / len(audited_l_passes)
                if audited_l_passes
                else None
            ),
        }

    def comparison(
        n: Mapping[str, Any], l: Mapping[str, Any], selected_pairs: Sequence[Mapping[str, Any]]
    ) -> dict[str, Any]:
        return {
            "pass_rate_l_minus_n": float(l["pass_rate"]) - float(n["pass_rate"]),
            "median_paired_l_minus_n_scored_seconds": statistics.median(
                float(pair["l_minus_n_scored_seconds"]) for pair in selected_pairs
            ),
            "median_paired_l_minus_n_model_tokens": statistics.median(
                int(pair["l_minus_n_model_tokens"]) for pair in selected_pairs
            ),
            "pair_count": len(selected_pairs),
        }

    by_condition = {
        condition: group([row for row in rows if row["condition"] == condition])
        for condition in EXPECTED_CONDITIONS
    }
    by_tier_condition = {
        tier: {
            condition: group(
                [row for row in rows if row["tier"] == tier and row["condition"] == condition]
            )
            for condition in EXPECTED_CONDITIONS
        }
        for tier in ("T1", "T2", "T3")
    }
    tier_comparisons = {
        tier: comparison(
            by_tier_condition[tier]["N"],
            by_tier_condition[tier]["L"],
            [pair for pair in pairs if pair["tier"] == tier],
        )
        for tier in ("T1", "T2", "T3")
    }
    return {
        "overall": group(list(rows)),
        "by_condition": by_condition,
        "comparison": comparison(by_condition["N"], by_condition["L"], pairs),
        "by_tier_condition": by_tier_condition,
        "by_tier_comparison": tier_comparisons,
        "failure_code_counts": {
            code: sum(row.get("failure_code") == code for row in rows)
            for code in FAILURE_PRECEDENCE
        },
    }


def _pairs(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    buckets: dict[str, dict[str, Mapping[str, Any]]] = {}
    for row in rows:
        buckets.setdefault(str(row["pair_id"]), {})[str(row["condition"])] = row
    result: list[dict[str, Any]] = []
    for pair_id, bucket in sorted(buckets.items()):
        if set(bucket) != set(EXPECTED_CONDITIONS):
            raise ReportError(f"paired analysis is incomplete for {pair_id}")
        n, l = bucket["N"], bucket["L"]
        result.append(
            {
                "pair_id": pair_id,
                "task_id": n["task_id"],
                "tier": n["tier"],
                "repetition_id": n["repetition_id"],
                "n_pass": n["pass"],
                "l_pass": l["pass"],
                "l_minus_n_pass": int(bool(l["pass"])) - int(bool(n["pass"])),
                "n_scored_seconds": n["scored_elapsed_seconds"],
                "l_scored_seconds": l["scored_elapsed_seconds"],
                "l_minus_n_scored_seconds": l["scored_elapsed_seconds"] - n["scored_elapsed_seconds"],
                "n_model_tokens": n["model_tokens"],
                "l_model_tokens": l["model_tokens"],
                "l_minus_n_model_tokens": l["model_tokens"] - n["model_tokens"],
            }
        )
    if len(result) != 9:
        raise ReportError("P01 paired analysis does not contain exactly nine N/L pairs")
    return result


def _percentile(values: Sequence[float], q: float) -> float:
    ordered = sorted(values)
    index = (len(ordered) - 1) * q
    low, high = math.floor(index), math.ceil(index)
    if low == high:
        return ordered[low]
    return ordered[low] * (high - index) + ordered[high] * (index - low)


def _bootstrap(pairs: Sequence[Mapping[str, Any]], seed_material: str) -> dict[str, Any]:
    seed = int(hashlib.sha256(seed_material.encode()).hexdigest()[:16], 16)
    rng = random.Random(seed)
    draws = 10_000
    metrics = {
        "pass_rate_difference": ("l_minus_n_pass", statistics.mean),
        "median_scored_seconds_difference": (
            "l_minus_n_scored_seconds",
            statistics.median,
        ),
        "median_model_tokens_difference": (
            "l_minus_n_model_tokens",
            statistics.median,
        ),
    }
    intervals: dict[str, Any] = {}
    for name, (field, estimator) in metrics.items():
        observed = estimator(float(pair[field]) for pair in pairs)
        samples = [
            estimator(float(rng.choice(pairs)[field]) for _ in pairs)
            for _ in range(draws)
        ]
        intervals[name] = {
            "estimate": observed,
            "exploratory_pair_bootstrap_95_percentile_interval": [
                _percentile(samples, 0.025),
                _percentile(samples, 0.975),
            ],
            "whole_paper_cluster_bootstrap_interval": [observed, observed],
        }
    return {
        "seed": seed,
        "resamples": draws,
        "unit_for_exploratory_interval": "nine frozen P01 paired assignments",
        "whole_paper_unit_count": 1,
        "whole_paper_resampling_degenerate": True,
        "note": (
            "HighamBench's whole-paper resampling has one available paper at this "
            "checkpoint, so every cluster bootstrap replicate is P01 and its interval "
            "is degenerate. Pair-level intervals are deterministic exploratory summaries, "
            "not substitutes for the planned whole-corpus uncertainty analysis."
        ),
        "metrics": intervals,
    }


def _tex(value: Any) -> str:
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(character, character) for character in text)


def _fmt_bool(value: bool) -> str:
    return "pass" if value else "fail"


def _fmt_rate(value: float | None) -> str:
    return "--" if value is None else f"{100 * value:.1f}\\%"


def _failure_tex(value: Any) -> str:
    if value is None:
        return "--"
    return _tex(value).replace(r"\_", r"\_\allowbreak{}")


def _path_tex(value: Any) -> str:
    return (
        _tex(value)
        .replace(r"\_", r"\_\allowbreak{}")
        .replace("/", r"/\allowbreak{}")
        .replace("-", r"-\allowbreak{}")
    )


def _render_latex(report: Mapping[str, Any]) -> str:
    rows = report["runs"]
    pairs = report["pairs"]
    summary = report["analysis"]
    provenance = report["provenance"]
    rendered_limits = _mapping(provenance.get("limits"), "report limits")
    rendered_token_limit = _integer(
        rendered_limits.get("total_model_tokens"),
        "report token limit",
        positive=True,
    )
    rendered_ultra_canary = _mapping(
        _mapping(provenance.get("canaries"), "report canaries").get(
            "ultra_orchestration"
        ),
        "report Ultra canary",
    )
    rendered_projection = _mapping(
        rendered_ultra_canary.get("accounting_projection"),
        "report Ultra canary projection",
    )
    rendered_policy = _mapping(
        rendered_projection.get("fork_policy"), "report Ultra fork policy"
    )
    hook_cli_present = _tex(
        str(rendered_policy.get("hook_trust_bypass_cli_flag_present")).lower()
    )
    hook_thread_config = _tex(
        json.dumps(
            rendered_policy.get("hook_trust_bypass_thread_config"),
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    hook_effective_source = _tex(
        str(rendered_policy.get("hook_trust_bypass_effective_source"))
    )
    by_condition = summary["by_condition"]
    condition_rows = "\n".join(
        f"{condition} & {value['passes']}/{value['runs']} & {100*value['pass_rate']:.1f} & "
        f"{value['median_scored_seconds']:.1f} & {value['median_model_tokens']:.0f} & "
        + (
            "--"
            if condition == "N"
            else (
                f"{value['library_use_numerator_among_passing_l']}/"
                f"{value['library_use_denominator_passing_l']} "
                f"({_fmt_rate(value['library_use_rate_among_l_passes'])})"
            )
        )
        + r" \\"
        for condition, value in by_condition.items()
    )
    comparison = summary["comparison"]
    tier_rows_list: list[str] = []
    for tier, conditions in summary["by_tier_condition"].items():
        n, l = conditions["N"], conditions["L"]
        delta = summary["by_tier_comparison"][tier]
        library = (
            f"{l['library_use_numerator_among_passing_l']}/"
            f"{l['library_use_denominator_passing_l']} "
            f"({_fmt_rate(l['library_use_rate_among_l_passes'])})"
        )
        tier_rows_list.append(
            f"{tier} & {n['passes']}/{n['runs']} & {l['passes']}/{l['runs']} & "
            f"{n['failures']}/{l['failures']} & {library} & "
            f"{100*delta['pass_rate_l_minus_n']:+.1f} & "
            f"{delta['median_paired_l_minus_n_scored_seconds']:+.1f} & "
            f"{delta['median_paired_l_minus_n_model_tokens']:+.0f} \\\\"
        )
    tier_rows = "\n".join(tier_rows_list)
    run_rows = "\n".join(
        f"{_tex(row['run_id'])} & {_fmt_bool(row['pass'])} & "
        f"{row['scored_elapsed_seconds']:.1f} & {row['model_tokens']} & "
        f"{('yes' if row['library_use'] is True else 'no' if row['library_use'] is False else 'n/a')} & "
        f"{_tex(', '.join(row['library_declarations']) or '--')} \\\\"
        for row in rows
    )
    pair_rows = "\n".join(
        f"{_tex(pair['pair_id'])} & {_fmt_bool(pair['n_pass'])}/{_fmt_bool(pair['l_pass'])} & "
        f"{pair['n_scored_seconds']:.1f} & {pair['l_scored_seconds']:.1f} & "
        f"{pair['l_minus_n_scored_seconds']:+.1f} & {pair['n_model_tokens']} & "
        f"{pair['l_model_tokens']} & {pair['l_minus_n_model_tokens']:+d} \\\\"
        for pair in pairs
    )
    failure_rows_list = [
        f"{_tex(row['run_id'])} & {_failure_tex(row['failure_code'])} & "
        f"{_tex(row['failure_note'] or '--')} \\\\"
        for row in rows
        if not row["pass"]
    ]
    failure_rows = "\n".join(failure_rows_list) or r"\multicolumn{3}{c}{No failed final runs} \\"
    pass_coordinates = " ".join(
        f"({condition},{100*by_condition[condition]['pass_rate']:.6f})"
        for condition in EXPECTED_CONDITIONS
    )
    n_coordinates = " ".join(
        f"({index},{pair['n_scored_seconds']:.6f})" for index, pair in enumerate(pairs, 1)
    )
    l_coordinates = " ".join(
        f"({index},{pair['l_scored_seconds']:.6f})" for index, pair in enumerate(pairs, 1)
    )
    host = provenance["host_class"]
    hardware_rows = "\n".join(
        f"{_tex(field)} & {_tex(value)} \\\\"
        for field, value in host.items()
    )
    hashes = provenance["metadata_document_sha256"]
    proof_count = sum(row["proof"] is not None for row in rows)
    library_names = sorted({name for row in rows for name in row["library_declarations"]})
    library_text = ", ".join(_tex(name) for name in library_names) or "none declared"
    bootstrap_note = _tex(report["uncertainty"]["note"])
    failure_count_rows = "\n".join(
        f"{_failure_tex(code)} & {count} \\\\"
        for code, count in summary["failure_code_counts"].items()
    )
    provider_endpoint_counts = Counter(
        str(row["provider_gate_endpoint"]) for row in rows
    )
    provider_endpoint_rows = "\n".join(
        f"{_tex(endpoint)} & {count} \\\\"
        for endpoint, count in sorted(provider_endpoint_counts.items())
    )
    uncertainty_labels = {
        "pass_rate_difference": r"Pass-rate difference $L-N$",
        "median_scored_seconds_difference": r"Median paired seconds $L-N$",
        "median_model_tokens_difference": r"Median paired tokens $L-N$",
    }
    uncertainty_rows = "\n".join(
        f"{uncertainty_labels[name]} & {entry['estimate']:.3f} & "
        f"[{entry['exploratory_pair_bootstrap_95_percentile_interval'][0]:.3f}, "
        f"{entry['exploratory_pair_bootstrap_95_percentile_interval'][1]:.3f}] & "
        f"[{entry['whole_paper_cluster_bootstrap_interval'][0]:.3f}, "
        f"{entry['whole_paper_cluster_bootstrap_interval'][1]:.3f}] \\\\"
        for name, entry in report["uncertainty"]["metrics"].items()
    )
    supplement = provenance["prompt_protocol"]["condition_l_supplement"]
    common_prompt = provenance["prompt_protocol"]["common_prompt"]
    hardware_record_rows = "\n".join(
        f"{_tex(item['job_id'])} & {_path_tex(item['path'])} & "
        f"{{\\ttfamily\\scriptsize\\seqsplit{{{item['sha256']}}}}} & "
        f"{{\\ttfamily\\scriptsize\\seqsplit{{{item['record_sha256']}}}}} \\\\"
        for item in provenance["hardware_records"]
    )
    hardware_sharing_text = "; ".join(
        _tex(
            f"job {item['job_id']}: partition {item['partition']}, "
            f"job={item['job_oversubscribe']}, partition={item['partition_oversubscribe']}, "
            f"exclusive={str(item['exclusive']).lower()}, affinity={item['cpu_affinity_logical_cpus']}, "
            f"GPU={item['allocated_gpu_count']} (raw AllocTRES and exact GPU environment "
            "snapshot authenticated in summary.json)"
        )
        for item in provenance["hardware_records"]
    )
    incident_evidence = provenance["matrix_incident_authentication"]
    incident_rows = "\n".join(
        f"{_tex(item['planned_run_id'])} & {item['matrix_attempt']} & "
        f"{{\\ttfamily\\scriptsize\\seqsplit{{{item['matrix_incident_sha256']}}}}} & "
        f"{_tex(item['reason'])} \\\\"
        for item in incident_evidence["incidents"]
    ) or "-- & 0 & -- & No resolved pre-prompt startup retries \\\\"
    return rf"""\documentclass[11pt]{{article}}
\usepackage[margin=0.72in]{{geometry}}
\usepackage{{booktabs,longtable,array,ragged2e,xcolor,hyperref,seqsplit,tikz,pgfplots}}
\pgfplotsset{{compat=1.18}}
\usetikzlibrary{{arrows.meta,positioning,shapes.geometric}}
\hypersetup{{colorlinks=true,linkcolor=blue,urlcolor=blue}}
\definecolor{{privateRed}}{{HTML}}{{8B1E1E}}
\setlength{{\LTpre}}{{4pt}}
\setlength{{\LTpost}}{{4pt}}
\title{{HighamBench P01: Frozen Measurement Checkpoint}}
\author{{Authenticated automated report}}
\date{{}}
\begin{{document}}
\raggedbottom
\maketitle
\begin{{center}}
\fcolorbox{{privateRed}}{{red!5}}{{\parbox{{0.91\linewidth}}{{\centering\bfseries\color{{privateRed}}
PRIVATE / NOT FOR PUBLIC RELEASE. This document reports actual measured records;
it is neither a placeholder nor a smoke test.}}}}
\end{{center}}

\section{{Scope and acceptance}}
The checkpoint contains exactly 18 final, scored P01 records: three fixed tasks,
three frozen repetitions, and conditions N and L. No P02 or later benchmark
record is included. All records cite one current freeze, the current release and
environment identities, a 120/120 construction certificate, and two passed live
canaries. The token-control probe is the unscored synthetic Token V8 provider-gate
compaction crossing with exactly {len(token_canary.ARTIFACT_LABELS)} authenticated artifacts; the Ultra V12 orchestration probe
has exactly {len(ultra_canary.ARTIFACT_LABELS)} authenticated artifacts, including the production dependency-audit
helper and a complete no-library dependency audit. {proof_count} accepted proofs were byte-authenticated against hidden
validation logs and protected snapshots where the Ultra submission barrier was used.
Two independent fresh-context Codex-agent reviews certify 60/60 source-faithful
tasks. They retain 13 exact-target collisions (47 novel targets); the configured
private override applies only to those novelty rejections and does not authorize
public release.

The separate complete-corpus construction check passed all 120/120 task-condition
proofs. In particular, P02 T1, T2, and T3 construction proofs passed in both N and
L (six checks). There are no P02 benchmark measurements in this checkpoint; those
construction checks are validator/isolation readiness evidence, not measured runs.

\begin{{center}}
\begin{{tikzpicture}}[node distance=7mm and 8mm, every node/.style={{font=\small}},
 box/.style={{draw,rounded corners,align=center,minimum height=8mm}},
 arr/.style={{-{{Latex[length=2mm]}},thick}}]
\node[box] (release) {{current release\\and task hashes}};
\node[box,right=of release] (freeze) {{frozen environment\\hardware + canaries}};
\node[box,right=of freeze] (ledger) {{sealed provider gate\\+ reconciled delivery}};
\node[box,below=of ledger] (barrier) {{outer exec + blocked inner submit\\immutable snapshot}};
\node[box,left=of barrier] (lean) {{hidden Lean validation\\dependency audit}};
\node[box,left=of lean,fill=green!8] (report) {{18 scored records\\this report}};
\draw[arr] (release)--(freeze); \draw[arr] (freeze)--(ledger);
\draw[arr] (ledger)--(barrier); \draw[arr] (barrier)--(lean); \draw[arr] (lean)--(report);
\end{{tikzpicture}}
\end{{center}}

\begin{{center}}
\begin{{tabular}}{{lr}}
\toprule Authenticated provider-gate endpoint & Final records \\
\midrule
{provider_endpoint_rows}
\bottomrule
\end{{tabular}}
\end{{center}}

\section{{Outcomes and resource use}}
\begin{{table}}[ht]
\centering
\caption{{Condition-level outcomes. Tokens include cached input exactly once.}}
\begin{{tabular}}{{lrrrrr}}
\toprule Condition & Pass & Rate (\%) & Median seconds & Median tokens & L-use/pass L \\
\midrule
{condition_rows}
\bottomrule
\end{{tabular}}
\end{{table}}

Across all nine pairs, the measured L-minus-N pass-rate change is
{100*comparison['pass_rate_l_minus_n']:+.1f} percentage points; the median paired
changes are {comparison['median_paired_l_minus_n_scored_seconds']:+.1f} seconds and
{comparison['median_paired_l_minus_n_model_tokens']:+.0f} model tokens.

\begin{{table}}[ht]
\centering
\small
\caption{{Tier-level outcomes and paired L-minus-N changes. Library uptake is the
numerator/denominator among passing L runs only.}}
\begin{{tabular}}{{lrrrrrrr}}
\toprule Tier & N pass & L pass & N/L fail & L use/pass & $\Delta$ pass pp &
$\widetilde{{\Delta t}}$ & $\widetilde{{\Delta tok}}$ \\
\midrule
{tier_rows}
\bottomrule
\end{{tabular}}
\normalsize
\end{{table}}

\begin{{figure}}[ht]
\centering
\begin{{tikzpicture}}
\begin{{axis}}[ybar,bar width=18pt,width=.43\linewidth,height=5cm,
 symbolic x coords={{N,L}},xtick=data,ymin=0,ymax=100,ylabel={{pass rate (\%)}}]
\addplot[fill=blue!55] coordinates {{{pass_coordinates}}};
\end{{axis}}
\end{{tikzpicture}}\hfill
\begin{{tikzpicture}}
\begin{{axis}}[width=.52\linewidth,height=5cm,xlabel={{frozen N/L pair}},ylabel={{scored seconds}},
 legend style={{font=\small,at={{(0.5,1.02)}},anchor=south,legend columns=2}}]
\addplot+[mark=*,blue] coordinates {{{n_coordinates}}};
\addplot+[mark=square*,orange] coordinates {{{l_coordinates}}};
\legend{{N,L}}
\end{{axis}}
\end{{tikzpicture}}
\caption{{Measured success rates and paired first-valid-proof/failure-charged times.}}
\end{{figure}}

\section{{Run-level measurements}}
\small
\begin{{longtable}}{{p{{3.7cm}}lrrlp{{4.3cm}}}}
\caption{{All final scored records and audited library declarations.}}\\
\toprule Run & Outcome & Seconds & Tokens & Lib. used & Declarations \\
\midrule\endfirsthead
\toprule Run & Outcome & Seconds & Tokens & Lib. used & Declarations \\
\midrule\endhead
{run_rows}
\bottomrule
\end{{longtable}}
\normalsize

\section{{Paired changes}}
\small
\begin{{longtable}}{{p{{3.0cm}}lrrrrrr}}
\caption{{Paired L minus N changes.}}\\
\toprule Pair & N/L outcome & N sec. & L sec. & $\Delta$ sec. & N tok. & L tok. & $\Delta$ tok. \\
\midrule\endfirsthead
\toprule Pair & N/L outcome & N sec. & L sec. & $\Delta$ sec. & N tok. & L tok. & $\Delta$ tok. \\
\midrule\endhead
{pair_rows}
\bottomrule
\end{{longtable}}
\normalsize

\section{{Failures and library-use audit}}
\begin{{longtable}}{{>{{\RaggedRight\arraybackslash}}p{{4cm}}>{{\RaggedRight\arraybackslash}}p{{2.7cm}}>{{\RaggedRight\arraybackslash}}p{{7.5cm}}}}
\toprule Run & Failure code & Recorded reason \\
\midrule\endfirsthead
\toprule Run & Failure code & Recorded reason \\
\midrule\endhead
{failure_rows}
\bottomrule
\end{{longtable}}
\begin{{center}}
\begin{{tabular}}{{lr}}
\toprule Failure code & Final-run count \\
\midrule
{failure_count_rows}
\bottomrule
\end{{tabular}}
\end{{center}}
Across accepted proofs, the transitive dependency audit declared: {library_text}.
Condition N is required to declare none and to carry a successful import-absence preflight.
Library uptake elsewhere in this report always means the numerator, denominator,
and rate among passing L runs; failed L runs without a completed validation audit
are excluded from that denominator.

\section{{Uncertainty at the P01 checkpoint}}
{bootstrap_note}
The deterministic exploratory bootstrap uses seed
\texttt{{{report['uncertainty']['seed']}}} and 10,000 resamples of the nine frozen
paired assignments. Time and token estimands are medians of the nine paired
L-minus-N changes; the pass-rate estimand is the mean paired pass indicator change.
\begin{{center}}
\small
\begin{{tabular}}{{lrrr}}
\toprule Estimand & Estimate & Pair-bootstrap 95\% interval & Whole-paper interval \\
\midrule
{uncertainty_rows}
\bottomrule
\end{{tabular}}
\normalsize
\end{{center}}
With only one paper, whole-paper resampling is necessarily degenerate; the numeric
pair intervals are explicitly exploratory checkpoint summaries.

\section{{Prompt treatment and repetition control}}
The frozen common prompt is \texttt{{{_tex(common_prompt['path'])}}}
(SHA-256 {{\ttfamily\footnotesize\seqsplit{{{common_prompt['sha256']}}}}}). Condition L alone receives
\texttt{{{_tex(supplement['path'])}}} (SHA-256
{{\ttfamily\footnotesize\seqsplit{{{supplement['sha256']}}}}}). That supplement explicitly permits
searching and using the mounted NumStability snapshot at
\texttt{{/library/NumStability}}, \texttt{{/library/NumStability.lean}}, and
\texttt{{/library-olean}}, and encourages \texttt{{rg}}/\texttt{{find}} search.
No theorem/module hint list is supplied. This signposted-library-v1 L-only treatment
is a user-directed departure from the reference PDF section 3 identical-prompt rule;
the departure is authenticated in the environment metadata and kept separate from
earlier raw-access measurements.

The scored model limit in this checkpoint is {rendered_token_limit:,} tokens per
attempt. This user-directed 5-million-token setting replaces the earlier
2-million-token plan and is applied identically to N and L; it is therefore reported
as another protocol departure rather than as a strict reference-PDF result.

All rep-01/02/03 records authenticate \texttt{{backend\_seed=null}} and
\texttt{{seed\_enforced\_by\_agent=false}}. They are private unseeded repetitions;
the repetition names are not represented as backend seeds.

\section{{Hardware and protocol provenance}}
\footnotesize
\begin{{longtable}}{{p{{5.3cm}}p{{9.7cm}}}}
\toprule Frozen field & Value \\
\midrule\endfirsthead
\toprule Frozen field & Value \\
\midrule\endhead
{hardware_rows}
\bottomrule
\end{{longtable}}

\begin{{longtable}}{{p{{1.2cm}}p{{3.5cm}}p{{5.0cm}}p{{5.0cm}}}}
\toprule Job & Results-relative record & File SHA-256 & Canonical self-hash \\
\midrule\endfirsthead
\toprule Job & Results-relative record & File SHA-256 & Canonical self-hash \\
\midrule\endhead
{hardware_record_rows}
\bottomrule
\end{{longtable}}

\begin{{longtable}}{{p{{3.7cm}}p{{1.4cm}}p{{4.8cm}}p{{4.8cm}}}}
\caption{{Authenticated resolved startup incidents (count:
{incident_evidence['resolved_pre_prompt_retry_count']}).}}\\
\toprule Planned run & Attempt & Incident self-hash & Recorded reason \\
\midrule\endfirsthead
\toprule Planned run & Attempt & Incident self-hash & Recorded reason \\
\midrule\endhead
{incident_rows}
\bottomrule
\end{{longtable}}

\begin{{tabular}}{{p{{4cm}}p{{11cm}}}}
Benchmark ID & \ttfamily\footnotesize\seqsplit{{{_tex(provenance['benchmark_id'])}}} \\
Environment ID & \ttfamily\footnotesize\seqsplit{{{_tex(provenance['environment_id'])}}} \\
Environment bundle & \ttfamily\footnotesize\seqsplit{{{provenance['environment_bundle_sha256']}}} \\
Release manifest & \ttfamily\footnotesize\seqsplit{{{provenance['release']['sha256']}}} \\
Construction certificate & \ttfamily\footnotesize\seqsplit{{{provenance['construction']['sha256']}}} \\
Specification PDF & \ttfamily\footnotesize\seqsplit{{{provenance['specification']['sha256']}}} \\
Fresh-context review A & \ttfamily\footnotesize\seqsplit{{{provenance['reviews']['reviews'][0]['sha256']}}} \\
Fresh-context review B & \ttfamily\footnotesize\seqsplit{{{provenance['reviews']['reviews'][1]['sha256']}}} \\
Config document & \ttfamily\footnotesize\seqsplit{{{hashes['config']}}} \\
Environment document & \ttfamily\footnotesize\seqsplit{{{hashes['environment']}}} \\
Manifest document & \ttfamily\footnotesize\seqsplit{{{hashes['manifest']}}} \\
Run-order document & \ttfamily\footnotesize\seqsplit{{{hashes['run_order']}}} \\
Token canary & \ttfamily\footnotesize\seqsplit{{{provenance['canaries']['token_control']['sha256']}}} \\
Ultra canary & \ttfamily\footnotesize\seqsplit{{{provenance['canaries']['ultra_orchestration']['sha256']}}} \\
\end{{tabular}}
\enlargethispage{{2\baselineskip}}

The construction certificate binds the complete 20-paper/60-task manifest, all 120
N/L results, private proof sources, controlled manifests, fresh per-result workspaces,
condition-N absence probes, hidden Lean rebuilds, semantic statement equality, and
transitive dependency audits. Allocation records are canonical-self-hashed, sealed to
the freeze/release/environment identities, and linked from every final run; they also
record CPU affinity, authenticated zero-GPU scheduler/environment evidence, and the
factual non-exclusive forced-sharing scheduler policy.
Authenticated allocation facts: {hardware_sharing_text}.
The accounting records use projection schema v6. Provider totals determine the
scored token count; app-server delivery rows are retained as structural evidence,
including narrowly proved collaboration-wait suppressions. The records also use an authenticated
PreToolUse decision for every spawn, complete allowed-child linkage, descendant
accounting, cumulative projection evidence, and a sealed provider-gate binding. The frozen policy permits omitted,
\texttt{{all}}, and \texttt{{none}} fork histories and blocks positive-integer
suffixes without creating children. Hook trust is reported in three distinct
authenticated fields: CLI flag present=\texttt{{{hook_cli_present}}}, thread/start
config=\texttt{{{hook_thread_config}}}, and effective source=
\texttt{{{hook_effective_source}}}. Thus CLI presence is not mistaken for the
pinned app-server's effective thread-start configuration. Passing runs use
the schema-v5 boundary in which the sole final outer custom-exec raw item has the
frozen 98-byte source (SHA-256
\texttt{{\seqsplit{{{codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256}}}}}),
including an exact 2,400,000-ms code-mode yield pragma, and both its authenticated
inner submit-proof dynamic call and the same completed raw response are observed
before boundary publication. Schema v5 admits either
timestamp-authenticated observation order, records it with an exact enum and XOR
Boolean flags, and rejects ambiguous or mismatched order evidence. The inner call
remains blocked and emits no result or outer progress output. The yield timer begins
no earlier than authenticated prompt release and strictly exceeds the 1,800-second
measured limit plus the 369-second validation/teardown reserve by 231 seconds;
naturally failed runs require a fully drained exact tree. Each accepted run closes
the provider gate after request publication, with all upstream provider calls already
committed, while the blocked inner call still makes app-server tree terminality false.
The adapter then performs immediate clean child teardown. A token-limit run instead
closes at one sole-inflight sanitized crossing: an ordinary turn releases a minimal
empty-output completion, while a compaction request releases exactly one opaque
compaction item and then the completion. Neither crossing releases messages, tool
frames, or an interrupt; provider-token closure remains exact even if tree drain and
cumulative accounting are intentionally incomplete. The 272,000-token catalog bound
drives conservative reservation, then drain, then exclusive admission. Production
transport provenance authenticates explicit TLS; DNS address variability is an
availability-only fact and never a scoring input. This trusted adapter/gate endpoint
is a disclosed execution-protocol amendment applied identically to N and L, so this
checkpoint does not claim the strict unmodified reference-PDF protocol. The frozen
Codex binary and model configuration are unchanged; the trusted adapter and gate
enforce the amended endpoint. Every scored record independently reauthenticates sealed
READY, GO, and RELEASED files. Measured time begins at RELEASED's
\texttt{{CLOCK\_MONOTONIC}} timestamp captured immediately before the exact
\texttt{{turn/start}} request is written; for a passing Ultra run it ends at the
authenticated nested-boundary publication timestamp after the outer exec raw
response completes with the inner \texttt{{submit\_proof}} call blocked. Adapter
startup is governed by a separate frozen 120-second timeout and is excluded from
the 1,800-second scored wall limit. The frozen post-submission validation reserve
is 369 seconds. The incident ledger contains
{incident_evidence['resolved_pre_prompt_retry_count']} authenticated, resolved
attempt-1 pre-prompt retry record(s), and no terminal/unscorable incident or active
run marker.

\paragraph{{Interpretation boundary.}}
This is a private one-paper checkpoint. It reports the authenticated measurements
as recorded and does not release the benchmark, proofs, or results publicly.
\normalsize
\end{{document}}
"""


def _write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def _write_csv(path: Path, rows: Sequence[Mapping[str, Any]], fields: Sequence[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(fields), extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def _compile_pdf(output_dir: Path, tex_path: Path) -> Path:
    command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name]
    logs: list[str] = []
    for _ in range(2):
        try:
            completed = subprocess.run(
                command,
                cwd=output_dir,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
        except FileNotFoundError as error:
            raise ReportError("--compile-pdf requested but pdflatex is unavailable") from error
        logs.append(completed.stdout)
        if completed.returncode != 0:
            (output_dir / "pdflatex.log.txt").write_text("\n".join(logs), encoding="utf-8")
            raise ReportError("pdflatex failed; see pdflatex.log.txt")
    (output_dir / "pdflatex.log.txt").write_text("\n".join(logs), encoding="utf-8")
    pdf = tex_path.with_suffix(".pdf")
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise ReportError("pdflatex reported success but produced no PDF")
    return pdf


def build_report(
    benchmark_root: Path,
    results_root: Path,
    output_dir: Path,
    *,
    compile_pdf: bool = False,
) -> dict[str, Any]:
    benchmark_root = benchmark_root.resolve()
    results_root = results_root.resolve()
    output_dir = output_dir.resolve()
    if not benchmark_root.is_dir() or not results_root.is_dir():
        raise ReportError("benchmark root and results root must be existing directories")
    metadata = benchmark_root / "metadata"
    config = read_json(metadata / "config.json")
    environment = read_json(metadata / "environment.json")
    manifest = read_json(metadata / "manifest.json")
    run_order = read_json(metadata / "run_order.json")
    release = read_json(metadata / "release_files.json")
    benchmark_id = config.get("benchmark_id")
    if not isinstance(benchmark_id, str) or any(
        value.get("benchmark_id") != benchmark_id for value in (environment, manifest, run_order)
    ):
        raise ReportError("benchmark identity disagrees across current metadata")
    frozen = _mapping(config.get("frozen_environment"), "frozen environment")
    bundle = environment_bundle_sha256(config, environment)
    if (
        bundle != frozen.get("environment_bundle_sha256")
        or bundle != environment.get("environment_bundle_sha256")
        or frozen.get("environment_id") != environment.get("environment_id")
    ):
        raise ReportError("config/environment canonical bundle identity is stale")
    release_summary = _authenticate_release(
        benchmark_root, release, frozen.get("release_manifest_sha256")
    )
    if environment.get("release_manifest_sha256") != release_summary["sha256"]:
        raise ReportError("environment.json has a stale release manifest digest")
    specification = _specification_check(benchmark_root, manifest)
    prompt_protocol = _signposted_protocol_check(benchmark_root, config, environment)
    tasks = _manifest_tasks(benchmark_root, manifest)
    construction = _construction_check(benchmark_root, manifest)
    reviews = _review_check(benchmark_root, config, manifest)
    limits = _mapping(config.get("limits"), "config limits")
    token_limit = _integer(limits.get("total_model_tokens"), "token limit", positive=True)
    wall_limit = _number(limits.get("wall_clock_seconds"), "wall-clock limit")
    runtime = _mapping(environment.get("runtime"), "environment runtime")
    if (
        _number(
            limits.get("prompt_startup_timeout_seconds"),
            "config prompt startup timeout",
        )
        != 120.0
        or _number(
            runtime.get("prompt_startup_timeout_seconds"),
            "environment prompt startup timeout",
        )
        != 120.0
    ):
        raise ReportError(
            "config/environment must freeze the separate 120-second prompt startup timeout"
        )
    config_validation_reserve = _number(
        limits.get("post_submission_validation_reserve_seconds"),
        "config post-submission validation reserve",
    )
    environment_validation_reserve = _number(
        runtime.get("post_submission_validation_reserve_seconds"),
        "environment post-submission validation reserve",
    )
    if (
        config_validation_reserve != POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
        or environment_validation_reserve != config_validation_reserve
    ):
        raise ReportError(
            "config/environment must freeze the exact 369-second post-submission validation reserve"
        )
    if _number(
        limits.get("failure_scored_time_seconds"), "fixed failure scored time"
    ) != wall_limit:
        raise ReportError("the frozen failure charge must equal the wall-clock limit")
    try:
        production_prompt_protocol, execution_components = (
            run_matrix.production_freeze_bindings(config, environment)
        )
    except BenchmarkToolError as error:
        raise ReportError(
            f"production prompt/execution freeze bindings are invalid: {error}"
        ) from error
    agent = _expected_canary_agent(config)
    canaries = {
        "token_control": _authenticate_canary(
            benchmark_root,
            frozen.get("token_control_canary"),
            name="token-control canary",
            benchmark_id=benchmark_id,
            agent=agent,
            token_limit=token_limit,
            prompt_protocol=production_prompt_protocol,
            execution_components=execution_components,
        ),
        "ultra_orchestration": _authenticate_canary(
            benchmark_root,
            frozen.get("ultra_orchestration_canary"),
            name="Ultra orchestration canary",
            benchmark_id=benchmark_id,
            agent=agent,
            token_limit=token_limit,
            prompt_protocol=production_prompt_protocol,
            execution_components=execution_components,
        ),
    }
    if environment.get("token_control_canary") != frozen.get("token_control_canary") or environment.get(
        "ultra_orchestration_canary"
    ) != frozen.get("ultra_orchestration_canary"):
        raise ReportError("canary descriptors disagree between config and environment")
    expected_all, expected_p01 = _expected_assignments(config, run_order, tasks)
    boundary_status = _validate_boundary_status(results_root, expected_all, expected_p01)
    freeze, metadata_hashes = _freeze_check(
        benchmark_root,
        results_root,
        config,
        environment,
        manifest,
        run_order,
        release_summary,
        canaries,
    )
    freeze_sha = document_sha256(freeze)
    hardware_records = _validate_hardware_records(
        results_root,
        environment,
        release_summary["sha256"],
        freeze_sha,
    )
    raw_records, startup_incidents = _load_records(results_root, expected_p01)
    runtime_binding_cache: dict[tuple[str, str], bool] = {}
    rows = [
        _validate_record(
            benchmark_root,
            results_root,
            config,
            environment,
            freeze,
            tasks[str(planned["task_id"])],
            planned,
            record,
            hardware_records,
            runtime_binding_cache,
        )
        for planned, record in zip(expected_p01, raw_records)
    ]
    prompt_artifacts = [
        path
        for row in rows
        for path in row["prompt_release_authentication"]["artifacts"].values()
    ]
    if len(prompt_artifacts) != 3 * EXPECTED_FINAL_RUNS or len(
        set(prompt_artifacts)
    ) != len(prompt_artifacts):
        raise ReportError("P01 final records reuse or omit prompt-release artifacts")
    prompt_release_authentication = {
        "schema_version": 1,
        "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "timing_origin": "authenticated_turn_start_write",
        "ultra_success_endpoint": (
            "authenticated_nested_submission_boundary_publication_after_"
            "outer_exec_raw_response_completion"
        ),
        "startup_timeout_seconds": 120.0,
        "startup_timeout_separate_from_scored_wall_limit": True,
        "selected_final_run_count": EXPECTED_FINAL_RUNS,
        "authenticated_release_count": EXPECTED_FINAL_RUNS,
        "retained_artifact_set_count": EXPECTED_FINAL_RUNS,
        "retained_artifact_file_count": 3 * EXPECTED_FINAL_RUNS,
        "retained_artifacts_reauthenticated": True,
        "all_selected_final_releases_authenticated": True,
        "run_evidence": [
            {"run_id": row["run_id"], **row["prompt_release_authentication"]}
            for row in rows
        ],
    }
    matrix_record_authentication = {
        "schema_version": 1,
        "hash_field": "matrix_record_sha256",
        "canonicalization": (
            "compact_sorted_key_utf8_json_remove_only_hash_field"
        ),
        "selected_final_record_count": EXPECTED_FINAL_RUNS,
        "authenticated_final_record_count": EXPECTED_FINAL_RUNS,
        "all_selected_final_records_authenticated": True,
        "run_evidence": [
            {
                "run_id": row["run_id"],
                "matrix_attempt": row["matrix_attempt"],
                "matrix_record_sha256": row["matrix_record_sha256"],
                "recomputed_matrix_record_sha256": row[
                    "matrix_record_sha256"
                ],
                "valid": True,
            }
            for row in rows
        ],
    }
    incident_authentication = {
        "schema_version": 1,
        "policy": "only_resolved_attempt_1_pre_prompt_system_error_retry_may_coexist",
        "resolved_pre_prompt_retry_count": len(startup_incidents),
        "terminal_or_unscorable_incident_count": 0,
        "active_run_marker_present": False,
        "incidents": startup_incidents,
    }
    # Enforce the frozen pair execution order using actual timestamps.
    raw_by_id = {str(record["run_id"]): record for record in raw_records}
    for planned in expected_p01:
        if planned["order_index"] != 1:
            continue
        pair = [item for item in expected_p01 if item["pair_id"] == planned["pair_id"]]
        first, second = sorted(pair, key=lambda item: int(item["order_index"]))
        if _iso(raw_by_id[str(first["run_id"])]["finished_at_utc"], "pair finish") > _iso(
            raw_by_id[str(second["run_id"])]["started_at_utc"], "pair start"
        ):
            raise ReportError(f"pair {planned['pair_id']} ran out of frozen N/L order")
    pairs = _pairs(rows)
    analysis = _summary(rows, pairs)
    bootstrap_seed_material = document_sha256(
        {
            "paper_id": EXPECTED_PAPER,
            "manifest_sha256": metadata_hashes["manifest"],
            "run_order_sha256": metadata_hashes["run_order"],
            "final_record_sha256": [document_sha256(record) for record in raw_records],
        }
    )
    uncertainty = _bootstrap(pairs, bootstrap_seed_material)
    uncertainty["seed_material_sha256"] = bootstrap_seed_material
    provenance = {
        "benchmark_id": benchmark_id,
        "environment_id": environment.get("environment_id"),
        "environment_bundle_sha256": bundle,
        "metadata_document_sha256": metadata_hashes,
        "freeze_check_sha256": freeze_sha,
        "release": release_summary,
        "specification": specification,
        "prompt_protocol": prompt_protocol,
        "limits": {
            "wall_clock_seconds": wall_limit,
            "total_model_tokens": token_limit,
        },
        "construction": construction,
        "reviews": reviews,
        "canaries": canaries,
        "host_class": environment.get("host_class"),
        "hardware_records": list(hardware_records.values()),
        "backend_seed": None,
        "seed_enforced_by_agent": False,
        "p01_target_sha256": {task: tasks[task]["target_sha256"] for task in EXPECTED_TASKS},
        "boundary_status": boundary_status,
        "matrix_record_authentication": matrix_record_authentication,
        "matrix_incident_authentication": incident_authentication,
        "prompt_release_authentication": prompt_release_authentication,
    }
    report = {
        "schema_version": REPORT_SCHEMA_VERSION,
        "kind": "highambench-private-p01-checkpoint-report-data",
        "status": "authenticated",
        "public_release": False,
        "actual_measurements": True,
        "paper_id": EXPECTED_PAPER,
        "final_scored_record_count": len(rows),
        "later_paper_record_count": 0,
        "analysis": analysis,
        "pairs": pairs,
        "uncertainty": uncertainty,
        "runs": rows,
        "provenance": provenance,
    }
    # Nothing is written before every authentication and consistency check passes.
    output_dir.mkdir(parents=True, exist_ok=True)
    validation = {
        "schema_version": REPORT_SCHEMA_VERSION,
        "kind": "highambench-p01-report-validation",
        "ok": True,
        "selected_final_scored_records": EXPECTED_FINAL_RUNS,
        "p02_or_later_records": 0,
        "freeze_check_sha256": provenance["freeze_check_sha256"],
        "accepted_proof_count": sum(row["proof"] is not None for row in rows),
        "submission_boundary_count": sum(
            bool(row["proof"] and row["proof"]["submission_boundary"]) for row in rows
        ),
        "matrix_record_authentication_count": EXPECTED_FINAL_RUNS,
        "authenticated_prompt_release_count": EXPECTED_FINAL_RUNS,
        "authenticated_prompt_release_artifact_count": 3 * EXPECTED_FINAL_RUNS,
        "authenticated_resolved_startup_incident_count": len(startup_incidents),
        "terminal_or_unscorable_incident_count": 0,
    }
    _write_json(output_dir / "validation.json", validation)
    _write_json(output_dir / "summary.json", report)
    _write_csv(
        output_dir / "runs.csv",
        rows,
        (
            "run_id",
            "pair_id",
            "task_id",
            "tier",
            "condition",
            "repetition_id",
            "pass",
            "failure_code",
            "actual_stop_seconds",
            "scored_elapsed_seconds",
            "model_tokens",
            "input_tokens",
            "cached_input_tokens",
            "output_tokens",
            "thread_count",
            "response_count",
            "library_use",
        ),
    )
    _write_csv(
        output_dir / "pairs.csv",
        pairs,
        (
            "pair_id",
            "task_id",
            "tier",
            "repetition_id",
            "n_pass",
            "l_pass",
            "l_minus_n_pass",
            "n_scored_seconds",
            "l_scored_seconds",
            "l_minus_n_scored_seconds",
            "n_model_tokens",
            "l_model_tokens",
            "l_minus_n_model_tokens",
        ),
    )
    tex_path = output_dir / "HighamBench_P01_Checkpoint_Report.tex"
    tex_path.write_text(_render_latex(report), encoding="utf-8")
    if compile_pdf:
        _compile_pdf(output_dir, tex_path)
    return report


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark-root", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--compile-pdf", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        report = build_report(
            args.benchmark_root,
            args.results_root,
            args.output_dir,
            compile_pdf=args.compile_pdf,
        )
    except ReportError as error:
        print(f"P01 report rejected: {error}", file=sys.stderr)
        return 2
    print(
        "Authenticated private P01 checkpoint: "
        f"{report['final_scored_record_count']} final scored records; "
        f"report written to {args.output_dir.resolve()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
