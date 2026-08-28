#!/usr/bin/env python3
"""Build a detailed, standalone HighamBench construction report.

The short table renderer in ``analyze.py`` is useful for machine-facing result
artifacts. This program builds the longer report for every paper and task in
the current manifest. It deliberately refuses a partial or stale analysis: the
report is an end product, not a way to make an unfinished matrix look complete.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
from typing import Any, Iterable, Mapping, Sequence

try:
    from .common import FAILURE_CODES, BenchmarkToolError, read_json
    from .hashes import load_manifest, verify_manifest
    from .task_tags import validate_t4_task_metadata
    from . import run_matrix
    from . import codex_isolated
    from . import provider_token_gate
    from . import runner
    from . import run_token_control_canary as token_canary
    from . import run_ultra_orchestration_canary as ultra_canary
except ImportError:  # Direct script execution.
    from common import FAILURE_CODES, BenchmarkToolError, read_json  # type: ignore
    from hashes import load_manifest, verify_manifest  # type: ignore
    from task_tags import validate_t4_task_metadata  # type: ignore
    import run_matrix  # type: ignore
    import codex_isolated  # type: ignore
    import provider_token_gate  # type: ignore
    import runner  # type: ignore
    import run_token_control_canary as token_canary  # type: ignore
    import run_ultra_orchestration_canary as ultra_canary  # type: ignore


class ReportError(BenchmarkToolError):
    """The requested final report cannot be made from the supplied records."""


CONSTRUCTION_TOOL_PATHS = (
    "tools/check_construction.py",
    "tools/common.py",
    "tools/hashes.py",
    "tools/lean_isolated.py",
    "tools/preflight.py",
    "tools/validator.py",
    "tools/dependency_audit.lean",
)
PRUNED_LIBRARY_OLEAN_ROOT = (
    "paper_bencmark/scratch_pad/highambench_environment/numstability_olean"
)
PACKAGES_RUNTIME_ROOT = (
    "paper_bencmark/scratch_pad/highambench_environment/packages_runtime"
)
T4_SKELETON_PRIVATE_PROOF_NOTE = (
    "this skeleton-specific check is separate from the mandatory "
    "proof-complete private N/L solvability builds"
)
T4_PRIVATE_CONSTRUCTION_PROSE = (
    "T1--T4 private construction proofs are complete answers used only to "
    "establish that controlled tasks are solvable. For T4, proof-complete "
    "private N/L builds are mandatory in addition to the public "
    "designated-hole skeleton gate. The following "
)
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)
TOKEN_MEASUREMENT_SOURCE = "codex_app_server_rawResponse/completed"
TOKEN_USAGE_NOTIFICATION = "rawResponse/completed"
TOKEN_USAGE_SCOPE = "rooted_attempt_thread_tree_completed_responses"
ULTRA_OUTCOME_EXACTNESS = {
    "accepted_proof": {
        "required_evidence": "exact_authenticated_submission_boundary",
        "provider_gate_close_reason": "accepted_submission",
        "provider_requests_quiescent": True,
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "root_turn_active": True,
        "descendants_quiescent": True,
        "later_model_response_possible": False,
    },
    "token_limit": {
        "required_evidence": "sealed_sanitized_sole_inflight_crossing",
        "provider_gate_close_reason": "token_limit",
        "provider_requests_quiescent": True,
        "tree_quiescent": False,
        "drain_complete": False,
        "measurement_exact": True,
        "crossing_response_actions_released": False,
    },
    "scored_failure": {
        "required_evidence": "exact_natural_drain",
        "provider_gate_close_reason": "natural_end",
        "provider_requests_quiescent": True,
        "drain_complete": True,
        "measurement_exact": True,
        "tree_quiescent": True,
    },
    "unscorable_useful_work": {
        "trigger": "no_exact_authenticated_provider_gate_endpoint_for_outcome",
        "matrix_action": "abort_and_preserve_incident",
        "retry_allowed": False,
        "scored": False,
    },
}
LEGACY_TOKEN_MEASUREMENT_SOURCE = "codex_app_server_thread/tokenUsage/updated"
LEGACY_TOKEN_USAGE_NOTIFICATION = "thread/tokenUsage/updated"
LEGACY_TOKEN_USAGE_SCOPE = "thread"
TOKEN_CONTROL_CANARY_PATH = token_canary.FROZEN_EVIDENCE_PATH
TOKEN_CONTROL_CANARY_KEY = "token_control_live_canary"
TOKEN_CONTROL_CANARY_ARTIFACTS = token_canary.ARTIFACT_LABELS
ULTRA_ORCHESTRATION_CANARY_PATH = ultra_canary.FROZEN_EVIDENCE_PATH
ACCOUNTING_PROJECTION_SCHEMA_VERSION = (
    ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
)
ACCOUNTING_SPAWN_BINDING_SOURCE = (
    "raw_function_call.call_id=subAgentActivity.id"
)
ACCOUNTING_TOKEN_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)
ULTRA_FORK_POLICY_CALL_FIELDS = {
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
PROMPT_RELEASE_PROTOCOL_VERSION = "highambench-prompt-release-v1"
PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS = 120.0
PROMPT_RELEASE_GO_MINIMUM_WINDOW_SECONDS = 5.0
PROMPT_RELEASE_COMMON_FIELDS = {
    "schema_version",
    "protocol_version",
    "handshake_nonce",
    "run_id",
    "condition",
    "model",
    "reasoning_effort",
    "root_thread_id",
    "turn_start_request_id",
    "effective_prompt_sha256",
    "effective_prompt_bytes",
    "adapter_name",
    "adapter_version",
    "app_server_client_name",
    "app_server_client_version",
    "elapsed_clock",
}
PROMPT_RELEASE_ARTIFACTS = {
    "ready": ("ready_sha256", "highambench_prompt_ready", ".prompt-ready.json"),
    "go": ("go_sha256", "highambench_prompt_go", ".prompt-go.json"),
    "released": (
        "release_sha256",
        "highambench_prompt_released",
        ".prompt-release.json",
    ),
}
TOKEN_CANARY_PROMPT_RELEASE_FIELDS = {
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


def _valid_token_canary_prompt_release(value: Any) -> bool:
    """Independently check the token canary's authenticated timing summary."""

    if not isinstance(value, Mapping) or set(value) != TOKEN_CANARY_PROMPT_RELEASE_FIELDS:
        return False
    released = value.get("released_at_monotonic_ns")
    deadline = value.get("deadline_monotonic_ns")
    wall = value.get("wall_time_seconds")
    actual_stop = value.get("actual_stop_seconds")
    artifacts = value.get("artifacts")
    if (
        value.get("schema_version") != 1
        or value.get("protocol_version") != PROMPT_RELEASE_PROTOCOL_VERSION
        or value.get("status") != "released_authenticated"
        or value.get("authenticated") is not True
        or value.get("timing_exact") is not True
        or value.get("useful_work_basis") != "authenticated_release"
        or value.get("startup_timeout_seconds")
        != PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS
        or value.get("startup_timeout_triggered") is not False
        or value.get("go_minimum_release_window_seconds")
        != PROMPT_RELEASE_GO_MINIMUM_WINDOW_SECONDS
        or value.get("artifact_content_verified") is not True
        or value.get("artifact_count") != len(PROMPT_RELEASE_ARTIFACTS)
        or value.get("canonical_encoding")
        != "compact_sorted_key_utf8_json_newline"
        or value.get("sealed_mode") != "0444"
        or not _hex_digest(value.get("handshake_nonce"))
        or not isinstance(value.get("root_thread_id"), str)
        or not value.get("root_thread_id")
        or not _hex_digest(value.get("effective_prompt_sha256"))
        or not isinstance(value.get("effective_prompt_bytes"), int)
        or isinstance(value.get("effective_prompt_bytes"), bool)
        or value.get("effective_prompt_bytes") <= 0
        or not _hex_digest(value.get("turn_start_request_sha256"))
        or value.get("turn_start_wire_verified") is not True
        or value.get("command_binding_verified") is not True
        or value.get("root_identity_verified") is not True
        or any(
            not _hex_digest(value.get(field))
            for field in ("ready_sha256", "go_sha256", "release_sha256")
        )
        or value.get("measurement_time_origin")
        != "RELEASED.released_at_monotonic_ns"
        or type(released) is not int
        or released <= 0
        or type(deadline) is not int
        or type(wall) is not int
        or wall <= 0
        or deadline != released + wall * 1_000_000_000
        or value.get("deadline_derivation")
        != "released_at_monotonic_ns + wall_time_seconds*1000000000"
        or not isinstance(actual_stop, (int, float))
        or isinstance(actual_stop, bool)
        or not 0 < actual_stop < wall
        or value.get("token_crossing_within_deadline") is not True
        or value.get("first_valid_seconds") is not None
        or value.get("submission_boundary") is not None
        or value.get("sanitized_provider_gate_crossing") is not True
        or value.get("top_level_artifact_count_unchanged")
        != len(TOKEN_CONTROL_CANARY_ARTIFACTS)
        or not isinstance(artifacts, Mapping)
        or set(artifacts) != {"ready", "go", "release"}
    ):
        return False
    for label, suffix, top_hash in (
        ("ready", ".prompt-ready.json", "ready_sha256"),
        ("go", ".prompt-go.json", "go_sha256"),
        ("release", ".prompt-release.json", "release_sha256"),
    ):
        descriptor = artifacts.get(label)
        if (
            not isinstance(descriptor, Mapping)
            or set(descriptor) != {"path", "file_sha256", "record_sha256"}
            or not isinstance(descriptor.get("path"), str)
            or not Path(descriptor["path"]).is_absolute()
            or not descriptor["path"].endswith(suffix)
            or not _hex_digest(descriptor.get("file_sha256"))
            or descriptor.get("record_sha256") != value.get(top_hash)
        ):
            return False
    return True


def _uses_ultra_token_control(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and value.get("measurement_source") == TOKEN_MEASUREMENT_SOURCE
        and value.get("notification") == TOKEN_USAGE_NOTIFICATION
        and value.get("usage_scope") == TOKEN_USAGE_SCOPE
    )


def _valid_token_control(
    value: Any, limit_tokens: Any, *, require_feature_row: bool
) -> bool:
    """Check one complete Ultra or legacy frozen token-control contract."""

    if not isinstance(value, Mapping):
        return False
    required = {
        "cached_input_counted_once": True,
        "checked_before_submission_validation": True,
        "comparison": ">=",
        "input_includes_cached": True,
        "limit_tokens": limit_tokens,
        "live_update_sequence": True,
        "live_cumulative": True,
        "outer_runner_polling": True,
        "over_limit_pass_allowed": False,
        "trusted_usage_path_outside_workspace": True,
    }
    if any(value.get(name) != expected for name, expected in required.items()):
        return False
    ultra = {
        "control": "loopback_provider_response_admission_gate",
        "measurement_source": TOKEN_MEASUREMENT_SOURCE,
        "notification": TOKEN_USAGE_NOTIFICATION,
        "usage_scope": TOKEN_USAGE_SCOPE,
        "one_response_overshoot_possible": True,
        "concurrent_inflight_overshoot_possible": False,
        "all_descendant_threads_included": True,
        "response_ids_deduplicated": True,
        "outcome_exactness": ULTRA_OUTCOME_EXACTNESS,
        "measurement_exact_required": True,
        "root_completion_is_tree_barrier": False,
        "trusted_adapter_freezes_first_threshold": True,
        "trusted_adapter_latches_first_threshold": True,
        "provider_gate_protocol": runner.PROVIDER_GATE_PROTOCOL,
        "provider_response_bound_tokens": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        "strict_admission_inequality": (
            "completed_tokens + (open_request_count + 1) * "
            "response_bound < token_limit"
        ),
        "crossing_response_release": runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY,
        "crossing_response_actions_released": False,
        "provider_requests_quiescent_at_scored_endpoint": True,
        "tree_quiescence_distinct_from_provider_quiescence": True,
    }
    legacy = {
        "control": "app_server_live_cumulative_usage",
        "measurement_source": LEGACY_TOKEN_MEASUREMENT_SOURCE,
        "notification": LEGACY_TOKEN_USAGE_NOTIFICATION,
        "usage_scope": LEGACY_TOKEN_USAGE_SCOPE,
        "one_response_overshoot_possible": True,
        "trusted_adapter_freezes_first_threshold": True,
    }
    matches_ultra = all(
        value.get(name) == expected for name, expected in ultra.items()
    )
    ultra_only_fields = set(ultra) - set(legacy)
    matches_legacy = all(
        value.get(name) == expected for name, expected in legacy.items()
    ) and all(name not in value for name in ultra_only_fields)
    if not (matches_ultra or matches_legacy):
        return False
    advisory = value.get("advisory_rollout_budget")
    if not isinstance(advisory, Mapping):
        return False
    advisory_required = {
        "enabled": True,
        "feature": "rollout_budget",
        "limit_tokens": limit_tokens,
        "prefill_token_weight": 1,
        "role": "advisory_only",
        "sampling_token_weight": 1,
        "strict_config": True,
    }
    if any(
        advisory.get(name) != expected
        for name, expected in advisory_required.items()
    ):
        return False
    feature_row = advisory.get("feature_row")
    return not require_feature_row or (
        isinstance(feature_row, str) and feature_row.startswith("rollout_budget ")
    )


def _package_runtime_file_kind(relative: str) -> str | None:
    if relative == "mathlib/Mathlib.lean" or (
        relative.startswith("mathlib/Mathlib/") and relative.endswith(".lean")
    ):
        return "source"
    if "/.lake/build/lib/lean/" not in relative:
        return None
    if relative.endswith(".olean"):
        return "olean"
    if relative.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES):
        return "compiled_support"
    return None


@dataclass(frozen=True)
class ReportInputs:
    benchmark_root: Path
    config: Mapping[str, Any]
    environment: Mapping[str, Any]
    manifest: Mapping[str, Any]
    run_order: Mapping[str, Any]
    papers: tuple[Mapping[str, Any], ...]
    tasks: tuple[Mapping[str, Any], ...]
    evidence: Mapping[str, Mapping[str, Any]]
    construction_check: Mapping[str, Any]
    freeze_check: Mapping[str, Any]
    release_manifest: Mapping[str, Any]
    compiled_environment_summary: Mapping[str, Any]
    packages_runtime_manifest: Mapping[str, Any]
    source_manifest: Mapping[str, Any]
    compiled_manifest: Mapping[str, Any]
    reviews: tuple[Mapping[str, Any], ...]
    analysis: Mapping[str, Any]
    shared_source: str


def _object(path: Path, label: str) -> Mapping[str, Any]:
    if not path.is_file():
        raise ReportError(f"missing {label}: {path}")
    value = read_json(path)
    if not isinstance(value, Mapping):
        raise ReportError(f"{label} must be a JSON object: {path}")
    return value


def _document_digest(value: Mapping[str, Any]) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _hex_digest(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(
        character in "0123456789abcdef" for character in value
    )


_PROVIDER_GATE_RUN_SUMMARY_FIELDS = {
    "required",
    "status",
    "protocol",
    "cleanup_grace_seconds",
    "implementation_source_sha256",
    "model_catalog",
    "transport_provenance",
    "live",
    "final",
    "error",
}
_PROVIDER_GATE_MODEL_CATALOG_FIELDS = {
    "catalog_sha256",
    "entry_sha256",
    "response_bound",
}
_PROVIDER_GATE_FILE_FIELDS = {
    "path",
    "absolute",
    "exists",
    "regular_non_symlink",
    "mode",
    "size_bytes",
    "file_sha256",
}
_PROVIDER_GATE_FINAL_AUTH_FIELDS = {
    "path",
    "file_sha256",
    "record_sha256",
    "size_bytes",
    "mode",
    "authenticated",
    "record",
    "derived",
}
_PROVIDER_GATE_DERIVED_FIELDS = {
    "completed_tokens",
    "response_count",
    "response_ids",
    "provider_response_count",
    "provider_response_ids",
    "appserver_response_count",
    "appserver_response_ids",
    "suppressed_collaboration_wait_response_count",
    "suppressed_collaboration_wait_response_ids",
    "superseded_by_collaboration_message_response_count",
    "superseded_by_collaboration_message_response_ids",
    "discarded_after_explicit_child_interrupt_response_count",
    "discarded_after_explicit_child_interrupt_response_ids",
    "first_crossing",
    "poisoned",
    "appserver_deliveries_reconciled",
}
_ULTRA_LIMIT_ENFORCEMENT_FIELDS = {
    "mode",
    "notification",
    "configured_limit_tokens",
    "triggered",
    "observed_tokens",
    "overshoot_tokens",
    "first_crossing_tokens",
    "first_crossing_overshoot_tokens",
    "final_endpoint_tokens",
    "final_overshoot_tokens",
    "checked_before_submission_validation",
    "one_response_overshoot_possible",
    "concurrent_inflight_overshoot_possible",
}
_TOKEN_CANARY_SUMMARY_FIELDS = {
    "path",
    "sha256",
    "status",
    "canary_limit_tokens",
    "first_crossing_tokens",
    "final_endpoint_tokens",
    "thread_count",
    "observed_child_thread_count",
    "response_count",
    "drain_complete",
    "provider_gate_quiescent",
    "measurement_exact",
    "synthetic_input",
    "matrix_assignment",
    "benchmark_task_bytes_used",
    "prompt_protocol",
    "prompt_release",
    "source_separation_audit_sha256",
    "accounting_projection",
    "artifacts",
}


def _gate_object(value: Any, fields: set[str] | frozenset[str], label: str) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != set(fields):
        raise ReportError(f"{label} has a missing or extra field")
    return dict(value)


def _gate_nonnegative(value: Any, label: str) -> int:
    if type(value) is not int or value < 0:
        raise ReportError(f"{label} is not a nonnegative integer")
    return value


def _gate_positive(value: Any, label: str) -> int:
    result = _gate_nonnegative(value, label)
    if result == 0:
        raise ReportError(f"{label} is not positive")
    return result


def _gate_string(value: Any, label: str, *, nullable: bool = False) -> str | None:
    if value is None and nullable:
        return None
    if not isinstance(value, str) or not value or "\x00" in value:
        raise ReportError(f"{label} is not a nonempty string")
    return value


def _collaboration_event_observation_is_between_calls(
    *,
    event_unix_ns: Any,
    receipt_monotonic_ns: Any,
    provider_commit_unix_ns: Any,
    successor_admitted_unix_ns: Any,
) -> bool:
    """Use authenticated event time for the provider-call window.

    ``receipt_monotonic_ns`` is captured when the adapter reads the event.  A
    busy reader can observe it after the successor request was admitted, so it
    is only a positive local audit timestamp and is not a gate-window clock.
    The event clock has millisecond resolution, so its whole possible interval
    must end no later than the successor admission.
    """

    return bool(
        type(event_unix_ns) is int
        and event_unix_ns > 0
        and type(receipt_monotonic_ns) is int
        and receipt_monotonic_ns > 0
        and type(provider_commit_unix_ns) is int
        and provider_commit_unix_ns > 0
        and type(successor_admitted_unix_ns) is int
        and successor_admitted_unix_ns > 0
        and provider_commit_unix_ns < event_unix_ns
        and event_unix_ns + 1_000_000 <= successor_admitted_unix_ns
    )


def _rooted_collaboration_route_matches(
    *,
    thread_id: Any,
    author: Any,
    recipient: Any,
    thread_accounting: Any,
    root_thread_id: Any,
) -> bool:
    """Independently authenticate one direct parent/child message route."""

    if not all(
        isinstance(item, str) and item
        for item in (thread_id, author, recipient, root_thread_id)
    ) or not isinstance(thread_accounting, list):
        return False
    threads: dict[str, Mapping[str, Any]] = {}
    agent_paths: dict[str, str] = {}
    for raw_thread in thread_accounting:
        if not isinstance(raw_thread, Mapping):
            return False
        candidate_id = raw_thread.get("thread_id")
        if (
            not isinstance(candidate_id, str)
            or not candidate_id
            or candidate_id in threads
        ):
            return False
        is_root = candidate_id == root_thread_id
        candidate_path = "/root" if is_root else raw_thread.get("agent_path")
        if (
            not isinstance(candidate_path, str)
            or not candidate_path
            or candidate_path in agent_paths
            or (
                is_root
                and (
                    raw_thread.get("agent_path") != "root"
                    or raw_thread.get("parent_thread_id") is not None
                    or raw_thread.get("provisional") is not False
                    or raw_thread.get("spawn_binding_status") != "root_zero"
                )
            )
            or (
                not is_root
                and (
                    not candidate_path.startswith("/root/")
                    or raw_thread.get("provisional") is not False
                    or raw_thread.get("spawn_binding_status") != "resolved"
                )
            )
        ):
            return False
        threads[candidate_id] = raw_thread
        agent_paths[candidate_path] = candidate_id
    target = threads.get(thread_id)
    target_path = "/root" if thread_id == root_thread_id else (
        target.get("agent_path") if isinstance(target, Mapping) else None
    )
    author_thread_id = agent_paths.get(author)
    if (
        not isinstance(target, Mapping)
        or recipient != target_path
        or author_thread_id is None
        or author_thread_id == thread_id
    ):
        return False
    author_thread = threads[author_thread_id]
    return bool(
        target.get("parent_thread_id") == author_thread_id
        or author_thread.get("parent_thread_id") == thread_id
    )


def _validate_explicit_child_interrupt_discard(
    *,
    evidence_value: Any,
    target: Mapping[str, Any],
    interrupting: Mapping[str, Any],
    thread_accounting: Any,
    root_thread_id: Any,
    label: str,
) -> dict[str, Any]:
    """Independently bind one complete child response to its parent interrupt."""

    evidence = _gate_object(
        evidence_value,
        codex_isolated.DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS,
        label,
    )
    string_fields = (
        "response_id",
        "provider_call_id",
        "thread_id",
        "turn_id",
        "interrupting_response_id",
        "interrupting_provider_call_id",
        "interrupt_function_item_id",
        "interrupt_function_call_id",
        "interrupt_parent_thread_id",
        "interrupt_parent_turn_id",
        "interrupted_agent_path",
        "interrupt_output_item_id",
    )
    digest_fields = (
        "interrupt_function_arguments_sha256",
        "interrupt_activity_item_sha256",
        "interrupt_output_item_sha256",
    )
    if any(
        not isinstance(evidence.get(field), str) or not evidence[field]
        for field in string_fields
    ) or any(not _hex_digest(evidence.get(field)) for field in digest_fields):
        raise ReportError(f"{label} has malformed identity or digest evidence")

    target_metadata = target.get("request_metadata")
    target_delivery = target.get("appserver_delivery")
    interrupt_metadata = interrupting.get("request_metadata")
    interrupt_delivery = interrupting.get("appserver_delivery")
    interrupt_crossbind = interrupting.get("appserver_crossbind")
    if not all(
        isinstance(value, Mapping)
        for value in (
            target_metadata,
            target_delivery,
            interrupt_metadata,
            interrupt_delivery,
            interrupt_crossbind,
        )
    ):
        raise ReportError(f"{label} lacks its provider delivery pair")
    assert isinstance(target_metadata, Mapping)
    assert isinstance(target_delivery, Mapping)
    assert isinstance(interrupt_metadata, Mapping)
    assert isinstance(interrupt_delivery, Mapping)
    assert isinstance(interrupt_crossbind, Mapping)
    if (
        evidence.get("response_id") != target.get("response_id")
        or evidence.get("provider_call_id") != target.get("call_id")
        or evidence.get("thread_id") != target_metadata.get("thread_id")
        or evidence.get("turn_id") != target_metadata.get("turn_id")
        or evidence.get("interrupting_response_id")
        != interrupting.get("response_id")
        or evidence.get("interrupting_provider_call_id")
        != interrupting.get("call_id")
        or evidence.get("interrupt_parent_thread_id")
        != interrupt_metadata.get("thread_id")
        or evidence.get("interrupt_parent_turn_id")
        != interrupt_metadata.get("turn_id")
        or target_metadata.get("request_kind") != "turn"
        or interrupt_metadata.get("request_kind") != "turn"
        or target_metadata.get("thread_id") == interrupt_metadata.get("thread_id")
        or target.get("appserver_crossbind") is not None
        or target.get("client_release_complete") is not False
        or target.get("error") is not None
        or target.get("crossed_cap") is not False
        or target.get("release_kind") != "byte_identity"
        or target_delivery.get("kind")
        != provider_token_gate.PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
        or target_delivery.get("successor_call_id") != interrupting.get("call_id")
        or target_delivery.get("successor_response_id")
        != interrupting.get("response_id")
        or interrupting.get("client_release_complete") is not True
        or interrupting.get("error") is not None
        or interrupting.get("crossed_cap") is not False
        or interrupting.get("release_kind") != "byte_identity"
        or interrupt_delivery.get("kind")
        != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
        or interrupt_delivery.get("successor_call_id") is not None
        or interrupt_delivery.get("successor_response_id") is not None
        or interrupt_crossbind.get("thread_id") != interrupt_metadata.get("thread_id")
        or interrupt_crossbind.get("turn_id") != interrupt_metadata.get("turn_id")
        or interrupt_delivery.get("bind_unix_ns")
        != interrupt_crossbind.get("bind_unix_ns")
        or interrupt_delivery.get("bind_monotonic_ns")
        != interrupt_crossbind.get("bind_monotonic_ns")
    ):
        raise ReportError(f"{label} provider target/interrupt binding changed")

    manifest = interrupting.get("response_output_manifest")
    items = manifest.get("items") if isinstance(manifest, Mapping) else None
    item = items[0] if isinstance(items, list) and len(items) == 1 else None
    if (
        not isinstance(manifest, Mapping)
        or manifest.get("output_item_count") != 1
        or manifest.get("action_capable_item_count") != 1
        or not isinstance(item, Mapping)
        or item.get("index") != 0
        or item.get("type") != "function_call"
        or item.get("name") != "interrupt_agent"
        or item.get("namespace") != "collaboration"
        or item.get("id") != evidence.get("interrupt_function_item_id")
        or item.get("call_id") != evidence.get("interrupt_function_call_id")
        or item.get("arguments_sha256")
        != evidence.get("interrupt_function_arguments_sha256")
        or type(item.get("arguments_bytes")) is not int
        or item.get("arguments_bytes", 0) <= 0
        or item.get("wait_timeout_ms") is not None
    ):
        raise ReportError(f"{label} interrupt_agent manifest binding changed")

    if not isinstance(root_thread_id, str) or not root_thread_id or not isinstance(
        thread_accounting, list
    ):
        raise ReportError(f"{label} lacks a resolved rooted thread tree")
    threads: dict[str, Mapping[str, Any]] = {}
    agent_paths: set[str] = set()
    for raw_thread in thread_accounting:
        thread_id = raw_thread.get("thread_id") if isinstance(raw_thread, Mapping) else None
        agent_path = raw_thread.get("agent_path") if isinstance(raw_thread, Mapping) else None
        if (
            not isinstance(raw_thread, Mapping)
            or not isinstance(thread_id, str)
            or not thread_id
            or thread_id in threads
            or not isinstance(agent_path, str)
            or not agent_path
            or agent_path in agent_paths
        ):
            raise ReportError(f"{label} rooted thread tree is malformed")
        threads[thread_id] = raw_thread
        agent_paths.add(agent_path)
    child = threads.get(str(evidence["thread_id"]))
    parent = threads.get(str(evidence["interrupt_parent_thread_id"]))
    root = threads.get(root_thread_id)
    parent_path = (
        "/root"
        if evidence.get("interrupt_parent_thread_id") == root_thread_id
        else parent.get("agent_path") if isinstance(parent, Mapping) else None
    )
    if (
        not isinstance(child, Mapping)
        or not isinstance(parent, Mapping)
        or not isinstance(root, Mapping)
        or root.get("agent_path") != "root"
        or root.get("parent_thread_id") is not None
        or root.get("provisional") is not False
        or root.get("spawn_binding_status") != "root_zero"
        or child.get("parent_thread_id") != evidence.get("interrupt_parent_thread_id")
        or child.get("agent_path") != evidence.get("interrupted_agent_path")
        or not str(evidence.get("interrupted_agent_path")).startswith("/root/")
        or not isinstance(parent_path, str)
        or str(evidence.get("interrupted_agent_path")).rsplit("/", 1)[0]
        != parent_path
        or child.get("provisional") is not False
        or child.get("spawn_binding_status") != "resolved"
        or child.get("turn_seen") is not True
        or (
            evidence.get("interrupt_parent_thread_id") == root_thread_id
            and (
                parent.get("agent_path") != "root"
                or parent.get("parent_thread_id") is not None
                or parent.get("provisional") is not False
                or parent.get("spawn_binding_status") != "root_zero"
            )
        )
        or (
            evidence.get("interrupt_parent_thread_id") != root_thread_id
            and (
                not str(parent.get("agent_path", "")).startswith("/root/")
                or parent.get("provisional") is not False
                or parent.get("spawn_binding_status") != "resolved"
            )
        )
    ):
        raise ReportError(f"{label} does not resolve to a direct interrupted child")

    for suffix in ("unix_ns", "monotonic_ns"):
        target_admitted = target.get(f"admitted_{suffix}")
        interrupt_admitted = interrupting.get(f"admitted_{suffix}")
        interrupt_commit = interrupting.get(f"commit_{suffix}")
        interrupt_bind = interrupt_delivery.get(f"bind_{suffix}")
        target_commit = target.get(f"commit_{suffix}")
        target_bind = target_delivery.get(f"bind_{suffix}")
        provider_times = (
            target_admitted,
            interrupt_admitted,
            interrupt_commit,
            interrupt_bind,
            target_commit,
            target_bind,
        )
        if (
            not all(type(value) is int and value > 0 for value in provider_times)
            or max(target_admitted, interrupt_admitted) >= interrupt_commit
            or not interrupt_commit < interrupt_bind < target_commit < target_bind
        ):
            raise ReportError(f"{label} provider lifecycle timing changed")
    unix_times = tuple(
        evidence.get(f"{name}_observed_at_unix_ns")
        for name in (
            "interrupt_function",
            "interrupt_activity",
            "interrupt_output",
            "interrupted_turn",
        )
    )
    monotonic_times = tuple(
        evidence.get(f"{name}_observed_at_monotonic_ns")
        for name in (
            "interrupt_function",
            "interrupt_activity",
            "interrupt_output",
            "interrupted_turn",
        )
    )
    resolution_ns = codex_isolated.APP_SERVER_EVENT_TIME_RESOLUTION_NS
    if (
        not all(type(value) is int and value > 0 for value in unix_times + monotonic_times)
        or any(later < earlier for earlier, later in zip(unix_times, unix_times[1:]))
        or any(later <= earlier for earlier, later in zip(monotonic_times, monotonic_times[1:]))
        or target.get("admitted_unix_ns", 0) >= unix_times[0]
        or interrupting.get("commit_unix_ns", 0) >= unix_times[0]
        or any(value + resolution_ns > target.get("commit_unix_ns", 0) for value in unix_times)
    ):
        raise ReportError(f"{label} interrupt event timing changed")
    return evidence


def _validate_projected_explicit_child_interrupt_evidence(
    *,
    evidence_value: Any,
    discarded_response_id: str,
    interrupting: Mapping[str, Any],
    thread_accounting: Any,
    root_thread_id: Any,
    label: str,
) -> dict[str, Any]:
    """Recheck the portion of an interrupt discard retained by projection v6."""

    evidence = _gate_object(
        evidence_value,
        codex_isolated.DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS,
        label,
    )
    required_strings = (
        "response_id",
        "provider_call_id",
        "thread_id",
        "turn_id",
        "interrupting_response_id",
        "interrupting_provider_call_id",
        "interrupt_function_item_id",
        "interrupt_function_call_id",
        "interrupt_parent_thread_id",
        "interrupt_parent_turn_id",
        "interrupted_agent_path",
        "interrupt_output_item_id",
    )
    if (
        any(
            not isinstance(evidence.get(field), str) or not evidence[field]
            for field in required_strings
        )
        or any(
            not _hex_digest(evidence.get(field))
            for field in (
                "interrupt_function_arguments_sha256",
                "interrupt_activity_item_sha256",
                "interrupt_output_item_sha256",
            )
        )
        or evidence.get("response_id") != discarded_response_id
        or evidence.get("interrupting_response_id")
        != interrupting.get("response_id")
        or evidence.get("interrupting_provider_call_id")
        != interrupting.get("call_id")
    ):
        raise ReportError(f"{label} identity or digest binding changed")
    metadata = interrupting.get("request_metadata")
    delivery = interrupting.get("appserver_delivery")
    crossbind = interrupting.get("appserver_crossbind")
    manifest = interrupting.get("response_output_manifest")
    items = manifest.get("items") if isinstance(manifest, Mapping) else None
    item = items[0] if isinstance(items, list) and len(items) == 1 else None
    if (
        not isinstance(metadata, Mapping)
        or evidence.get("interrupt_parent_thread_id") != metadata.get("thread_id")
        or evidence.get("interrupt_parent_turn_id") != metadata.get("turn_id")
        or metadata.get("request_kind") != "turn"
        or interrupting.get("client_release_complete") is not True
        or interrupting.get("error") is not None
        or interrupting.get("crossed_cap") is not False
        or interrupting.get("release_kind") != "byte_identity"
        or not isinstance(delivery, Mapping)
        or delivery.get("kind") != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
        or delivery.get("successor_call_id") is not None
        or delivery.get("successor_response_id") is not None
        or not isinstance(crossbind, Mapping)
        or delivery.get("bind_unix_ns") != crossbind.get("bind_unix_ns")
        or delivery.get("bind_monotonic_ns") != crossbind.get("bind_monotonic_ns")
        or not isinstance(manifest, Mapping)
        or manifest.get("output_item_count") != 1
        or manifest.get("action_capable_item_count") != 1
        or not isinstance(item, Mapping)
        or item.get("index") != 0
        or item.get("type") != "function_call"
        or item.get("name") != "interrupt_agent"
        or item.get("namespace") != "collaboration"
        or item.get("id") != evidence.get("interrupt_function_item_id")
        or item.get("call_id") != evidence.get("interrupt_function_call_id")
        or item.get("arguments_sha256")
        != evidence.get("interrupt_function_arguments_sha256")
        or type(item.get("arguments_bytes")) is not int
        or item.get("arguments_bytes", 0) <= 0
        or item.get("wait_timeout_ms") is not None
    ):
        raise ReportError(f"{label} direct interrupting call changed")

    threads = {
        raw.get("thread_id"): raw
        for raw in thread_accounting
        if isinstance(raw, Mapping) and isinstance(raw.get("thread_id"), str)
    } if isinstance(thread_accounting, list) else {}
    child = threads.get(evidence.get("thread_id"))
    parent = threads.get(evidence.get("interrupt_parent_thread_id"))
    root = threads.get(root_thread_id)
    parent_path = (
        "/root"
        if evidence.get("interrupt_parent_thread_id") == root_thread_id
        else parent.get("agent_path") if isinstance(parent, Mapping) else None
    )
    if (
        len(threads) != len(thread_accounting or [])
        or not isinstance(root_thread_id, str)
        or not isinstance(child, Mapping)
        or not isinstance(parent, Mapping)
        or not isinstance(root, Mapping)
        or root.get("agent_path") != "root"
        or root.get("parent_thread_id") is not None
        or root.get("provisional") is not False
        or root.get("spawn_binding_status") != "root_zero"
        or child.get("parent_thread_id") != evidence.get("interrupt_parent_thread_id")
        or child.get("agent_path") != evidence.get("interrupted_agent_path")
        or not str(evidence.get("interrupted_agent_path")).startswith("/root/")
        or not isinstance(parent_path, str)
        or str(evidence.get("interrupted_agent_path")).rsplit("/", 1)[0]
        != parent_path
        or child.get("provisional") is not False
        or child.get("spawn_binding_status") != "resolved"
        or child.get("turn_seen") is not True
        or (
            evidence.get("interrupt_parent_thread_id") == root_thread_id
            and (
                parent.get("agent_path") != "root"
                or parent.get("parent_thread_id") is not None
                or parent.get("provisional") is not False
                or parent.get("spawn_binding_status") != "root_zero"
            )
        )
    ):
        raise ReportError(f"{label} resolved parent-child tree changed")
    unix_times = tuple(
        evidence.get(f"{name}_observed_at_unix_ns")
        for name in (
            "interrupt_function",
            "interrupt_activity",
            "interrupt_output",
            "interrupted_turn",
        )
    )
    monotonic_times = tuple(
        evidence.get(f"{name}_observed_at_monotonic_ns")
        for name in (
            "interrupt_function",
            "interrupt_activity",
            "interrupt_output",
            "interrupted_turn",
        )
    )
    if (
        not all(type(value) is int and value > 0 for value in unix_times + monotonic_times)
        or any(later < earlier for earlier, later in zip(unix_times, unix_times[1:]))
        or any(later <= earlier for earlier, later in zip(monotonic_times, monotonic_times[1:]))
        or interrupting.get("commit_unix_ns", 0) >= unix_times[0]
    ):
        raise ReportError(f"{label} event chronology changed")
    return evidence


def _gate_canonical_newline(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def _gate_usage(value: Any, label: str) -> dict[str, int]:
    result = _gate_object(value, set(ACCOUNTING_TOKEN_FIELDS), label)
    normalized = {
        field: _gate_nonnegative(result[field], f"{label}.{field}")
        for field in ACCOUNTING_TOKEN_FIELDS
    }
    if (
        normalized["cached_input_tokens"] > normalized["input_tokens"]
        or normalized["cache_write_input_tokens"] > normalized["input_tokens"]
        or normalized["reasoning_output_tokens"] > normalized["output_tokens"]
        or normalized["total_tokens"]
        != normalized["input_tokens"] + normalized["output_tokens"]
    ):
        raise ReportError(f"{label} is not a consistent six-field usage record")
    return normalized


def _gate_normalize_provider_usage(value: Any, label: str) -> dict[str, int]:
    if not isinstance(value, Mapping):
        raise ReportError(f"{label} is not a provider usage object")
    input_tokens = _gate_nonnegative(value.get("input_tokens"), f"{label}.input_tokens")
    output_tokens = _gate_nonnegative(value.get("output_tokens"), f"{label}.output_tokens")
    total_tokens = _gate_nonnegative(value.get("total_tokens"), f"{label}.total_tokens")
    input_details = value.get("input_tokens_details", {})
    output_details = value.get("output_tokens_details", {})
    if not isinstance(input_details, Mapping) or not isinstance(output_details, Mapping):
        raise ReportError(f"{label} token details are malformed")
    normalized = {
        "input_tokens": input_tokens,
        "cached_input_tokens": _gate_nonnegative(
            input_details.get("cached_tokens", 0), f"{label}.cached_tokens"
        ),
        "cache_write_input_tokens": _gate_nonnegative(
            input_details.get("cache_write_tokens", 0), f"{label}.cache_write_tokens"
        ),
        "output_tokens": output_tokens,
        "reasoning_output_tokens": _gate_nonnegative(
            output_details.get("reasoning_tokens", 0), f"{label}.reasoning_tokens"
        ),
        "total_tokens": total_tokens,
    }
    if total_tokens != input_tokens + output_tokens:
        raise ReportError(f"{label} total is not input plus output")
    return _gate_usage(normalized, label)


def _gate_validate_response_output_manifest(
    value: Any, response_id: str, label: str
) -> bool:
    """Validate the privacy-preserving response shape retained by gate v6.

    The return value says whether the response is exactly one collaboration
    wait action plus optional reasoning items.  No response text or arguments
    are retained in this report path.
    """

    manifest = _gate_object(
        value,
        provider_token_gate.PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
        f"{label} output manifest",
    )
    output_count = _gate_nonnegative(
        manifest.get("output_item_count"), f"{label} output count"
    )
    action_count = _gate_nonnegative(
        manifest.get("action_capable_item_count"), f"{label} action count"
    )
    items = manifest.get("items")
    if (
        manifest.get("schema_version")
        != provider_token_gate.PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_SCHEMA_VERSION
        or type(manifest.get("schema_version")) is not int
        or manifest.get("response_id") != response_id
        or not isinstance(items, list)
        or len(items) != output_count
    ):
        raise ReportError(f"{label} output manifest identity/count changed")

    computed_actions = 0
    wait_items: list[dict[str, Any]] = []
    for index, raw_item in enumerate(items):
        item = _gate_object(
            raw_item,
            provider_token_gate.PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
            f"{label} output item {index}",
        )
        item_type = item.get("type")
        if (
            item.get("index") != index
            or type(item.get("index")) is not int
            or not isinstance(item_type, str)
            or not item_type.strip()
        ):
            raise ReportError(f"{label} output manifest item identity changed")
        if item_type == "function_call" or item_type.endswith("_call"):
            computed_actions += 1
        for field in ("id", "name", "namespace", "call_id"):
            field_value = item.get(field)
            if field_value is not None and (
                not isinstance(field_value, str) or not field_value.strip()
            ):
                raise ReportError(f"{label} output item {field} is malformed")
        if (
            not _hex_digest(item.get("payload_sha256"))
            or _gate_positive(
                item.get("payload_bytes"), f"{label} output payload bytes"
            )
            <= 0
        ):
            raise ReportError(f"{label} output item payload evidence changed")
        arguments_sha = item.get("arguments_sha256")
        arguments_bytes = item.get("arguments_bytes")
        if arguments_sha is None or arguments_bytes is None:
            if arguments_sha is not None or arguments_bytes is not None:
                raise ReportError(f"{label} output argument evidence is incomplete")
        elif (
            not _hex_digest(arguments_sha)
            or _gate_nonnegative(
                arguments_bytes, f"{label} output argument bytes"
            )
            < 0
        ):
            raise ReportError(f"{label} output argument evidence changed")
        timeout = item.get("wait_timeout_ms")
        if timeout is not None:
            if (
                type(timeout) is not int
                or not (
                    provider_token_gate.PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS
                    <= timeout
                    <= provider_token_gate.PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS
                )
                or item_type != "function_call"
                or item.get("name") != "wait_agent"
                or item.get("namespace") != "collaboration"
                or not isinstance(item.get("id"), str)
                or not isinstance(item.get("call_id"), str)
                or arguments_sha is None
            ):
                raise ReportError(f"{label} collaboration-wait manifest changed")
            wait_items.append(item)
    if computed_actions != action_count:
        raise ReportError(f"{label} action-capable output count changed")
    return (
        action_count == 1
        and len(wait_items) == 1
        and all(
            item.get("wait_timeout_ms") is not None
            or item.get("type") == "reasoning"
            for item in items
        )
    )


def _gate_superseded_delivery_is_exact(
    call: Mapping[str, Any],
    metadata: Mapping[str, Any],
    delivery: Mapping[str, Any],
) -> bool:
    """Check the transport facts for a response superseded by a message.

    The response manifest is validated generically before this check.  Its
    output shape is deliberately irrelevant: app-server can supersede a
    message-only response, a collaboration send, or another tool response.
    """

    return bool(
        call.get("appserver_crossbind") is None
        and metadata.get("request_kind") == "turn"
        and call.get("crossed_cap") is False
        and call.get("release_kind") == "byte_identity"
        and isinstance(delivery.get("successor_call_id"), str)
        and delivery.get("successor_call_id")
        and isinstance(delivery.get("successor_response_id"), str)
        and delivery.get("successor_response_id")
    )


def _gate_usage_sum(calls: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {
        field: sum(int(call["normalized_usage"][field]) for call in calls)
        for field in ACCOUNTING_TOKEN_FIELDS
    }


def _gate_read_sealed(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    """Read one immutable gate record through a no-follow descriptor."""

    if not path.is_absolute():
        raise ReportError(f"{label} path is not absolute")
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise ReportError(f"cannot open {label}: {error}") from error
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or stat.S_IMODE(metadata.st_mode) != 0o444
            or metadata.st_size <= 0
            or metadata.st_size > 128 * 1024 * 1024
        ):
            raise ReportError(f"{label} is not a bounded mode-0444 regular file")
        chunks: list[bytes] = []
        remaining = metadata.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) != metadata.st_size:
            raise ReportError(f"{label} changed while it was read")
    finally:
        os.close(descriptor)
    try:
        current = path.lstat()
    except OSError as error:
        raise ReportError(f"{label} disappeared after it was read") from error
    if (
        stat.S_ISLNK(current.st_mode)
        or current.st_dev != metadata.st_dev
        or current.st_ino != metadata.st_ino
        or current.st_size != metadata.st_size
        or stat.S_IMODE(current.st_mode) != 0o444
    ):
        raise ReportError(f"{label} identity changed while it was authenticated")
    try:
        value = json.loads(payload.decode("utf-8"))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise ReportError(f"{label} is not UTF-8 JSON: {error}") from error
    record = _gate_object(value, runner.PROVIDER_GATE_TOP_LEVEL_KEYS, label)
    if payload != _gate_canonical_newline(record):
        raise ReportError(f"{label} is not canonical newline-terminated JSON")
    unsigned = {key: item for key, item in record.items() if key != "record_sha256"}
    if (
        not _hex_digest(record.get("record_sha256"))
        or hashlib.sha256(_gate_canonical_newline(unsigned)).hexdigest()
        != record.get("record_sha256")
    ):
        raise ReportError(f"{label} self-hash is invalid")
    return record, payload


def _gate_dependency(
    value: Any,
    label: str,
    *,
    authenticated_historical_snapshot: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Validate one transport dependency, including historical node-local state.

    Production/current validation still rereads the dependency from disk.  A
    report over a completed paired-hardware campaign may instead supply the
    exact independently authenticated launch-time ``/etc/hosts`` descriptor.
    That file is node-local and can legitimately differ on the node rendering
    the report.  No other dependency is eligible for historical validation.
    """

    dependency = _gate_object(value, runner.PROVIDER_TRANSPORT_DEPENDENCY_KEYS, label)
    logical = dependency.get("logical_path")
    resolved = dependency.get("resolved_path")
    symlink_target = dependency.get("symlink_target")
    if (
        not isinstance(logical, str)
        or not os.path.isabs(logical)
        or not isinstance(resolved, str)
        or not os.path.isabs(resolved)
        or resolved.endswith(" (deleted)")
        or (symlink_target is not None and (not isinstance(symlink_target, str) or not symlink_target))
        or not _hex_digest(dependency.get("sha256"))
        or _gate_positive(dependency.get("bytes"), f"{label}.bytes") <= 0
        or not isinstance(dependency.get("mode"), str)
        or re.fullmatch(r"0[0-7]{3}", str(dependency.get("mode"))) is None
    ):
        raise ReportError(f"{label} transport dependency descriptor is malformed")
    if authenticated_historical_snapshot is not None:
        snapshot = _gate_object(
            authenticated_historical_snapshot,
            runner.PROVIDER_TRANSPORT_DEPENDENCY_KEYS,
            f"{label} authenticated historical snapshot",
        )
        if (
            logical != runner.PROVIDER_HOSTS_PATH
            or resolved != runner.PROVIDER_HOSTS_PATH
            or symlink_target is not None
        ):
            raise ReportError(
                f"{label} is not the fixed regular node-local hosts file"
            )
        if dependency != snapshot:
            raise ReportError(
                f"{label} does not match its authenticated historical snapshot"
            )
        return dependency
    resolved_path = Path(resolved)
    try:
        details = resolved_path.stat()
    except OSError as error:
        raise ReportError(f"{label} transport dependency is unavailable: {error}") from error
    if (
        not stat.S_ISREG(details.st_mode)
        or details.st_size != dependency["bytes"]
        or f"{stat.S_IMODE(details.st_mode):04o}" != dependency["mode"]
        or _file_digest(resolved_path) != dependency["sha256"]
    ):
        raise ReportError(f"{label} transport dependency no longer matches its bytes")
    return dependency


def _gate_transport(
    value: Any,
    label: str,
    *,
    authenticated_historical_hosts_file: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    provenance = _gate_object(value, runner.PROVIDER_TRANSPORT_PROVENANCE_KEYS, label)
    if (
        provenance.get("schema_version") != runner.PROVIDER_TRANSPORT_SCHEMA_VERSION
        or type(provenance.get("schema_version")) is not int
        or provenance.get("kind") != runner.PROVIDER_TRANSPORT_KIND
        or provenance.get("connection_factory_mode")
        != runner.PROVIDER_CONNECTION_FACTORY_MODE
    ):
        raise ReportError(f"{label} is not the production explicit-TLS transport")
    python = _gate_object(
        provenance.get("python"), runner.PROVIDER_TRANSPORT_PYTHON_KEYS, f"{label}.python"
    )
    if (
        python.get("executable") != "/usr/bin/python3.10"
        or not isinstance(python.get("version"), str)
        or re.fullmatch(r"3\.10\.\d+", str(python.get("version"))) is None
        or python.get("implementation") != "cpython"
        or python.get("socket_implementation") != "built-in"
    ):
        raise ReportError(f"{label} Python transport identity changed")
    python_dependencies = (
        "binary",
        "ssl_module",
        "http_client_module",
        "socket_module",
        "http_server_module",
        "json_module",
        "json_encoder_module",
        "json_decoder_module",
        "json_extension",
        "hashlib_module",
        "hashlib_extension",
        "ssl_extension",
    )
    descriptors = {
        field: _gate_dependency(python[field], f"{label}.python.{field}")
        for field in python_dependencies
    }
    if descriptors["binary"]["logical_path"] != python["executable"]:
        raise ReportError(f"{label} Python binary descriptor is unbound")

    openssl = _gate_object(
        provenance.get("openssl"), runner.PROVIDER_TRANSPORT_OPENSSL_KEYS, f"{label}.openssl"
    )
    if not isinstance(openssl.get("version"), str) or not openssl["version"]:
        raise ReportError(f"{label} OpenSSL version is missing")
    _gate_positive(openssl.get("version_number"), f"{label}.openssl.version_number")
    openssl_dependencies = {
        field: _gate_dependency(openssl[field], f"{label}.openssl.{field}")
        for field in ("libssl", "libcrypto", "config")
    }
    if (
        openssl_dependencies["config"]["logical_path"]
        != runner.PROVIDER_OPENSSL_CONFIG_PATH
        or not Path(openssl_dependencies["libssl"]["resolved_path"]).name.startswith("libssl.so")
        or not Path(openssl_dependencies["libcrypto"]["resolved_path"]).name.startswith("libcrypto.so")
    ):
        raise ReportError(f"{label} OpenSSL dependency class changed")

    tls = _gate_object(
        provenance.get("tls"), runner.PROVIDER_TRANSPORT_TLS_KEYS, f"{label}.tls"
    )
    exact_tls = {
        "protocol": "PROTOCOL_TLS_CLIENT",
        "protocol_value": 16,
        "server_hostname": "chatgpt.com",
        "server_port": 443,
        "certificate_source_mode": runner.PROVIDER_CERTIFICATE_SOURCE_MODE,
        "default_capath_used": False,
        "verify_mode": "CERT_REQUIRED",
        "verify_mode_value": 2,
        "check_hostname": True,
        "minimum_version": "TLSv1_2",
        "minimum_version_value": 771,
        "maximum_version": "MAXIMUM_SUPPORTED",
        "maximum_version_value": -1,
        "alpn_protocols": runner.PROVIDER_TLS_ALPN_PROTOCOLS,
        "keylog_enabled": False,
    }
    if (
        tls.get("default_capath_used") is not False
        or tls.get("check_hostname") is not True
        or tls.get("keylog_enabled") is not False
        or any(
            type(tls.get(field)) is not int
            for field in (
                "protocol_value",
                "server_port",
                "verify_mode_value",
                "minimum_version_value",
                "maximum_version_value",
            )
        )
        or any(tls.get(field) != wanted for field, wanted in exact_tls.items())
    ):
        raise ReportError(f"{label} TLS authentication policy changed")
    ca = _gate_dependency(tls.get("certificate_source"), f"{label}.tls.certificate_source")
    if ca["logical_path"] != runner.PROVIDER_CA_BUNDLE_PATH or ca["symlink_target"] is not None:
        raise ReportError(f"{label} does not use the fixed no-follow CA bundle")
    _gate_positive(tls.get("certificate_authority_count"), f"{label}.tls.certificate_authority_count")
    for field in ("context_options", "verify_flags", "security_level"):
        _gate_nonnegative(tls.get(field), f"{label}.tls.{field}")
    if not _hex_digest(tls.get("cipher_names_sha256")):
        raise ReportError(f"{label} TLS cipher inventory is unauthenticated")

    resolver = _gate_object(
        provenance.get("resolver"), runner.PROVIDER_TRANSPORT_RESOLVER_KEYS, f"{label}.resolver"
    )
    if (
        resolver.get("policy") != runner.PROVIDER_RESOLVER_POLICY
        or resolver.get("hostname") != "chatgpt.com"
        or resolver.get("resolved_addresses_frozen") is not False
        or resolver.get("variability_classification")
        != runner.PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION
    ):
        raise ReportError(f"{label} DNS variability is not classified as availability-only")
    resolver_dependencies = {}
    for field in (
        "resolv_conf",
        "nsswitch_conf",
        "hosts_file",
        "gai_conf",
        "libc",
        "libnss_dns",
        "libnss_files",
    ):
        resolver_dependencies[field] = _gate_dependency(
            resolver[field],
            f"{label}.resolver.{field}",
            authenticated_historical_snapshot=(
                authenticated_historical_hosts_file
                if field == "hosts_file"
                else None
            ),
        )
    expected_paths = {
        "resolv_conf": runner.PROVIDER_RESOLV_CONF_PATH,
        "nsswitch_conf": runner.PROVIDER_NSSWITCH_PATH,
        "hosts_file": runner.PROVIDER_HOSTS_PATH,
        "gai_conf": runner.PROVIDER_GAI_CONF_PATH,
    }
    if any(
        resolver_dependencies[field]["logical_path"] != wanted
        for field, wanted in expected_paths.items()
    ):
        raise ReportError(f"{label} resolver inputs changed identity")
    environment = _gate_object(
        provenance.get("environment"),
        runner.PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
        f"{label}.environment",
    )
    absent = list(runner.PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT)
    if (
        environment.get("required_absent") != absent
        or environment.get("observed_absent") != absent
        or environment.get("proxy_mode") != runner.PROVIDER_PROXY_MODE
    ):
        raise ReportError(f"{label} transport override environment was not sanitized")
    return provenance


def _gate_command_value(command: Any, option: str, label: str) -> str:
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        raise ReportError(f"{label} agent command is malformed")
    positions = [index for index, item in enumerate(command) if item == option]
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        raise ReportError(f"{label} agent command does not contain exactly one {option}")
    return command[positions[0] + 1]


_PROVIDER_SSE_CONTENT_TYPE_RE = re.compile(
    r'\A[ \t]*text/event-stream(?:[ \t]*;[ \t]*charset[ \t]*=[ \t]*'
    r'(?:utf-8|"utf-8"))?[ \t]*\Z',
    re.IGNORECASE,
)


def _gate_validate_upstream_sse_authentication(
    call: Mapping[str, Any], label: str
) -> dict[str, Any]:
    """Independently bind the accepted upstream envelope to its body evidence."""

    content_type_count = call.get("upstream_content_type_occurrences")
    content_encoding_count = call.get("upstream_content_encoding_occurrences")
    if (
        type(content_type_count) is not int
        or content_type_count not in {0, 1}
        or type(content_encoding_count) is not int
        or content_encoding_count not in {0, 1}
    ):
        raise ReportError(f"{label} has ambiguous response header occurrences")

    content_type = call.get("upstream_content_type")
    content_encoding = call.get("upstream_content_encoding")
    if content_type_count == 0:
        if content_type is not None:
            raise ReportError(f"{label} absent Content-Type is not represented exactly")
        content_type_basis = "authenticated_stream_request_header_absent"
        synthesized = True
    else:
        if (
            not isinstance(content_type, str)
            or _PROVIDER_SSE_CONTENT_TYPE_RE.fullmatch(content_type) is None
        ):
            raise ReportError(f"{label} declared Content-Type is not exact SSE")
        content_type_basis = "declared_text_event_stream"
        synthesized = False

    if content_encoding_count == 0:
        if content_encoding is not None:
            raise ReportError(
                f"{label} absent Content-Encoding is not represented exactly"
            )
        content_encoding_basis = "implicit_identity_header_absent"
    else:
        if (
            not isinstance(content_encoding, str)
            or re.fullmatch(
                r"[ \t]*identity[ \t]*", content_encoding, re.IGNORECASE
            )
            is None
        ):
            raise ReportError(f"{label} declared Content-Encoding is not identity")
        content_encoding_basis = "declared_identity"

    authentication = _gate_object(
        call.get("upstream_sse_authentication"),
        runner.PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
        f"{label} strict SSE authentication",
    )
    json_event_count = authentication.get("json_event_count")
    completed_event_index = authentication.get("completed_event_index")
    done_count = authentication.get("done_count")
    if (
        authentication.get("schema_version") != 1
        or type(authentication.get("schema_version")) is not int
        or authentication.get("protocol")
        != "highambench-responses-sse-envelope-v1"
        or authentication.get("parser")
        != "highambench-strict-responses-sse-v2"
        or authentication.get("complete") is not True
        or authentication.get("content_type_basis") != content_type_basis
        or authentication.get("content_encoding_basis") != content_encoding_basis
        or type(json_event_count) is not int
        or json_event_count < 1
        or type(completed_event_index) is not int
        or completed_event_index != json_event_count - 1
        or type(done_count) is not int
        or done_count not in {0, 1}
        or authentication.get("body_sha256")
        != call.get("upstream_body_sha256")
        or authentication.get("body_bytes") != call.get("upstream_body_bytes")
        or type(authentication.get("body_bytes")) is not int
        or authentication.get("response_id") != call.get("response_id")
        or authentication.get("downstream_content_type_synthesized")
        is not synthesized
    ):
        raise ReportError(f"{label} strict SSE authentication is inconsistent")
    return authentication


def _gate_validate_sanitized_call(call: Mapping[str, Any], label: str) -> None:
    event = call.get("released_sanitized_event")
    events = call.get("released_sanitized_events")
    body = call.get("released_sanitized_body_utf8")
    if (
        not isinstance(event, Mapping)
        or not isinstance(events, list)
        or not events
        or any(not isinstance(item, Mapping) for item in events)
        or not isinstance(body, str)
    ):
        raise ReportError(f"{label} crossing lacks its quarantined completion")
    expected = "".join(
        "event: "
        + str(item.get("type"))
        + "\ndata: "
        + json.dumps(dict(item), sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n\n"
        for item in events
    )
    release_kind = call.get("release_kind")
    metadata = call.get("request_metadata")
    request_kind = metadata.get("request_kind") if isinstance(metadata, Mapping) else None
    if release_kind == runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE:
        item_event = events[0] if len(events) == 2 else None
        item = item_event.get("item") if isinstance(item_event, Mapping) else None
        if (
            request_kind != "compaction"
            or not isinstance(item_event, Mapping)
            or set(item_event) != {"type", "item"}
            or item_event.get("type") != "response.output_item.done"
            or not isinstance(item, Mapping)
            or set(item) != {"type", "encrypted_content"}
            or item.get("type") != "compaction"
            or not isinstance(item.get("encrypted_content"), str)
            or not item["encrypted_content"]
        ):
            raise ReportError(f"{label} compaction quarantine is not the exact opaque item")
    elif release_kind == runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE:
        if request_kind == "compaction" or len(events) != 1:
            raise ReportError(f"{label} ordinary crossing has extra sanitized frames")
    else:
        raise ReportError(f"{label} crossing release kind is not frozen")
    response = event.get("response")
    if (
        body != expected
        or hashlib.sha256(body.encode("utf-8")).hexdigest()
        != call.get("released_body_sha256")
        or len(body.encode("utf-8")) != call.get("released_body_bytes")
        or set(event) != {"type", "response"}
        or event.get("type") != "response.completed"
        or dict(events[-1]) != dict(event)
        or not isinstance(response, Mapping)
        or set(response) != {"id", "usage", "end_turn", "output"}
        or response.get("id") != call.get("response_id")
        or response.get("usage") != call.get("usage")
        or response.get("end_turn") is not True
        or response.get("output") != []
    ):
        raise ReportError(f"{label} crossing release is not the exact action-free SSE")
    lowered = body.lower()
    if any(
        marker in lowered
        for marker in (
            "function_call",
            "custom_tool_call",
            "tool_call",
            "shell_call",
            "computer_call",
            '"type":"message"',
            '"type":"output_text"',
        )
    ):
        raise ReportError(f"{label} crossing release retained a tool or message frame")


def _authenticate_provider_gate_record(
    run: Mapping[str, Any],
    *,
    artifact_path: Path | None = None,
    label: str | None = None,
    authenticated_historical_hosts_file: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Independently authenticate one sealed provider-token endpoint.

    This intentionally does not call the runner or canary gate authenticators.
    Their embedded authentication is compared only after this renderer has
    reread the mode-0444 file, replayed admissions and usage, and derived the
    winning endpoint itself.
    """

    run_label = label or str(run.get("run_id") or "Ultra run")
    summary = _gate_object(
        run.get("provider_token_gate"),
        _PROVIDER_GATE_RUN_SUMMARY_FIELDS,
        f"{run_label} provider-gate summary",
    )
    if (
        summary.get("required") is not True
        or summary.get("status") != "final_artifact_authenticated"
        or summary.get("protocol") != runner.PROVIDER_GATE_PROTOCOL
        or summary.get("cleanup_grace_seconds") != 45.0
        or type(summary.get("cleanup_grace_seconds")) is not float
        or summary.get("error") is not None
        or not _hex_digest(summary.get("implementation_source_sha256"))
    ):
        raise ReportError(f"{run_label} has no scoreable sealed provider-gate endpoint")

    implementation_path = Path(runner.__file__).resolve().with_name(
        runner.PROVIDER_GATE_IMPLEMENTATION_NAME
    )
    try:
        implementation_metadata = implementation_path.lstat()
    except OSError as error:
        raise ReportError(
            f"{run_label} provider-gate implementation source is unavailable: {error}"
        ) from error
    if (
        stat.S_ISLNK(implementation_metadata.st_mode)
        or not stat.S_ISREG(implementation_metadata.st_mode)
        or _file_digest(implementation_path)
        != summary.get("implementation_source_sha256")
    ):
        raise ReportError(
            f"{run_label} provider-gate implementation source does not match disk"
        )

    # Launch-time authentication checks the full bundled catalog; final run
    # records intentionally retain only the two content digests and bound.
    # Rebind that exact projection to both argv and the sealed configuration.
    catalog = _gate_object(
        summary.get("model_catalog"),
        _PROVIDER_GATE_MODEL_CATALOG_FIELDS,
        f"{run_label} provider model-catalog projection",
    )
    if (
        not _hex_digest(catalog.get("catalog_sha256"))
        or catalog.get("catalog_sha256")
        != runner.FROZEN_BUNDLED_MODEL_CATALOG_SHA256
        or not _hex_digest(catalog.get("entry_sha256"))
        or catalog.get("entry_sha256")
        != runner.FROZEN_BUNDLED_MODEL_ENTRY_SHA256
        or catalog.get("response_bound") != runner.PROVIDER_RESPONSE_TOKEN_BOUND
        or type(catalog.get("response_bound")) is not int
    ):
        raise ReportError(f"{run_label} provider model-catalog projection changed")

    transport = _gate_transport(
        summary.get("transport_provenance"),
        f"{run_label} prelaunch transport",
        authenticated_historical_hosts_file=authenticated_historical_hosts_file,
    )
    command = run.get("agent_command")
    usage_raw = _gate_command_value(command, "--usage-output", run_label)
    usage_path = Path(usage_raw)
    if not usage_path.is_absolute():
        raise ReportError(f"{run_label} --usage-output is not absolute")
    expected_gate_path = runner.provider_gate_paths(usage_path.resolve())["final"]
    if artifact_path is None:
        artifact_path = expected_gate_path
    artifact_path = artifact_path.resolve()
    if artifact_path != expected_gate_path:
        raise ReportError(f"{run_label} provider-gate artifact is not usage-path-bound")
    expected_options = {
        "--provider-gate-live-output": str(
            runner.provider_gate_paths(usage_path.resolve())["live"]
        ),
        "--provider-gate-output": str(artifact_path),
        "--model-catalog-sha256": str(catalog["catalog_sha256"]),
        "--model-entry-sha256": str(catalog["entry_sha256"]),
        "--provider-response-bound": str(runner.PROVIDER_RESPONSE_TOKEN_BOUND),
    }
    if any(
        _gate_command_value(command, option, run_label) != wanted
        for option, wanted in expected_options.items()
    ):
        raise ReportError(f"{run_label} provider-gate command bindings changed")

    live_summary = _gate_object(
        summary.get("live"),
        {"scoreable", "file", "authenticated_crossing"},
        f"{run_label} live gate summary",
    )
    final_summary = _gate_object(
        summary.get("final"),
        {"scoreable", "file", "authentication"},
        f"{run_label} final gate summary",
    )
    if live_summary.get("scoreable") is not False or final_summary.get("scoreable") is not True:
        raise ReportError(f"{run_label} conflates provisional and sealed gate evidence")
    descriptor = _gate_object(
        final_summary.get("file"),
        _PROVIDER_GATE_FILE_FIELDS,
        f"{run_label} final gate file descriptor",
    )
    record, payload = _gate_read_sealed(artifact_path, f"{run_label} provider gate")
    file_digest = hashlib.sha256(payload).hexdigest()
    if (
        descriptor.get("path") != str(artifact_path)
        or descriptor.get("absolute") is not True
        or descriptor.get("exists") is not True
        or descriptor.get("regular_non_symlink") is not True
        or descriptor.get("mode") != "0444"
        or descriptor.get("size_bytes") != len(payload)
        or type(descriptor.get("size_bytes")) is not int
        or descriptor.get("file_sha256") != file_digest
    ):
        raise ReportError(f"{run_label} final gate descriptor is stale or unsealed")

    authentication = _gate_object(
        final_summary.get("authentication"),
        _PROVIDER_GATE_FINAL_AUTH_FIELDS,
        f"{run_label} final gate authentication",
    )
    if (
        authentication.get("path") != str(artifact_path)
        or authentication.get("file_sha256") != file_digest
        or authentication.get("record_sha256") != record.get("record_sha256")
        or authentication.get("size_bytes") != len(payload)
        or type(authentication.get("size_bytes")) is not int
        or authentication.get("mode") != "0444"
        or authentication.get("authenticated") is not True
        or authentication.get("record") != record
    ):
        raise ReportError(f"{run_label} retained gate authentication does not match disk")

    if (
        record.get("schema_version") != runner.PROVIDER_GATE_SCHEMA_VERSION
        or type(record.get("schema_version")) is not int
        or record.get("protocol") != runner.PROVIDER_GATE_PROTOCOL
        or record.get("canonical_encoding") != runner.PROVIDER_GATE_CANONICAL_ENCODING
        or record.get("sealed_mode") != runner.PROVIDER_GATE_SEALED_MODE
    ):
        raise ReportError(f"{run_label} gate static protocol changed")
    implementation = _gate_object(
        record.get("implementation"),
        runner.PROVIDER_GATE_IMPLEMENTATION_KEYS,
        f"{run_label} gate implementation",
    )
    if (
        implementation.get("name") != runner.PROVIDER_GATE_IMPLEMENTATION_NAME
        or implementation.get("version") != runner.PROVIDER_GATE_IMPLEMENTATION_VERSION
        or implementation.get("source_sha256")
        != summary.get("implementation_source_sha256")
        or not _hex_digest(implementation.get("source_sha256"))
    ):
        raise ReportError(f"{run_label} gate implementation source is unauthenticated")

    configuration = _gate_object(
        record.get("configuration"),
        runner.PROVIDER_GATE_CONFIGURATION_KEYS,
        f"{run_label} gate configuration",
    )
    limits = run.get("limits")
    if not isinstance(limits, Mapping):
        raise ReportError(f"{run_label} resource limits are missing")
    token_limit = _gate_positive(limits.get("model_tokens"), f"{run_label} token limit")
    upstream_contract = _gate_object(
        configuration.get("upstream_response_contract"),
        runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
        f"{run_label} upstream response contract",
    )
    expected_upstream_contract = {
        "schema_version": 1,
        "protocol": "highambench-responses-sse-envelope-v1",
        "success_status": 200,
        "content_type_policy": (
            "absent_or_single_text_event_stream_optional_utf8_charset"
        ),
        "content_encoding_policy": "absent_or_single_identity",
        "outbound_accept": "text/event-stream",
        "parser": "highambench-strict-responses-sse-v2",
        "downstream_content_type": "text/event-stream",
        "downstream_content_encoding": "identity",
    }
    if (
        configuration.get("token_limit") != token_limit
        or type(configuration.get("token_limit")) is not int
        or configuration.get("response_bound") != runner.PROVIDER_RESPONSE_TOKEN_BOUND
        or type(configuration.get("response_bound")) is not int
        or configuration.get("response_bound_enforcement")
        != "runtime_fail_closed_before_buffered_response_release"
        or configuration.get("model_catalog_sha256") != catalog.get("catalog_sha256")
        or configuration.get("model_entry_sha256") != catalog.get("entry_sha256")
        or configuration.get("strict_admission_inequality")
        != "completed_tokens + (open_request_count + 1) * response_bound < token_limit"
        or configuration.get("upstream_origin") != "https://chatgpt.com"
        or configuration.get("upstream_base_path") != "/backend-api/codex"
        or configuration.get("loopback_only") is not True
        or configuration.get("capability_persisted") is not False
        or configuration.get("websockets_supported") is not False
        or configuration.get("request_retries") != 0
        or type(configuration.get("request_retries")) is not int
        or configuration.get("stream_retries") != 0
        or type(configuration.get("stream_retries")) is not int
        or configuration.get("request_compression") is not False
        or configuration.get("response_compression") != "identity"
        or configuration.get("counted_route") != "POST /responses"
        or configuration.get("counted_request_kinds") != ["turn", "compaction"]
        or configuration.get("rejected_inference_routes") != ["POST /responses/compact"]
        or configuration.get("allowed_setup_route_prefixes") != []
        or configuration.get("crossing_release_policy")
        != runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY
        or upstream_contract != expected_upstream_contract
        or configuration.get("transport_provenance") != transport
    ):
        raise ReportError(f"{run_label} gate configuration is not the frozen production contract")

    usage = run.get("token_usage")
    if not isinstance(usage, Mapping):
        raise ReportError(f"{run_label} lacks its exact Ultra usage ledger")
    agent = run.get("agent")
    if not isinstance(agent, Mapping):
        raise ReportError(f"{run_label} frozen agent identity is missing")
    prompt_release = run.get("prompt_release")
    released_descriptor = (
        prompt_release.get("released") if isinstance(prompt_release, Mapping) else None
    )
    released_record = (
        released_descriptor.get("record")
        if isinstance(released_descriptor, Mapping)
        else None
    )
    if not isinstance(released_record, Mapping):
        raise ReportError(f"{run_label} gate is not bound to a RELEASED record")
    release_digest = hashlib.sha256(_gate_canonical_newline(dict(released_record))).hexdigest()
    bindings = _gate_object(
        record.get("bindings"), runner.PROVIDER_GATE_BINDING_KEYS, f"{run_label} gate bindings"
    )
    expected_bindings = {
        "root_thread_id": usage.get("root_thread_id"),
        "prompt_release_sha256": release_digest,
        "prompt_release_protocol": released_record.get("protocol_version"),
        "prompt_sha256": prompt_release.get("effective_prompt_sha256"),
        "run_id": run.get("run_id"),
        "model": agent.get("model"),
        "reasoning_effort": agent.get("reasoning_effort"),
    }
    if (
        bindings != expected_bindings
        or any(not isinstance(value, str) or not value for value in bindings.values())
        or bindings.get("model") != "gpt-5.6-sol"
        or bindings.get("reasoning_effort") != "ultra"
    ):
        raise ReportError(f"{run_label} gate run/prompt/model bindings disagree")

    lifecycle = _gate_object(
        record.get("lifecycle"), runner.PROVIDER_GATE_LIFECYCLE_KEYS, f"{run_label} lifecycle"
    )
    for clock in ("unix", "monotonic"):
        values = [
            _gate_positive(lifecycle.get(f"{phase}_{clock}_ns"), f"{run_label} {phase} {clock}")
            for phase in ("started", "stopped", "finalized")
        ]
        if values != sorted(values):
            raise ReportError(f"{run_label} gate lifecycle clocks regress")

    state = _gate_object(
        record.get("state"), runner.PROVIDER_GATE_STATE_KEYS, f"{run_label} gate state"
    )
    if (
        state.get("phase") != "CLOSED"
        or state.get("poisoned") is not False
        or state.get("poison_reasons") != []
        or state.get("open_request_ids") != []
        or state.get("all_complete") is not True
        or state.get("no_post_close_upstream") is not True
        or state.get("active_handler_count") != 0
        or type(state.get("active_handler_count")) is not int
        or state.get("handlers_quiescent") is not True
        or state.get("close_reason") not in {"token_limit", "accepted_submission", "natural_end"}
    ):
        raise ReportError(f"{run_label} provider requests are not cleanly quiescent")

    raw_calls = record.get("calls")
    if not isinstance(raw_calls, list) or not raw_calls:
        raise ReportError(f"{run_label} provider call ledger is empty or malformed")
    calls: list[dict[str, Any]] = []
    call_ids: set[str] = set()
    response_ids: set[str] = set()
    event_sequences: set[int] = set()
    exact_wait_responses: dict[str, bool] = {}
    global_sequences: set[int] = set()
    global_events: list[tuple[int, int]] = []
    for index, raw_call in enumerate(raw_calls):
        call = _gate_object(
            raw_call, runner.PROVIDER_GATE_CALL_KEYS, f"{run_label} calls[{index}]"
        )
        sequence = _gate_positive(call.get("sequence"), f"{run_label} call sequence")
        call_id = _gate_string(call.get("call_id"), f"{run_label} call ID")
        response_id = _gate_string(call.get("response_id"), f"{run_label} response ID")
        assert isinstance(call_id, str) and isinstance(response_id, str)
        if (
            sequence in global_sequences
            or call_id != f"provider-call-{sequence:08d}"
            or call_id in call_ids
            or response_id in response_ids
            or call.get("method") != "POST"
            or call.get("route") != "/responses"
            or call.get("request_model") != "gpt-5.6-sol"
            or call.get("request_stream") is not True
            or not _hex_digest(call.get("request_body_sha256"))
            or _gate_positive(call.get("request_bytes"), f"{run_label} request bytes") <= 0
            or call.get("admission_mode") not in {"CONCURRENT", "EXCLUSIVE"}
            or call.get("response_bound") != runner.PROVIDER_RESPONSE_TOKEN_BOUND
            or type(call.get("response_bound")) is not int
            or call.get("upstream_started") is not True
            or call.get("upstream_status") != 200
            or type(call.get("upstream_status")) is not int
            or not _hex_digest(call.get("upstream_body_sha256"))
            or _gate_positive(call.get("upstream_body_bytes"), f"{run_label} upstream bytes") <= 0
            or not _hex_digest(call.get("released_body_sha256"))
            or _gate_positive(call.get("released_body_bytes"), f"{run_label} released bytes") <= 0
            or call.get("error") is not None
        ):
            raise ReportError(f"{run_label} provider call {index} is malformed")
        _gate_validate_upstream_sse_authentication(
            call, f"{run_label} provider call {index}"
        )
        metadata = _gate_object(
            call.get("request_metadata"),
            runner.PROVIDER_GATE_REQUEST_METADATA_KEYS,
            f"{run_label} call metadata",
        )
        for field in runner.PROVIDER_GATE_REQUEST_METADATA_KEYS:
            _gate_string(metadata[field], f"{run_label} metadata.{field}")
        if metadata.get("request_kind") not in {"turn", "compaction"}:
            raise ReportError(f"{run_label} provider call has an uncounted request kind")
        credentials = call.get("credential_headers_present")
        if (
            not isinstance(credentials, list)
            or credentials != sorted(set(credentials))
            or "authorization" not in credentials
            or any(not isinstance(item, str) or re.fullmatch(r"[a-z0-9-]+", item) is None for item in credentials)
        ):
            raise ReportError(f"{run_label} credential-header names are malformed")
        normalized = _gate_usage(call.get("normalized_usage"), f"{run_label} normalized usage")
        if (
            _gate_normalize_provider_usage(call.get("usage"), f"{run_label} provider usage")
            != normalized
            or normalized["total_tokens"] > runner.PROVIDER_RESPONSE_TOKEN_BOUND
        ):
            raise ReportError(f"{run_label} provider usage normalization changed")
        admitted_mono = _gate_positive(call.get("admitted_monotonic_ns"), f"{run_label} admitted time")
        admitted_unix = _gate_positive(call.get("admitted_unix_ns"), f"{run_label} admitted wall time")
        upstream_mono = _gate_positive(call.get("upstream_start_monotonic_ns"), f"{run_label} upstream time")
        upstream_unix = _gate_positive(call.get("upstream_start_unix_ns"), f"{run_label} upstream wall time")
        commit_mono = _gate_positive(call.get("commit_monotonic_ns"), f"{run_label} commit time")
        commit_unix = _gate_positive(call.get("commit_unix_ns"), f"{run_label} commit wall time")
        if (
            not admitted_mono <= upstream_mono <= commit_mono
            or not admitted_unix <= upstream_unix <= commit_unix
            or admitted_mono < lifecycle["started_monotonic_ns"]
            or commit_mono > lifecycle["stopped_monotonic_ns"]
        ):
            raise ReportError(f"{run_label} provider call timestamps regress")
        exact_wait = _gate_validate_response_output_manifest(
            call.get("response_output_manifest"), response_id, f"{run_label} call {index}"
        )
        delivery = _gate_object(
            call.get("appserver_delivery"),
            provider_token_gate.PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
            f"{run_label} app-server delivery",
        )
        delivery_kind = delivery.get("kind")
        delivery_mono = _gate_positive(
            delivery.get("bind_monotonic_ns"), f"{run_label} delivery time"
        )
        delivery_unix = _gate_positive(
            delivery.get("bind_unix_ns"), f"{run_label} delivery wall time"
        )
        if delivery_mono < commit_mono or delivery_unix < commit_unix:
            raise ReportError(f"{run_label} app-server delivery predates its response")
        crossbind: dict[str, Any] | None
        event_sequence: int | None = None
        if delivery_kind == provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT:
            crossbind = _gate_object(
                call.get("appserver_crossbind"),
                runner.PROVIDER_GATE_CROSSBIND_KEYS,
                f"{run_label} app-server crossbind",
            )
            event_sequence = _gate_positive(
                crossbind.get("event_sequence"), f"{run_label} app-server sequence"
            )
            if (
                event_sequence in event_sequences
                or call.get("client_release_complete") is not True
                or crossbind.get("thread_id") != metadata.get("thread_id")
                or crossbind.get("turn_id") != metadata.get("turn_id")
                or _gate_usage(
                    crossbind.get("normalized_usage"),
                    f"{run_label} crossbind usage",
                )
                != normalized
                or _gate_positive(
                    crossbind.get("bind_monotonic_ns"), f"{run_label} bind time"
                )
                < commit_mono
                or _gate_positive(
                    crossbind.get("bind_unix_ns"), f"{run_label} bind wall time"
                )
                < commit_unix
                or delivery.get("successor_call_id") is not None
                or delivery.get("successor_response_id") is not None
                or delivery_mono != crossbind.get("bind_monotonic_ns")
                or delivery_unix != crossbind.get("bind_unix_ns")
            ):
                raise ReportError(f"{run_label} direct app-server delivery changed")
        elif (
            delivery_kind
            == provider_token_gate.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT
        ):
            crossbind = None
            if (
                call.get("appserver_crossbind") is not None
                or call.get("client_release_complete") is not True
                or not exact_wait
                or metadata.get("request_kind") != "turn"
                or call.get("crossed_cap") is not False
                or call.get("release_kind") != "byte_identity"
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery.get("successor_call_id")
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery.get("successor_response_id")
            ):
                raise ReportError(
                    f"{run_label} suppressed collaboration wait is not exact"
                )
        elif (
            delivery_kind
            == provider_token_gate.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
        ):
            crossbind = None
            if (
                call.get("client_release_complete") is not True
                or not _gate_superseded_delivery_is_exact(call, metadata, delivery)
            ):
                raise ReportError(
                    f"{run_label} superseded collaboration response is not exact"
                )
        elif (
            delivery_kind
            == provider_token_gate.PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
        ):
            crossbind = None
            if (
                call.get("appserver_crossbind") is not None
                or call.get("client_release_complete") is not False
                or metadata.get("request_kind") != "turn"
                or call.get("crossed_cap") is not False
                or call.get("release_kind") != "byte_identity"
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery.get("successor_call_id")
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery.get("successor_response_id")
            ):
                raise ReportError(
                    f"{run_label} explicit-child-interrupt discard is not exact"
                )
        else:
            raise ReportError(f"{run_label} app-server delivery kind changed")
        if call.get("release_kind") == "byte_identity":
            if (
                call.get("released_body_sha256") != call.get("upstream_body_sha256")
                or call.get("released_body_bytes") != call.get("upstream_body_bytes")
                or call.get("released_sanitized_event") is not None
                or call.get("released_sanitized_events") is not None
                or call.get("released_sanitized_body_utf8") is not None
            ):
                raise ReportError(f"{run_label} non-crossing response was not byte-identical")
        elif call.get("release_kind") in {
            runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
            runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
        }:
            _gate_validate_sanitized_call(call, f"{run_label} crossing call")
        else:
            raise ReportError(f"{run_label} provider response release kind is unknown")
        call["request_metadata"] = metadata
        call["normalized_usage"] = normalized
        call["appserver_crossbind"] = (
            {**crossbind, "normalized_usage": normalized}
            if crossbind is not None
            else None
        )
        call["appserver_delivery"] = delivery
        calls.append(call)
        call_ids.add(call_id)
        response_ids.add(response_id)
        exact_wait_responses[response_id] = exact_wait
        if event_sequence is not None:
            event_sequences.add(event_sequence)
        global_sequences.add(sequence)
        global_events.append((sequence, admitted_mono))

    if len({call["admitted_monotonic_ns"] for call in calls}) != len(calls) or len(
        {call["commit_monotonic_ns"] for call in calls}
    ) != len(calls):
        raise ReportError(f"{run_label} provider admission/commit order is ambiguous")
    direct_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
    ]
    suppressed_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT
    ]
    superseded_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
    ]
    discarded_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
    ]
    if event_sequences != set(range(1, len(direct_calls) + 1)):
        raise ReportError(f"{run_label} app-server response-event ledger has a gap")
    if {call["admitted_monotonic_ns"] for call in calls} & {
        call["commit_monotonic_ns"] for call in calls
    }:
        raise ReportError(f"{run_label} provider admission equals a commit timestamp")

    commit_order = sorted(calls, key=lambda item: item["commit_monotonic_ns"])
    running_total = 0
    derived_crossing: dict[str, Any] | None = None
    reported_crossing = state.get("crossing")
    if reported_crossing is not None:
        reported_crossing = _gate_object(
            reported_crossing,
            runner.PROVIDER_GATE_CROSSING_KEYS,
            f"{run_label} crossing",
        )
        crossing_sequence = _gate_positive(
            reported_crossing.get("sequence"), f"{run_label} crossing sequence"
        )
        for field in (
            "previous_total",
            "response_tokens",
            "completed_tokens",
            "overshoot_tokens",
        ):
            _gate_nonnegative(
                reported_crossing.get(field), f"{run_label} crossing {field}"
            )
        _gate_string(reported_crossing.get("call_id"), f"{run_label} crossing call ID")
        _gate_string(
            reported_crossing.get("response_id"), f"{run_label} crossing response ID"
        )
        if (
            reported_crossing.get("sole_inflight") is not True
            or reported_crossing.get("request_kind") not in {"turn", "compaction"}
            or reported_crossing.get("release_kind")
            != {
                "turn": runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
                "compaction": runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            }.get(reported_crossing.get("request_kind"))
        ):
            raise ReportError(f"{run_label} crossing kind/sanitizer binding changed")
        if crossing_sequence in global_sequences:
            raise ReportError(f"{run_label} crossing sequence is reused")
        global_sequences.add(crossing_sequence)
        global_events.append(
            (
                crossing_sequence,
                _gate_positive(
                    reported_crossing.get("commit_monotonic_ns"),
                    f"{run_label} crossing commit",
                ),
            )
        )
    for call in commit_order:
        previous = running_total
        running_total += call["normalized_usage"]["total_tokens"]
        crossed = previous < token_limit <= running_total
        if (
            call.get("previous_total") != previous
            or type(call.get("previous_total")) is not int
            or call.get("committed_total") != running_total
            or type(call.get("committed_total")) is not int
            or call.get("crossed_cap") is not crossed
        ):
            raise ReportError(f"{run_label} committed provider total is not reproducible")
        if crossed:
            if derived_crossing is not None or not isinstance(reported_crossing, Mapping):
                raise ReportError(f"{run_label} does not have one unique first crossing")
            open_at_crossing = [
                candidate
                for candidate in calls
                if candidate["admitted_monotonic_ns"] <= call["commit_monotonic_ns"]
                and candidate["commit_monotonic_ns"] >= call["commit_monotonic_ns"]
            ]
            if (
                [candidate["call_id"] for candidate in open_at_crossing]
                != [call["call_id"]]
                or call.get("release_kind")
                not in {
                    runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
                    runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
                }
            ):
                raise ReportError(f"{run_label} cap crossing was not sole and quarantined")
            derived_crossing = {
                "call_id": call["call_id"],
                "response_id": call["response_id"],
                "sequence": reported_crossing["sequence"],
                "previous_total": previous,
                "response_tokens": call["normalized_usage"]["total_tokens"],
                "completed_tokens": running_total,
                "overshoot_tokens": running_total - token_limit,
                "commit_unix_ns": call["commit_unix_ns"],
                "commit_monotonic_ns": call["commit_monotonic_ns"],
                "sole_inflight": True,
                "release_kind": call["release_kind"],
                "request_kind": call["request_metadata"]["request_kind"],
            }
        elif call.get("release_kind") != "byte_identity":
            raise ReportError(f"{run_label} sanitized a response below the cap")
    if reported_crossing != derived_crossing:
        raise ReportError(f"{run_label} first crossing cannot be independently replayed")
    if derived_crossing is not None and (
        commit_order[-1]["call_id"] != derived_crossing["call_id"]
        or running_total != derived_crossing["completed_tokens"]
    ):
        raise ReportError(f"{run_label} released provider work after the cap crossing")

    calls_by_response = {call["response_id"]: call for call in calls}
    for suppressed in suppressed_calls:
        delivery = suppressed["appserver_delivery"]
        successor = calls_by_response.get(delivery["successor_response_id"])
        eligible = [
            candidate
            for candidate in direct_calls
            if candidate["commit_monotonic_ns"]
            > suppressed["commit_monotonic_ns"]
            and candidate["admitted_monotonic_ns"]
            > suppressed["commit_monotonic_ns"]
            and candidate["request_metadata"]["thread_id"]
            == suppressed["request_metadata"]["thread_id"]
            and candidate["request_metadata"]["turn_id"]
            == suppressed["request_metadata"]["turn_id"]
            and candidate["request_metadata"]["request_kind"] == "turn"
        ]
        earliest = (
            min(
                eligible,
                key=lambda candidate: (
                    candidate["commit_monotonic_ns"], candidate["sequence"]
                ),
            )
            if eligible
            else None
        )
        successor_delivery = (
            successor.get("appserver_delivery")
            if isinstance(successor, Mapping)
            else None
        )
        if (
            successor is None
            or successor.get("call_id") != delivery.get("successor_call_id")
            or earliest is None
            or earliest.get("response_id") != successor.get("response_id")
            or not isinstance(successor_delivery, Mapping)
            or successor_delivery.get("kind")
            != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
            or delivery["bind_monotonic_ns"]
            < successor_delivery.get("bind_monotonic_ns", 0)
            or delivery["bind_unix_ns"] < successor_delivery.get("bind_unix_ns", 0)
        ):
            raise ReportError(
                f"{run_label} suppressed collaboration wait successor changed"
            )
    for superseded in superseded_calls:
        delivery = superseded["appserver_delivery"]
        successor = calls_by_response.get(delivery["successor_response_id"])
        eligible = [
            candidate
            for candidate in calls
            if candidate is not superseded
            and candidate["admitted_monotonic_ns"]
            > superseded["commit_monotonic_ns"]
            and candidate["request_metadata"] == superseded["request_metadata"]
            and candidate["request_metadata"]["request_kind"] == "turn"
        ]
        earliest = (
            min(
                eligible,
                key=lambda candidate: (
                    candidate["admitted_monotonic_ns"], candidate["sequence"]
                ),
            )
            if eligible
            else None
        )
        successor_delivery = (
            successor.get("appserver_delivery")
            if isinstance(successor, Mapping)
            else None
        )
        if (
            successor is None
            or successor.get("call_id") != delivery.get("successor_call_id")
            or earliest is not successor
            or not isinstance(successor_delivery, Mapping)
            or successor_delivery.get("kind")
            not in {
                provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT,
                provider_token_gate.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
                provider_token_gate.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
            }
            or successor["admitted_unix_ns"] <= superseded["commit_unix_ns"]
        ):
            raise ReportError(
                f"{run_label} superseded collaboration response successor changed"
            )
    for origin in superseded_calls:
        cursor = origin
        seen_chain: set[str] = set()
        while cursor["appserver_delivery"]["kind"] in {
            provider_token_gate.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
            provider_token_gate.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
        }:
            if cursor["response_id"] in seen_chain:
                raise ReportError(
                    f"{run_label} superseded collaboration response chain is cyclic"
                )
            seen_chain.add(cursor["response_id"])
            cursor = calls_by_response[
                cursor["appserver_delivery"]["successor_response_id"]
            ]
        if (
            cursor["appserver_delivery"]["kind"]
            != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
        ):
            raise ReportError(
                f"{run_label} superseded collaboration response chain has no direct end"
            )
    if (
        commit_order[-1]["appserver_delivery"]["kind"]
        != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
        or (
            derived_crossing is not None
            and calls_by_response[derived_crossing["response_id"]][
                "appserver_delivery"
            ]["kind"]
            != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
        )
    ):
        raise ReportError(f"{run_label} terminal provider response was not directly delivered")

    for call in calls:
        open_before = [
            candidate
            for candidate in calls
            if candidate["call_id"] != call["call_id"]
            and candidate["admitted_monotonic_ns"] < call["admitted_monotonic_ns"]
            < candidate["commit_monotonic_ns"]
        ]
        completed = sum(
            candidate["normalized_usage"]["total_tokens"]
            for candidate in calls
            if candidate["commit_monotonic_ns"] < call["admitted_monotonic_ns"]
        )
        bound = runner.PROVIDER_RESPONSE_TOKEN_BOUND
        if (
            call.get("completed_before") != completed
            or type(call.get("completed_before")) is not int
            or call.get("open_before") != len(open_before)
            or type(call.get("open_before")) is not int
            or call.get("reserved_before") != completed + len(open_before) * bound
            or type(call.get("reserved_before")) is not int
            or call.get("reservation_after") != completed + (len(open_before) + 1) * bound
            or type(call.get("reservation_after")) is not int
            or (
                call.get("admission_mode") == "CONCURRENT"
                and not completed + (len(open_before) + 1) * bound < token_limit
            )
            or (call.get("admission_mode") == "EXCLUSIVE" and bool(open_before))
        ):
            raise ReportError(f"{run_label} reservation/drain/exclusive replay failed")

    transitions_raw = record.get("transitions")
    if not isinstance(transitions_raw, list) or not transitions_raw:
        raise ReportError(f"{run_label} gate transition ledger is absent")
    transitions: list[dict[str, Any]] = []
    prior_phase: str | None = None
    prior_mono = 0
    for index, raw_transition in enumerate(transitions_raw):
        transition = _gate_object(
            raw_transition,
            runner.PROVIDER_GATE_TRANSITION_KEYS,
            f"{run_label} transitions[{index}]",
        )
        sequence = _gate_positive(transition.get("sequence"), f"{run_label} transition sequence")
        mono = _gate_positive(transition.get("monotonic_ns"), f"{run_label} transition time")
        _gate_positive(transition.get("unix_ns"), f"{run_label} transition wall time")
        if (
            sequence in global_sequences
            or transition.get("from_phase") not in runner.PROVIDER_GATE_PHASES
            or transition.get("to_phase") not in runner.PROVIDER_GATE_PHASES
            or transition.get("from_phase") == transition.get("to_phase")
            or (index == 0 and transition.get("from_phase") != "CONCURRENT")
            or (prior_phase is not None and transition.get("from_phase") != prior_phase)
            or mono < prior_mono
            or (
                transition.get("call_id") is not None
                and transition.get("call_id") not in call_ids
            )
        ):
            raise ReportError(f"{run_label} gate transition chain is inconsistent")
        _gate_string(transition.get("reason"), f"{run_label} transition reason")
        transitions.append(transition)
        global_sequences.add(sequence)
        global_events.append((sequence, mono))
        prior_phase = str(transition["to_phase"])
        prior_mono = mono
    terminal = [
        transition
        for transition in transitions
        if transition.get("to_phase") in {"CLOSED", "POISONED"}
    ]
    if len(terminal) != 1 or terminal[0] != transitions[-1] or prior_phase != "CLOSED":
        raise ReportError(f"{run_label} gate terminal transition is not unique and final")
    terminal_mono = terminal[0]["monotonic_ns"]
    if any(call["upstream_start_monotonic_ns"] >= terminal_mono for call in calls):
        raise ReportError(f"{run_label} provider call began at or after gate close")

    denials_raw = record.get("denials")
    if not isinstance(denials_raw, list):
        raise ReportError(f"{run_label} gate denial ledger is malformed")
    denial_ids: set[str] = set()
    for index, raw_denial in enumerate(denials_raw):
        denial = _gate_object(
            raw_denial, runner.PROVIDER_GATE_DENIAL_KEYS, f"{run_label} denials[{index}]"
        )
        sequence = _gate_positive(denial.get("sequence"), f"{run_label} denial sequence")
        denial_id = _gate_string(denial.get("denial_id"), f"{run_label} denial ID")
        assert isinstance(denial_id, str)
        mono = _gate_positive(denial.get("monotonic_ns"), f"{run_label} denial time")
        if (
            sequence in global_sequences
            or denial_id != f"deny-{sequence:08d}"
            or denial_id in denial_ids
            or denial.get("phase") not in runner.PROVIDER_GATE_PHASES
            or denial.get("upstream_started") is not False
        ):
            raise ReportError(f"{run_label} denied request could have reached upstream")
        _gate_string(denial.get("method"), f"{run_label} denial method")
        _gate_string(denial.get("route"), f"{run_label} denial route")
        _gate_string(denial.get("reason"), f"{run_label} denial reason")
        _gate_positive(denial.get("unix_ns"), f"{run_label} denial wall time")
        _gate_object(
            denial.get("request_metadata"),
            runner.PROVIDER_GATE_REQUEST_METADATA_KEYS,
            f"{run_label} denial metadata",
        )
        global_sequences.add(sequence)
        global_events.append((sequence, mono))
        denial_ids.add(denial_id)

    if record.get("setup_requests") != []:
        raise ReportError(f"{run_label} gate forwarded setup or unknown routes")
    if global_sequences != set(range(1, max(global_sequences) + 1)):
        raise ReportError(f"{run_label} gate global event sequence has a gap")
    ordered_events = sorted(global_events)
    if any(later[1] < earlier[1] for earlier, later in zip(ordered_events, ordered_events[1:])):
        raise ReportError(f"{run_label} gate sequence contradicts monotonic time")
    if state.get("sequence") != max(global_sequences) or type(state.get("sequence")) is not int:
        raise ReportError(f"{run_label} final gate sequence is stale")
    if state.get("completed_tokens") != running_total or type(state.get("completed_tokens")) is not int:
        raise ReportError(f"{run_label} final provider total is stale")
    if state.get("crossing_closed") is not (derived_crossing is not None):
        raise ReportError(f"{run_label} crossing-close flag is inconsistent")
    invariants = record.get("invariants")
    if (
        not isinstance(invariants, Mapping)
        or set(invariants) != set(runner.PROVIDER_GATE_INVARIANT_KEYS)
        or any(value is not True for value in invariants.values())
    ):
        raise ReportError(f"{run_label} gate invariant attestations are incomplete")

    response_ledger = usage.get("appserver_response_ledger")
    provider_ids = [call["response_id"] for call in commit_order]
    ordered_direct_calls = sorted(
        direct_calls, key=lambda item: item["appserver_crossbind"]["event_sequence"]
    )
    appserver_ids = [call["response_id"] for call in ordered_direct_calls]
    suppressed_ids = [
        call["response_id"]
        for call in commit_order
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT
    ]
    superseded_ids = [
        call["response_id"]
        for call in commit_order
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
    ]
    discarded_ids = [
        call["response_id"]
        for call in commit_order
        if call["appserver_delivery"]["kind"]
        == provider_token_gate.PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
    ]
    provider_totals = _gate_usage_sum(calls)
    appserver_totals = _gate_usage_sum(direct_calls)
    suppressed_totals = _gate_usage_sum(suppressed_calls)
    superseded_totals = _gate_usage_sum(superseded_calls)
    discarded_totals = _gate_usage_sum(discarded_calls)
    retained_provider_totals = _gate_usage(
        usage.get("provider_usage"), f"{run_label} retained provider usage"
    )
    retained_appserver_totals = _gate_usage(
        usage.get("appserver_usage"), f"{run_label} retained app-server usage"
    )
    retained_suppressed_totals = _gate_usage(
        usage.get("suppressed_collaboration_wait_usage"),
        f"{run_label} retained suppressed-wait usage",
    )
    retained_superseded_totals = _gate_usage(
        usage.get("superseded_by_collaboration_message_usage"),
        f"{run_label} retained superseded-message usage",
    )
    retained_discarded_totals = _gate_usage(
        usage.get("discarded_after_explicit_child_interrupt_usage"),
        f"{run_label} retained explicit-child-interrupt discard usage",
    )
    if (
        not isinstance(response_ledger, list)
        or len(response_ledger) != len(direct_calls)
        or usage.get("response_count") != len(calls)
        or type(usage.get("response_count")) is not int
        or usage.get("call_count") != len(calls)
        or type(usage.get("call_count")) is not int
        or usage.get("provider_response_count") != len(calls)
        or type(usage.get("provider_response_count")) is not int
        or usage.get("appserver_response_count") != len(direct_calls)
        or type(usage.get("appserver_response_count")) is not int
        or usage.get("suppressed_collaboration_wait_response_count")
        != len(suppressed_calls)
        or type(usage.get("suppressed_collaboration_wait_response_count")) is not int
        or usage.get("superseded_by_collaboration_message_response_count")
        != len(superseded_calls)
        or type(
            usage.get("superseded_by_collaboration_message_response_count")
        )
        is not int
        or usage.get("discarded_after_explicit_child_interrupt_response_count")
        != len(discarded_calls)
        or type(
            usage.get("discarded_after_explicit_child_interrupt_response_count")
        )
        is not int
        or usage.get("notification_sequence") != len(direct_calls)
        or type(usage.get("notification_sequence")) is not int
        or usage.get("interrupt_requested") is not False
        or usage.get("pending_interrupt_response_count") != 0
        or type(usage.get("pending_interrupt_response_count")) is not int
        or usage.get("invalid_reasons") != []
        or usage.get("measurement_exact") is not True
    ):
        raise ReportError(f"{run_label} app-server response ledger is inexact or interrupted")
    ledger_ids: list[str] = []
    ledger_id_set: set[str] = set()
    ledger_sequences: set[int] = set()
    structural_totals = {field: 0 for field in ACCOUNTING_TOKEN_FIELDS}
    for index, raw_response in enumerate(response_ledger):
        response = _gate_object(
            raw_response, runner.ULTRA_RESPONSE_LEDGER_KEYS, f"{run_label} response_ledger[{index}]"
        )
        response_id = response.get("response_id")
        call = calls_by_response.get(response_id)
        if call is None or response_id in ledger_id_set:
            raise ReportError(f"{run_label} response ledger cites a duplicate/unknown response")
        crossbind = call["appserver_crossbind"]
        delivery = call["appserver_delivery"]
        sequence = _gate_positive(
            response.get("raw_response_notification_sequence"),
            f"{run_label} rawResponse sequence",
        )
        observed_mono = _gate_positive(
            response.get("raw_response_observed_at_monotonic_ns"),
            f"{run_label} rawResponse time",
        )
        observed_unix = _gate_positive(
            response.get("raw_response_observed_at_unix_ns"),
            f"{run_label} rawResponse wall time",
        )
        normalized = _gate_usage(response.get("usage"), f"{run_label} ledger usage")
        if (
            sequence != index + 1
            or sequence in ledger_sequences
            or not isinstance(crossbind, Mapping)
            or delivery.get("kind")
            != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
            or response.get("thread_id") != crossbind.get("thread_id")
            or response.get("turn_id") != crossbind.get("turn_id")
            or sequence != crossbind.get("event_sequence")
            or normalized != call["normalized_usage"]
            or response.get("provider_gate_call") != call
            or observed_mono < crossbind.get("bind_monotonic_ns", 0)
            or observed_unix < crossbind.get("bind_unix_ns", 0)
        ):
            raise ReportError(
                f"{run_label} app-server response/gate delivery binding changed"
            )
        for field in ACCOUNTING_TOKEN_FIELDS:
            structural_totals[field] += normalized[field]
        ledger_ids.append(str(response_id))
        ledger_id_set.add(str(response_id))
        ledger_sequences.add(sequence)
    if (
        ledger_id_set != set(appserver_ids)
        or ledger_sequences != set(range(1, len(direct_calls) + 1))
        or ledger_ids != appserver_ids
        or structural_totals != appserver_totals
        or usage.get("response_ids") != provider_ids
        or usage.get("provider_response_ids") != provider_ids
        or usage.get("appserver_response_ids") != appserver_ids
        or usage.get("suppressed_collaboration_wait_response_ids")
        != suppressed_ids
        or usage.get("superseded_by_collaboration_message_response_ids")
        != superseded_ids
        or usage.get("discarded_after_explicit_child_interrupt_response_ids")
        != discarded_ids
        or retained_provider_totals != provider_totals
        or retained_appserver_totals != appserver_totals
        or retained_suppressed_totals != suppressed_totals
        or retained_superseded_totals != superseded_totals
        or retained_discarded_totals != discarded_totals
        or any(
            usage.get("model_tokens" if field == "total_tokens" else field) != total
            or type(
                usage.get("model_tokens" if field == "total_tokens" else field)
            )
            is not int
            for field, total in provider_totals.items()
        )
    ):
        raise ReportError(
            f"{run_label} provider total or app-server structural ledger disagrees"
        )

    reconciliation = _gate_object(
        usage.get("provider_usage_reconciliation"),
        codex_isolated.PROVIDER_USAGE_RECONCILIATION_KEYS,
        f"{run_label} provider usage reconciliation",
    )
    evidence_raw = reconciliation.get("suppressed_collaboration_wait_evidence")
    reconciled_provider_totals = _gate_usage(
        reconciliation.get("provider_usage"),
        f"{run_label} reconciled provider usage",
    )
    reconciled_appserver_totals = _gate_usage(
        reconciliation.get("appserver_usage"),
        f"{run_label} reconciled app-server usage",
    )
    reconciled_suppressed_totals = _gate_usage(
        reconciliation.get("suppressed_collaboration_wait_usage"),
        f"{run_label} reconciled suppressed-wait usage",
    )
    reconciled_superseded_totals = _gate_usage(
        reconciliation.get("superseded_by_collaboration_message_usage"),
        f"{run_label} reconciled superseded-message usage",
    )
    reconciled_discarded_totals = _gate_usage(
        reconciliation.get("discarded_after_explicit_child_interrupt_usage"),
        f"{run_label} reconciled explicit-child-interrupt discard usage",
    )
    discarded_evidence_raw = reconciliation.get(
        "discarded_after_explicit_child_interrupt_evidence"
    )
    if (
        reconciliation.get("schema_version")
        != codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
        or type(reconciliation.get("schema_version")) is not int
        or any(
            type(reconciliation.get(field)) is not int
            for field in (
                "provider_response_count",
                "appserver_response_count",
                "suppressed_collaboration_wait_response_count",
                "superseded_by_collaboration_message_response_count",
                "discarded_after_explicit_child_interrupt_response_count",
            )
        )
        or reconciliation.get("provider_response_count") != len(calls)
        or reconciliation.get("appserver_response_count") != len(direct_calls)
        or reconciliation.get("suppressed_collaboration_wait_response_count")
        != len(suppressed_calls)
        or reconciliation.get(
            "superseded_by_collaboration_message_response_count"
        )
        != len(superseded_calls)
        or reconciliation.get(
            "discarded_after_explicit_child_interrupt_response_count"
        )
        != len(discarded_calls)
        or reconciled_provider_totals != provider_totals
        or reconciled_appserver_totals != appserver_totals
        or reconciled_suppressed_totals != suppressed_totals
        or reconciled_superseded_totals != superseded_totals
        or reconciled_discarded_totals != discarded_totals
        or reconciliation.get("provider_response_ids") != provider_ids
        or reconciliation.get("appserver_response_ids") != appserver_ids
        or reconciliation.get("suppressed_collaboration_wait_response_ids")
        != suppressed_ids
        or reconciliation.get(
            "superseded_by_collaboration_message_response_ids"
        )
        != superseded_ids
        or reconciliation.get(
            "discarded_after_explicit_child_interrupt_response_ids"
        )
        != discarded_ids
        or not isinstance(evidence_raw, list)
        or len(evidence_raw) != len(suppressed_calls)
        or not isinstance(discarded_evidence_raw, list)
        or len(discarded_evidence_raw) != len(discarded_calls)
        or any(
            reconciled_provider_totals[field]
            != reconciled_appserver_totals[field]
            + reconciled_suppressed_totals[field]
            + reconciled_superseded_totals[field]
            + reconciled_discarded_totals[field]
            for field in ACCOUNTING_TOKEN_FIELDS
        )
    ):
        raise ReportError(f"{run_label} provider usage reconciliation changed")
    evidence_message_ids: set[str] = set()
    for index, raw_evidence in enumerate(evidence_raw):
        evidence = _gate_object(
            raw_evidence,
            codex_isolated.SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS,
            f"{run_label} suppressed-wait evidence {index}",
        )
        suppressed = calls_by_response.get(suppressed_ids[index])
        successor = (
            calls_by_response.get(
                suppressed["appserver_delivery"]["successor_response_id"]
            )
            if isinstance(suppressed, Mapping)
            else None
        )
        string_fields = (
            "response_id",
            "provider_call_id",
            "thread_id",
            "turn_id",
            "successor_response_id",
            "successor_call_id",
            "agent_message_item_id",
            "agent_message_sha256",
            "agent_message_author",
            "agent_message_recipient",
        )
        if any(
            not isinstance(evidence.get(field), str) or not evidence.get(field)
            for field in string_fields
        ):
            raise ReportError(f"{run_label} suppressed-wait child result is malformed")
        message_id = str(evidence["agent_message_item_id"])
        message_mono = _gate_positive(
            evidence.get("agent_message_observed_at_monotonic_ns"),
            f"{run_label} child-result time",
        )
        message_unix = _gate_positive(
            evidence.get("agent_message_observed_at_unix_ns"),
            f"{run_label} child-result wall time",
        )
        if (
            suppressed is None
            or successor is None
            or evidence.get("response_id") != suppressed.get("response_id")
            or evidence.get("provider_call_id") != suppressed.get("call_id")
            or evidence.get("thread_id")
            != suppressed["request_metadata"]["thread_id"]
            or evidence.get("turn_id") != suppressed["request_metadata"]["turn_id"]
            or evidence.get("successor_response_id") != successor.get("response_id")
            or evidence.get("successor_call_id") != successor.get("call_id")
            or evidence.get("agent_message_recipient") != "/root"
            or not str(evidence.get("agent_message_author")).startswith("/root/")
            or not _hex_digest(evidence.get("agent_message_sha256"))
            or message_id in evidence_message_ids
            or not _collaboration_event_observation_is_between_calls(
                event_unix_ns=message_unix,
                receipt_monotonic_ns=message_mono,
                provider_commit_unix_ns=suppressed["commit_unix_ns"],
                successor_admitted_unix_ns=successor["admitted_unix_ns"],
            )
        ):
            raise ReportError(
                f"{run_label} suppressed collaboration wait lacks one unique child result"
            )
        evidence_message_ids.add(message_id)
    superseded_evidence_raw = reconciliation.get(
        "superseded_by_collaboration_message_evidence"
    )
    if (
        not isinstance(superseded_evidence_raw, list)
        or len(superseded_evidence_raw) != len(superseded_calls)
    ):
        raise ReportError(
            f"{run_label} superseded collaboration response evidence is incomplete"
        )
    superseded_by_response = {
        call["response_id"]: call for call in superseded_calls
    }
    for index, raw_evidence in enumerate(superseded_evidence_raw):
        evidence = _gate_object(
            raw_evidence,
            codex_isolated.SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS,
            f"{run_label} superseded-message evidence {index}",
        )
        superseded = superseded_by_response.get(superseded_ids[index])
        successor = (
            calls_by_response.get(
                superseded["appserver_delivery"]["successor_response_id"]
            )
            if isinstance(superseded, Mapping)
            else None
        )
        if (
            superseded is None
            or successor is None
            or evidence.get("response_id") != superseded.get("response_id")
            or evidence.get("provider_call_id") != superseded.get("call_id")
            or evidence.get("thread_id")
            != superseded["request_metadata"]["thread_id"]
            or evidence.get("turn_id")
            != superseded["request_metadata"]["turn_id"]
            or evidence.get("successor_response_id")
            != successor.get("response_id")
            or evidence.get("successor_call_id") != successor.get("call_id")
        ):
            raise ReportError(
                f"{run_label} superseded collaboration response binding changed"
            )
        raw_messages = evidence.get("collaboration_messages")
        if not isinstance(raw_messages, list) or not raw_messages:
            raise ReportError(
                f"{run_label} superseded collaboration response lacks child messages"
            )
        messages: list[dict[str, Any]] = []
        for message_index, raw_message in enumerate(raw_messages):
            message = _gate_object(
                raw_message,
                codex_isolated.COLLABORATION_MESSAGE_EVIDENCE_KEYS,
                f"{run_label} superseded child message {index}:{message_index}",
            )
            message_id = message.get("item_id")
            message_mono = _gate_positive(
                message.get("observed_at_monotonic_ns"),
                f"{run_label} superseded child-message time",
            )
            message_unix = _gate_positive(
                message.get("observed_at_unix_ns"),
                f"{run_label} superseded child-message wall time",
            )
            if (
                not isinstance(message_id, str)
                or not message_id
                or message_id in evidence_message_ids
                or not _hex_digest(message.get("item_sha256"))
                or not isinstance(message.get("author"), str)
                or not _rooted_collaboration_route_matches(
                    thread_id=evidence.get("thread_id"),
                    author=message.get("author"),
                    recipient=message.get("recipient"),
                    thread_accounting=usage.get("thread_accounting"),
                    root_thread_id=usage.get("root_thread_id"),
                )
                or not _collaboration_event_observation_is_between_calls(
                    event_unix_ns=message_unix,
                    receipt_monotonic_ns=message_mono,
                    provider_commit_unix_ns=superseded["commit_unix_ns"],
                    successor_admitted_unix_ns=successor["admitted_unix_ns"],
                )
            ):
                raise ReportError(
                    f"{run_label} superseded child-message evidence changed"
                )
            evidence_message_ids.add(message_id)
            messages.append(message)
        if messages != sorted(
            messages,
            key=lambda message: (
                message["observed_at_monotonic_ns"],
                message["observed_at_unix_ns"],
                message["item_id"],
            ),
        ):
            raise ReportError(
                f"{run_label} superseded child-message evidence is out of order"
            )
    interrupt_item_ids: set[str] = set()
    interrupt_output_ids: set[str] = set()
    for index, raw_evidence in enumerate(discarded_evidence_raw):
        target = calls_by_response.get(discarded_ids[index])
        interrupting_response_id = (
            raw_evidence.get("interrupting_response_id")
            if isinstance(raw_evidence, Mapping)
            else None
        )
        interrupting = calls_by_response.get(interrupting_response_id)
        if target is None or interrupting is None:
            raise ReportError(
                f"{run_label} explicit-child-interrupt discard cites an unknown response"
            )
        evidence = _validate_explicit_child_interrupt_discard(
            evidence_value=raw_evidence,
            target=target,
            interrupting=interrupting,
            thread_accounting=usage.get("thread_accounting"),
            root_thread_id=usage.get("root_thread_id"),
            label=f"{run_label} explicit-child-interrupt evidence {index}",
        )
        function_item_id = str(evidence["interrupt_function_item_id"])
        output_item_id = str(evidence["interrupt_output_item_id"])
        if function_item_id in interrupt_item_ids or output_item_id in interrupt_output_ids:
            raise ReportError(
                f"{run_label} explicit-child-interrupt evidence reuses an event item"
            )
        interrupt_item_ids.add(function_item_id)
        interrupt_output_ids.add(output_item_id)
    if usage.get("suppressed_collaboration_wait_evidence") != evidence_raw:
        raise ReportError(f"{run_label} retained suppressed-wait evidence changed")
    if (
        usage.get("superseded_by_collaboration_message_evidence")
        != superseded_evidence_raw
    ):
        raise ReportError(
            f"{run_label} retained superseded-message evidence changed"
        )
    if (
        usage.get("discarded_after_explicit_child_interrupt_evidence")
        != discarded_evidence_raw
    ):
        raise ReportError(
            f"{run_label} retained explicit-child-interrupt evidence changed"
        )
    usage_gate = _gate_object(
        usage.get("provider_token_gate"),
        runner.ULTRA_PROVIDER_GATE_SUMMARY_KEYS,
        f"{run_label} usage gate attachment",
    )
    if (
        usage_gate.get("enabled") is not True
        or usage_gate.get("response_token_bound") != runner.PROVIDER_RESPONSE_TOKEN_BOUND
        or type(usage_gate.get("response_token_bound")) is not int
        or usage_gate.get("artifact_path") != str(artifact_path)
        or usage_gate.get("record_sha256") != record.get("record_sha256")
        or usage_gate.get("final_attached") is not True
        or usage_gate.get("exact_for_usage") is not True
        or usage_gate.get("terminal") != state
    ):
        raise ReportError(f"{run_label} usage ledger is not attached to this sealed gate")
    teardown = _gate_object(
        usage.get("adapter_teardown"),
        runner.ULTRA_ADAPTER_TEARDOWN_KEYS,
        f"{run_label} adapter teardown",
    )
    teardown_returncode = teardown.get("returncode")
    teardown_signal = teardown.get("signal")
    if (
        teardown.get("process_group_isolated") is not True
        or teardown.get("immediate") is not (state.get("close_reason") != "natural_end")
        or teardown.get("stdin_closed") is not True
        or teardown.get("completed") is not True
        or type(teardown_returncode) is not int
        or (teardown_returncode, teardown_signal)
        not in ((0, None), (-15, "SIGTERM"), (-9, "SIGKILL"))
        or type(run.get("agent_exit_code")) is not int
        or run.get("agent_exit_code") != 0
    ):
        raise ReportError(f"{run_label} adapter did not exit cleanly at its gate endpoint")
    for clock in ("unix", "monotonic"):
        started = _gate_positive(
            teardown.get(f"started_at_{clock}_ns"), f"{run_label} teardown start"
        )
        completed = _gate_positive(
            teardown.get(f"completed_at_{clock}_ns"), f"{run_label} teardown completion"
        )
        if completed < started:
            raise ReportError(f"{run_label} adapter teardown clocks regress")
        if clock == "monotonic" and (
            started < terminal_mono
            or completed - started > int(summary["cleanup_grace_seconds"] * 1_000_000_000)
        ):
            raise ReportError(f"{run_label} adapter teardown is not immediate after gate close")

    measurement = run.get("token_measurement")
    if not isinstance(measurement, Mapping):
        raise ReportError(f"{run_label} lacks its exact token measurement")
    enforcement = _gate_object(
        measurement.get("limit_enforcement"),
        _ULTRA_LIMIT_ENFORCEMENT_FIELDS,
        f"{run_label} token-limit enforcement",
    )
    triggered = derived_crossing is not None
    crossing_tokens = (
        derived_crossing["completed_tokens"] if derived_crossing is not None else None
    )
    crossing_overshoot = (
        crossing_tokens - token_limit if crossing_tokens is not None else None
    )
    final_tokens = running_total if triggered else None
    final_overshoot = max(0, running_total - token_limit) if triggered else None
    if (
        enforcement.get("mode") != runner.ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE
        or enforcement.get("notification") != runner.ULTRA_USAGE_NOTIFICATION
        or enforcement.get("configured_limit_tokens") != token_limit
        or type(enforcement.get("configured_limit_tokens")) is not int
        or enforcement.get("triggered") is not triggered
        or enforcement.get("observed_tokens") != crossing_tokens
        or enforcement.get("overshoot_tokens") != crossing_overshoot
        or enforcement.get("first_crossing_tokens") != crossing_tokens
        or enforcement.get("first_crossing_overshoot_tokens") != crossing_overshoot
        or enforcement.get("final_endpoint_tokens") != final_tokens
        or enforcement.get("final_overshoot_tokens") != final_overshoot
        or enforcement.get("checked_before_submission_validation") is not True
        or enforcement.get("one_response_overshoot_possible") is not True
        or enforcement.get("concurrent_inflight_overshoot_possible") is not False
        or (
            triggered
            and any(
                type(enforcement.get(field)) is not int
                for field in (
                    "observed_tokens",
                    "overshoot_tokens",
                    "first_crossing_tokens",
                    "first_crossing_overshoot_tokens",
                    "final_endpoint_tokens",
                    "final_overshoot_tokens",
                )
            )
        )
    ):
        raise ReportError(
            f"{run_label} token-limit enforcement does not match the provider endpoint"
        )

    boundary = usage.get("submission_boundary")
    passed = run.get("pass") is True
    failure_code = run.get("failure_code")
    close_reason = state.get("close_reason")
    terminal_transition = terminal[0]
    accepted_endpoint = passed or (
        failure_code == "RULE_VIOLATION"
        and isinstance(boundary, Mapping)
        and usage.get("submission_boundary_exact") is True
    )
    if accepted_endpoint:
        if not isinstance(boundary, Mapping):
            raise ReportError(f"{run_label} accepted run lacks its submission boundary")
        request_published = _gate_positive(
            boundary.get("request_published_at_monotonic_ns"),
            f"{run_label} request publication",
        )
        gate_close = boundary.get("provider_gate_close")
        if (
            close_reason != "accepted_submission"
            or derived_crossing is not None
            or state.get("crossing_closed") is not False
            or usage.get("submission_boundary_exact") is not True
            or usage.get("drain_complete") is not False
            or usage.get("tree_quiescent") is not False
            or not isinstance(gate_close, Mapping)
            or set(gate_close) != {"won", "requested_reason", "effective_reason", "phase", "sequence"}
            or gate_close.get("won") is not True
            or gate_close.get("requested_reason") != "accepted_submission"
            or gate_close.get("effective_reason") != "accepted_submission"
            or gate_close.get("phase") != "CLOSED"
            or type(gate_close.get("sequence")) is not int
            or terminal_transition.get("reason") != "terminal_close:accepted_submission"
            or terminal_transition.get("call_id") is not None
            or terminal_transition.get("sequence") != gate_close.get("sequence")
            or terminal_transition.get("monotonic_ns") <= request_published
            or any(call["admitted_monotonic_ns"] >= request_published for call in calls)
            or any(call["upstream_start_monotonic_ns"] > request_published for call in calls)
            or any(call["commit_monotonic_ns"] > request_published for call in calls)
        ):
            raise ReportError(f"{run_label} accepted gate close is not ordered after publication")
        matching = [call for call in calls if call["response_id"] == boundary.get("response_id")]
        matching_crossbind = (
            matching[0].get("appserver_crossbind") if len(matching) == 1 else None
        )
        if (
            len(matching) != 1
            or matching[0]["commit_monotonic_ns"] >= request_published
            or matching[0]["appserver_delivery"]["kind"]
            != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
            or not isinstance(matching_crossbind, Mapping)
            or matching_crossbind.get("event_sequence")
            != boundary.get("raw_response_notification_sequence")
        ):
            raise ReportError(f"{run_label} accepted response was not committed before publication")
        endpoint = "accepted_provider_gate_close"
    elif failure_code == "TOKEN_LIMIT":
        close_transitions = [
            transition
            for transition in transitions
            if transition.get("to_phase") == "CLOSED"
            and transition.get("reason") == "first_token_limit_crossing"
        ]
        if (
            close_reason != "token_limit"
            or derived_crossing is None
            or boundary is not None
            or usage.get("submission_boundary_exact") is not False
            or usage.get("drain_complete") is not False
            or usage.get("tree_quiescent") is not False
            or usage.get("stop_reason") != "token_limit"
            or len(close_transitions) != 1
            or close_transitions[0].get("call_id") != derived_crossing["call_id"]
            or close_transitions[0].get("sequence") <= derived_crossing["sequence"]
            or not isinstance(usage.get("first_crossing"), Mapping)
            or usage["first_crossing"].get("response_id") != derived_crossing["response_id"]
            or usage["first_crossing"].get("tokens") != derived_crossing["completed_tokens"]
        ):
            raise ReportError(f"{run_label} TOKEN_LIMIT is not the sole sanitized crossing")
        endpoint = "sanitized_provider_gate_crossing"
    else:
        if (
            close_reason != "natural_end"
            or derived_crossing is not None
            or boundary is not None
            or usage.get("submission_boundary_exact") is not False
            or usage.get("drain_complete") is not True
            or usage.get("tree_quiescent") is not True
            or terminal_transition.get("reason") != "terminal_close:natural_end"
            or terminal_transition.get("call_id") is not None
        ):
            raise ReportError(f"{run_label} natural failure lacks a terminal tree/gate close")
        endpoint = "natural_provider_and_tree_close"

    derived = _gate_object(
        authentication.get("derived"),
        _PROVIDER_GATE_DERIVED_FIELDS,
        f"{run_label} retained gate derivation",
    )
    if (
        type(derived.get("completed_tokens")) is not int
        or type(derived.get("response_count")) is not int
        or any(
            type(derived.get(field)) is not int
            for field in (
                "provider_response_count",
                "appserver_response_count",
                "suppressed_collaboration_wait_response_count",
                "superseded_by_collaboration_message_response_count",
                "discarded_after_explicit_child_interrupt_response_count",
            )
        )
        or any(
            not isinstance(derived.get(field), list)
            for field in (
                "response_ids",
                "provider_response_ids",
                "appserver_response_ids",
                "suppressed_collaboration_wait_response_ids",
                "superseded_by_collaboration_message_response_ids",
                "discarded_after_explicit_child_interrupt_response_ids",
            )
        )
        or any(
            not isinstance(response_id, str) or not response_id
            for field in (
                "response_ids",
                "provider_response_ids",
                "appserver_response_ids",
                "suppressed_collaboration_wait_response_ids",
                "superseded_by_collaboration_message_response_ids",
                "discarded_after_explicit_child_interrupt_response_ids",
            )
            for response_id in derived.get(field, [])
        )
        or derived.get("poisoned") is not False
        or derived.get("appserver_deliveries_reconciled") is not True
    ):
        raise ReportError(f"{run_label} retained gate derivation has invalid JSON types")
    expected_derived = {
        "completed_tokens": running_total,
        "response_count": len(calls),
        "response_ids": provider_ids,
        "provider_response_count": len(calls),
        "provider_response_ids": provider_ids,
        "appserver_response_count": len(direct_calls),
        "appserver_response_ids": appserver_ids,
        "suppressed_collaboration_wait_response_count": len(suppressed_calls),
        "suppressed_collaboration_wait_response_ids": suppressed_ids,
        "superseded_by_collaboration_message_response_count": len(
            superseded_calls
        ),
        "superseded_by_collaboration_message_response_ids": superseded_ids,
        "discarded_after_explicit_child_interrupt_response_count": len(
            discarded_calls
        ),
        "discarded_after_explicit_child_interrupt_response_ids": discarded_ids,
        "first_crossing": derived_crossing,
        "poisoned": False,
        "appserver_deliveries_reconciled": True,
    }
    if derived != expected_derived:
        raise ReportError(f"{run_label} retained gate derivation is stale")
    return {
        "endpoint": endpoint,
        "record_sha256": record["record_sha256"],
        "file_sha256": file_digest,
        "completed_tokens": running_total,
        "response_count": len(calls),
        "response_ids": provider_ids,
        "provider_response_count": len(calls),
        "provider_response_ids": provider_ids,
        "appserver_response_count": len(direct_calls),
        "appserver_response_ids": appserver_ids,
        "suppressed_collaboration_wait_response_count": len(suppressed_calls),
        "suppressed_collaboration_wait_response_ids": suppressed_ids,
        "superseded_by_collaboration_message_response_count": len(
            superseded_calls
        ),
        "superseded_by_collaboration_message_response_ids": superseded_ids,
        "discarded_after_explicit_child_interrupt_response_count": len(
            discarded_calls
        ),
        "discarded_after_explicit_child_interrupt_response_ids": discarded_ids,
        "request_kinds": [
            call["request_metadata"]["request_kind"] for call in commit_order
        ],
        "release_kinds": [call["release_kind"] for call in commit_order],
        "first_crossing": derived_crossing,
        "provider_requests_quiescent": True,
        "setup_requests_empty": True,
        "appserver_deliveries_reconciled": True,
        "tree_quiescent": usage.get("tree_quiescent") is True,
        "close_reason": close_reason,
        "adapter_teardown_complete": teardown.get("completed") is True,
        "adapter_teardown_immediate": teardown.get("immediate"),
        "reservation_protocol": "concurrent_then_drain_then_exclusive",
        "dns_variability": runner.PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION,
    }


def _validate_canary_projection_provider_reconciliation(
    projection: Mapping[str, Any],
    run: Mapping[str, Any],
    authentication: Mapping[str, Any],
    label: str,
) -> None:
    """Bind a canary projection's usage partition to the authenticated run."""

    usage = run.get("token_usage")
    if not isinstance(usage, Mapping):
        raise ReportError(f"{label} runner has no token-usage record")
    expected = _gate_object(
        usage.get("provider_usage_reconciliation"),
        codex_isolated.PROVIDER_USAGE_RECONCILIATION_KEYS,
        f"{label} runner provider usage reconciliation",
    )
    actual = _gate_object(
        projection.get("provider_usage_reconciliation"),
        codex_isolated.PROVIDER_USAGE_RECONCILIATION_KEYS,
        f"{label} projection provider usage reconciliation",
    )
    provider_usage = _gate_usage(
        actual.get("provider_usage"), f"{label} projection provider usage"
    )
    appserver_usage = _gate_usage(
        actual.get("appserver_usage"), f"{label} projection app-server usage"
    )
    suppressed_usage = _gate_usage(
        actual.get("suppressed_collaboration_wait_usage"),
        f"{label} projection suppressed-wait usage",
    )
    superseded_usage = _gate_usage(
        actual.get("superseded_by_collaboration_message_usage"),
        f"{label} projection superseded-message usage",
    )
    discarded_usage = _gate_usage(
        actual.get("discarded_after_explicit_child_interrupt_usage"),
        f"{label} projection explicit-child-interrupt discard usage",
    )
    if (
        dict(actual) != dict(expected)
        or actual.get("schema_version")
        != codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
        or actual.get("provider_response_count")
        != authentication.get("provider_response_count")
        or actual.get("appserver_response_count")
        != authentication.get("appserver_response_count")
        or actual.get("suppressed_collaboration_wait_response_count")
        != authentication.get("suppressed_collaboration_wait_response_count")
        or actual.get("superseded_by_collaboration_message_response_count")
        != authentication.get(
            "superseded_by_collaboration_message_response_count"
        )
        or actual.get("discarded_after_explicit_child_interrupt_response_count")
        != authentication.get(
            "discarded_after_explicit_child_interrupt_response_count"
        )
        or actual.get("provider_response_ids")
        != authentication.get("provider_response_ids")
        or actual.get("appserver_response_ids")
        != authentication.get("appserver_response_ids")
        or actual.get("suppressed_collaboration_wait_response_ids")
        != authentication.get("suppressed_collaboration_wait_response_ids")
        or actual.get("superseded_by_collaboration_message_response_ids")
        != authentication.get(
            "superseded_by_collaboration_message_response_ids"
        )
        or actual.get("discarded_after_explicit_child_interrupt_response_ids")
        != authentication.get(
            "discarded_after_explicit_child_interrupt_response_ids"
        )
        or provider_usage["total_tokens"] != authentication.get("completed_tokens")
        or any(
            provider_usage[field]
            != appserver_usage[field]
            + suppressed_usage[field]
            + superseded_usage[field]
            + discarded_usage[field]
            for field in ACCOUNTING_TOKEN_FIELDS
        )
    ):
        raise ReportError(f"{label} projection provider usage reconciliation changed")


def _validate_token_canary_provider_gate_shape(
    authentication: Mapping[str, Any], label: str
) -> None:
    """Require the exact Token V8 below-cap turn then compaction crossing."""

    crossing = authentication.get("first_crossing")
    if (
        authentication.get("endpoint") != "sanitized_provider_gate_crossing"
        or authentication.get("response_count") != 2
        or type(authentication.get("response_count")) is not int
        or authentication.get("request_kinds") != ["turn", "compaction"]
        or authentication.get("release_kinds")
        != [
            "byte_identity",
            runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
        ]
        or authentication.get(
            "superseded_by_collaboration_message_response_count"
        )
        != 0
        or authentication.get(
            "superseded_by_collaboration_message_response_ids"
        )
        != []
        or authentication.get(
            "discarded_after_explicit_child_interrupt_response_count"
        )
        != 0
        or authentication.get(
            "discarded_after_explicit_child_interrupt_response_ids"
        )
        != []
        or not isinstance(crossing, Mapping)
        or crossing.get("request_kind") != "compaction"
        or crossing.get("release_kind")
        != runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
    ):
        raise ReportError(
            f"{label} is not the exact below-cap turn/compaction Token V8 gate shape"
        )


def _validate_submission_event_order_v5(
    value: Mapping[str, Any],
    label: str,
    *,
    require_event_timestamps: bool,
) -> str:
    """Independently authenticate the two-order submission-barrier v5 contract."""

    if (
        value.get("schema_version")
        != ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
    ):
        raise ReportError(f"{label} is not submission-barrier schema v5")
    dynamic_before = value.get(
        "dynamic_call_observed_before_raw_response_completed"
    )
    response_before = value.get(
        "raw_response_completed_before_dynamic_call_observed"
    )
    if type(dynamic_before) is not bool or type(response_before) is not bool:
        raise ReportError(f"{label} has non-Boolean submission event-order flags")
    if (dynamic_before, response_before) == (True, False):
        wanted = "inner_dynamic_call_before_raw_response_completed"
    elif (dynamic_before, response_before) == (False, True):
        wanted = "raw_response_completed_before_inner_dynamic_call"
    else:
        raise ReportError(f"{label} does not attest exactly one submission event order")
    if value.get("submission_event_order") != wanted:
        raise ReportError(f"{label} submission event-order enum disagrees with its flags")
    if value.get("raw_response_completed_before_boundary_publication") is not True:
        raise ReportError(f"{label} does not place raw-response completion before publication")
    if not require_event_timestamps:
        return wanted

    timestamp_fields = (
        "inner_dynamic_item_started_at_monotonic_ns",
        "captured_at_monotonic_ns",
        "raw_response_observed_at_monotonic_ns",
        "request_published_at_monotonic_ns",
    )
    timestamps = {field: value.get(field) for field in timestamp_fields}
    if any(type(observed) is not int or observed <= 0 for observed in timestamps.values()):
        raise ReportError(f"{label} has missing or invalid monotonic event timestamps")
    inner_ns = timestamps["inner_dynamic_item_started_at_monotonic_ns"]
    captured_ns = timestamps["captured_at_monotonic_ns"]
    response_ns = timestamps["raw_response_observed_at_monotonic_ns"]
    published_ns = timestamps["request_published_at_monotonic_ns"]
    assert isinstance(inner_ns, int)
    assert isinstance(captured_ns, int)
    assert isinstance(response_ns, int)
    assert isinstance(published_ns, int)
    valid_sequence = (
        inner_ns <= captured_ns < response_ns
        if dynamic_before
        else response_ns < inner_ns <= captured_ns
    )
    if not valid_sequence:
        raise ReportError(f"{label} submission event order contradicts its timestamps")
    if captured_ns > published_ns or response_ns > published_ns:
        raise ReportError(f"{label} submission events occur after boundary publication")
    return wanted


def _validate_nested_submission_wire_v5(
    value: Mapping[str, Any], label: str
) -> None:
    """Authenticate the exact v2 transport and independently derive its yield margin."""

    codex = ultra_canary.codex_isolated
    expected_yield = codex.nested_submission_exec_yield_record()
    wall_seconds = value.get("outer_exec_yield_attempt_wall_seconds")
    reserve_seconds = value.get(
        "outer_exec_yield_post_submission_validation_reserve_seconds"
    )
    envelope_ms = value.get("outer_exec_yield_envelope_ms")
    yield_ms = value.get("outer_exec_yield_time_ms")
    margin_ms = value.get("outer_exec_yield_margin_ms")
    outer_raw_item_id = value.get("outer_raw_item_id")
    outer_call_id = value.get("outer_exec_call_id")
    inner_call_id = value.get("call_id")
    outer_observed_ns = value.get("outer_raw_item_observed_at_monotonic_ns")
    inner_started_ns = value.get("inner_dynamic_item_started_at_monotonic_ns")
    if (
        value.get("schema_version") != codex.SUBMISSION_BARRIER_SCHEMA_VERSION
        or value.get("submission_transport") != codex.NESTED_SUBMISSION_WIRE_FORMAT
        or value.get("candidate_path") != "Candidate.lean"
        or value.get("outer_raw_item_type") != "custom_tool_call"
        or value.get("outer_exec_name") != "exec"
        or not all(
            isinstance(item, str) and bool(item)
            for item in (outer_raw_item_id, outer_call_id, inner_call_id)
        )
        or len({outer_raw_item_id, outer_call_id, inner_call_id}) != 3
        or value.get("inner_dynamic_call_id") != inner_call_id
        or value.get("inner_dynamic_tool_name") != "submit_proof"
        or value.get("inner_dynamic_arguments")
        != {"candidate_path": "Candidate.lean"}
        or value.get("outer_exec_program") != codex.NESTED_SUBMISSION_EXEC_SOURCE
        or not codex.is_canonical_nested_submit_exec_input(
            value.get("outer_exec_program"), candidate_path="Candidate.lean"
        )
        or value.get("outer_exec_program_bytes")
        != codex.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        or type(value.get("outer_exec_program_bytes")) is not int
        or value.get("outer_exec_program_sha256")
        != codex.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        or any(value.get(field) != wanted for field, wanted in expected_yield.items())
        or type(wall_seconds) is not int
        or type(reserve_seconds) is not int
        or type(envelope_ms) is not int
        or type(yield_ms) is not int
        or type(margin_ms) is not int
        or envelope_ms != 1_000 * (wall_seconds + reserve_seconds)
        or margin_ms != yield_ms - envelope_ms
        or margin_ms <= 0
        or yield_ms <= envelope_ms
        or type(outer_observed_ns) is not int
        or type(inner_started_ns) is not int
        or not 0 < outer_observed_ns <= inner_started_ns
        or value.get("outer_raw_item_observed_before_inner_dynamic_call") is not True
    ):
        raise ReportError(f"{label} does not authenticate the schema-v5 anti-yield wire")


def _relative_path(value: Any, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ReportError(f"{label} has no file path")
    path = Path(value)
    if path.is_absolute() or any(part in ("", ".", "..") for part in path.parts):
        raise ReportError(f"{label} has an unsafe file path: {value}")
    return path


def _find_repository_file(root: Path, raw_path: Any, label: str) -> Path:
    relative = _relative_path(raw_path, label)
    candidates = (root, root.parent, root.parent.parent)
    found: list[Path] = []
    for base in candidates:
        candidate = (base / relative).resolve()
        try:
            candidate.relative_to(base.resolve())
        except ValueError:
            continue
        if candidate.is_file() and candidate not in found:
            found.append(candidate)
    if not found:
        raise ReportError(f"cannot find {label}: {relative}")
    if len(found) > 1:
        raise ReportError(f"{label} is ambiguous below the benchmark ancestors: {relative}")
    return found[0]


def _require_sha_match(path: Path, expected: Any, label: str) -> None:
    if not _hex_digest(expected):
        raise ReportError(f"{label} has no valid recorded SHA-256")
    actual = _file_digest(path)
    if actual != expected:
        raise ReportError(
            f"{label} changed after it was frozen: expected {expected}, found {actual}"
        )


def _authenticate_token_canary_production_freeze(
    project_root: Path,
    evidence: Mapping[str, Any],
    *,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Independently authenticate the token canary's production freeze artifact."""

    project = project_root.resolve()
    artifact_root_relative = _relative_path(
        evidence.get("artifact_root"), "token-control canary artifact root"
    )
    unresolved_artifact_root = project / artifact_root_relative
    if unresolved_artifact_root.is_symlink():
        raise ReportError("token-control canary artifact root must not be a symlink")
    artifact_root = unresolved_artifact_root.resolve()
    try:
        artifact_root.relative_to(project)
    except ValueError as error:
        raise ReportError(
            "token-control canary artifact root escapes the repository"
        ) from error
    if not artifact_root.is_dir():
        raise ReportError("token-control canary artifact root is missing")

    artifacts = evidence.get("artifacts")
    descriptor = artifacts.get("freeze_check") if isinstance(artifacts, Mapping) else None
    if not isinstance(descriptor, Mapping) or set(descriptor) != {"path", "sha256"}:
        raise ReportError(
            "token-control canary production freeze artifact descriptor is invalid"
        )
    artifact_relative = _relative_path(
        descriptor.get("path"), "token-control canary production freeze artifact"
    )
    unresolved_artifact = artifact_root / artifact_relative
    if unresolved_artifact.is_symlink():
        raise ReportError(
            "token-control canary production freeze artifact must not be a symlink"
        )
    artifact_path = unresolved_artifact.resolve()
    try:
        artifact_path.relative_to(artifact_root)
    except ValueError as error:
        raise ReportError(
            "token-control canary production freeze artifact escapes its artifact root"
        ) from error
    if not artifact_path.is_file():
        raise ReportError("token-control canary production freeze artifact is missing")
    _require_sha_match(
        artifact_path,
        descriptor.get("sha256"),
        "token-control canary production freeze artifact",
    )
    production_freeze = _object(
        artifact_path, "token-control canary production freeze artifact"
    )
    if production_freeze.get("prompt_protocol") != dict(prompt_protocol):
        raise ReportError("token-control canary production prompt protocol is stale")
    if production_freeze.get("execution_components") != dict(execution_components):
        raise ReportError(
            "token-control canary production execution components are stale"
        )
    return production_freeze


def _frozen_artifact(
    root: Path,
    frozen: Mapping[str, Any],
    environment_copy: Mapping[str, Any],
    *,
    path_field: str,
    digest_field: str,
    label: str,
) -> tuple[Path, Mapping[str, Any]]:
    raw_path = frozen.get(path_field)
    expected = frozen.get(digest_field)
    if raw_path != environment_copy.get(path_field):
        raise ReportError(f"{label} path disagrees across frozen metadata")
    if expected != environment_copy.get(digest_field):
        raise ReportError(f"{label} SHA-256 disagrees across frozen metadata")
    path = _find_repository_file(root, raw_path, label)
    _require_sha_match(path, expected, label)
    return path, _object(path, label)


def _find_freeze_check(analysis_path: Path) -> tuple[Path, Mapping[str, Any]]:
    analysis = analysis_path.resolve()
    candidates = []
    for candidate in (
        analysis.parent / "freeze_check.json",
        analysis.parent.parent / "freeze_check.json",
    ):
        candidate = candidate.resolve()
        if candidate.is_file() and candidate not in candidates:
            candidates.append(candidate)
    if len(candidates) != 1:
        raise ReportError(
            "the analysis must have exactly one adjacent authenticated freeze_check.json"
        )
    return candidates[0], _object(candidates[0], "frozen-run verification")


def _controlled_manifest(path: Path, label: str) -> Mapping[str, Any]:
    try:
        return load_manifest(path)
    except BenchmarkToolError as error:
        raise ReportError(f"invalid {label}: {error}") from error


def _resolve_construction_check(
    root: Path,
    evidence_dir: Path,
    library_probe: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Resolve and authenticate the complete construction evidence.

    ``library_dependency_probe.json`` is intentionally a small pointer now.
    Its target must remain inside the benchmark's evidence directory, and its
    recorded byte digest is checked before the target JSON is trusted.
    """

    pointer_kind = "highambench-library-dependency-evidence-pointer"
    check_kind = "highambench-private-construction-check"
    kind = library_probe.get("kind")
    if kind == check_kind:
        # A direct record is accepted here, but the same complete verification
        # basis and complete manifest-result checks are still required below.
        return library_probe
    if kind != pointer_kind:
        raise ReportError(
            "library_dependency_probe.json is neither a construction check nor its current pointer"
        )

    target = _find_repository_file(
        root,
        library_probe.get("current_evidence"),
        "current library construction evidence",
    )
    evidence_root = evidence_dir.resolve()
    try:
        target.relative_to(evidence_root)
    except ValueError as error:
        raise ReportError(
            "current library construction evidence must remain inside metadata/evidence"
        ) from error
    pointer_path = (evidence_dir / "library_dependency_probe.json").resolve()
    if target == pointer_path or target.suffix != ".json":
        raise ReportError("current library construction evidence has an unsafe target")

    _require_sha_match(
        target,
        library_probe.get("current_evidence_sha256"),
        "current library construction evidence",
    )
    check = _object(target, "current library construction evidence")
    if check.get("kind") != check_kind:
        raise ReportError(
            "current library construction evidence is not a highambench-private-construction-check"
        )
    return check


def _task_records(
    manifest: Mapping[str, Any],
) -> tuple[list[str], list[tuple[str, Mapping[str, Any]]]]:
    papers = manifest.get("papers")
    if not isinstance(papers, list) or not papers or not all(
        isinstance(paper, Mapping) for paper in papers
    ):
        raise ReportError("the report requires a nonempty manifest paper list")
    paper_ids: list[str] = []
    task_records: list[tuple[str, Mapping[str, Any]]] = []
    seen_tasks: set[Any] = set()
    for paper in papers:
        assert isinstance(paper, Mapping)
        paper_id = paper.get("paper_id")
        if not isinstance(paper_id, str) or not paper_id or paper_id in paper_ids:
            raise ReportError("manifest paper IDs must be distinct and nonempty")
        paper_ids.append(paper_id)
        targets = paper.get("targets")
        if not isinstance(targets, list) or not targets or not all(
            isinstance(item, Mapping) for item in targets
        ):
            raise ReportError(f"manifest paper {paper_id} has no usable target list")
        seen_tiers: set[Any] = set()
        for target in targets:
            assert isinstance(target, Mapping)
            if target.get("availability") != "available":
                continue
            tier = target.get("tier")
            task_id = target.get("task_id")
            if (
                not isinstance(tier, str)
                or task_id != f"{paper_id}-{tier}"
                or task_id in seen_tasks
                or tier in seen_tiers
            ):
                raise ReportError(f"manifest has an invalid or repeated task for {paper_id}")
            seen_tiers.add(tier)
            seen_tasks.add(task_id)
            task_records.append((paper_id, target))
    if not task_records:
        raise ReportError("the manifest has no available tasks")
    return paper_ids, task_records


def _selected_tasks(
    tasks: Sequence[Mapping[str, Any]],
) -> list[Mapping[str, Any]]:
    """Return the measured T1--T3 stratum; T4 is whole-paper coverage."""

    return [task for task in tasks if task.get("tier") != "T4"]


def _t4_coverage_rows(
    tasks: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Authenticate and summarize final claim-scoped whole-paper coverage."""

    rows: list[dict[str, Any]] = []
    for task in tasks:
        if task.get("tier") != "T4":
            continue
        task_id = str(task.get("task_id"))
        try:
            summary = validate_t4_task_metadata(task, label=task_id)
        except BenchmarkToolError as error:
            raise ReportError(f"invalid T4 whole-paper metadata for {task_id}: {error}") from error
        review_units = int(summary["review_unit_count"])
        accepted_reviews = int(summary["review_count"])
        rows.append(
            {
                "paper_id": str(task.get("paper_id")),
                "task_id": task_id,
                "tier": "T4",
                "stratum": "whole-paper",
                "source_inventory_count": int(summary["source_inventory_count"]),
                "included_source_count": int(summary["included_source_count"]),
                "excluded_source_count": int(summary["excluded_source_count"]),
                "reviewed_included_source_count": int(summary["included_source_count"]),
                "declaration_count": int(summary["declaration_count"]),
                "reviewed_declaration_count": int(summary["declaration_count"]),
                "review_unit_count": review_units,
                "accepted_review_count": accepted_reviews,
                "accepted_review_unit_coverage_rate": (
                    accepted_reviews / review_units if review_units else None
                ),
                "controlled_sorry_count": int(summary["controlled_sorry_count"]),
                "measurement_ready": summary.get("measurement_ready") is True,
            }
        )
    return rows


def _review_task_records(review: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    """Return either supported fresh-review task-list schema."""

    candidates = [
        review.get(name)
        for name in ("task_reviews", "tasks")
        if review.get(name) is not None
    ]
    if len(candidates) != 1:
        raise ReportError(
            "each review record must contain exactly one of task_reviews or tasks"
        )
    records = candidates[0]
    if not isinstance(records, list) or not records or not all(
        isinstance(item, Mapping) for item in records
    ):
        raise ReportError("a review record has no usable task decisions")
    return list(records)


def _review_identifier(review: Mapping[str, Any], index: int) -> str:
    reviewer = review.get("reviewer")
    reviewer_id = reviewer.get("id") if isinstance(reviewer, Mapping) else None
    reviewer_identity = (
        reviewer.get("identity") if isinstance(reviewer, Mapping) else None
    )
    for value in (
        review.get("review_id"),
        reviewer_id,
        review.get("kind"),
        reviewer_identity,
    ):
        if isinstance(value, str) and value:
            return value
    return f"review-{index + 1}"


def _review_decision(review: Mapping[str, Any]) -> Any:
    return review.get("overall_status", review.get("overall_decision"))


def _task_review_decision(task_review: Mapping[str, Any]) -> Any:
    return task_review.get(
        "review_outcome",
        task_review.get("outcome", task_review.get("decision")),
    )


def _load_review_records(
    root: Path,
    metadata: Path,
    config: Mapping[str, Any],
    *,
    required: bool,
) -> tuple[Mapping[str, Any], ...]:
    """Load current reviews, authenticating a configured private override.

    The private override does not rewrite a failed novelty decision as a pass.
    It only names the fresh records whose exact-target novelty failures may be
    retained while the unchanged matrix is measured privately.
    """

    if not required:
        return ()
    review_dir = metadata / "reviews"
    override = config.get("private_measurement_review_override")
    if isinstance(override, Mapping) and override.get("enabled") is True:
        entries = override.get("review_records")
        if not isinstance(entries, list) or len(entries) < 2 or not all(
            isinstance(entry, Mapping) for entry in entries
        ):
            raise ReportError(
                "the private measurement review override needs at least two authenticated records"
            )
        reviews: list[Mapping[str, Any]] = []
        seen_paths: set[Path] = set()
        for index, entry in enumerate(entries):
            path = _find_repository_file(
                root,
                entry.get("path"),
                f"private measurement review record {index + 1}",
            )
            try:
                path.relative_to(review_dir.resolve())
            except ValueError as error:
                raise ReportError(
                    "private measurement review records must remain inside metadata/reviews"
                ) from error
            if path in seen_paths:
                raise ReportError("the private measurement review override repeats a record")
            seen_paths.add(path)
            _require_sha_match(
                path,
                entry.get("sha256"),
                f"private measurement review record {index + 1}",
            )
            review = _object(path, f"private measurement review record {index + 1}")
            if review.get("record_status") != entry.get("record_status"):
                raise ReportError(
                    "a private measurement review status disagrees with the configured override"
                )
            expected_count = entry.get("task_count")
            if expected_count != len(_review_task_records(review)):
                raise ReportError(
                    "a private measurement review task count disagrees with the configured override"
                )
            reviews.append(review)
        return tuple(reviews)

    review_paths = sorted(review_dir.glob("*.json")) if review_dir.is_dir() else []
    if len(review_paths) < 2:
        raise ReportError("at least two independent review records are required")
    all_reviews = tuple(
        _object(path, f"review record {path.name}") for path in review_paths
    )
    reviews = tuple(
        review
        for review in all_reviews
        if review.get("record_status") in (None, "current_final", "final")
    )
    if len(reviews) < 2:
        raise ReportError(
            "at least two current final review records are required; construction snapshots do not count"
        )
    return reviews


def load_report_inputs(benchmark_root: Path, analysis_path: Path) -> ReportInputs:
    """Read every input used by the report and perform construction checks."""

    root = benchmark_root.resolve()
    if not root.is_dir():
        raise ReportError(f"benchmark root is not a directory: {root}")
    metadata = root / "metadata"
    config = _object(metadata / "config.json", "configuration metadata")
    environment = _object(metadata / "environment.json", "environment metadata")
    manifest = _object(metadata / "manifest.json", "benchmark manifest")
    run_order = _object(metadata / "run_order.json", "run-order metadata")
    analysis = _object(analysis_path.resolve(), "analysis output")

    frozen = config.get("frozen_environment")
    lean_environment = environment.get("lean")
    runtime_environment = environment.get("runtime")
    if not isinstance(frozen, Mapping):
        raise ReportError("configuration metadata has no frozen environment")
    if not isinstance(lean_environment, Mapping):
        raise ReportError("environment metadata has no Lean environment record")
    if not isinstance(runtime_environment, Mapping):
        raise ReportError("environment metadata has no runtime record")

    release_path, _ = _frozen_artifact(
        root,
        frozen,
        environment,
        path_field="release_manifest",
        digest_field="release_manifest_sha256",
        label="evaluation release manifest",
    )
    source_path, _ = _frozen_artifact(
        root,
        frozen,
        lean_environment,
        path_field="numstability_source_manifest",
        digest_field="numstability_source_manifest_sha256",
        label="NumStability source manifest",
    )
    compiled_path, _ = _frozen_artifact(
        root,
        frozen,
        lean_environment,
        path_field="numstability_compiled_manifest",
        digest_field="numstability_compiled_manifest_sha256",
        label="pruned NumStability compiled manifest",
    )
    _, compiled_environment_summary = _frozen_artifact(
        root,
        frozen,
        lean_environment,
        path_field="compiled_environment_summary",
        digest_field="compiled_environment_summary_sha256",
        label="compiled Lean environment summary",
    )
    packages_runtime_path, _ = _frozen_artifact(
        root,
        frozen,
        runtime_environment,
        path_field="packages_runtime_manifest",
        digest_field="packages_runtime_manifest_sha256",
        label="pruned package-runtime manifest",
    )
    _, freeze_check = _find_freeze_check(analysis_path)
    release_manifest = _controlled_manifest(release_path, "evaluation release manifest")
    source_manifest = _controlled_manifest(source_path, "NumStability source manifest")
    compiled_manifest = _controlled_manifest(
        compiled_path, "pruned NumStability compiled manifest"
    )
    packages_runtime_manifest = _controlled_manifest(
        packages_runtime_path, "pruned package-runtime manifest"
    )

    paper_ids, manifest_tasks = _task_records(manifest)
    papers = tuple(
        _object(root / "tasks" / paper_id / "paper.json", f"{paper_id} paper metadata")
        for paper_id in paper_ids
    )
    tasks: list[Mapping[str, Any]] = []
    for paper_id, target in manifest_tasks:
        tier = target.get("tier")
        task_id = target.get("task_id")
        task = _object(
            root / "tasks" / paper_id / str(tier) / "task.json",
            f"{task_id} task metadata",
        )
        if (
            task.get("task_id") != task_id
            or task.get("paper_id") != paper_id
            or task.get("tier") != tier
        ):
            raise ReportError(f"{task_id} task metadata disagrees with the manifest")
        tasks.append(task)

    evidence_dir = metadata / "evidence"
    evidence_paths = sorted(evidence_dir.glob("*.json")) if evidence_dir.is_dir() else []
    evidence = {path.stem: _object(path, f"construction evidence {path.name}") for path in evidence_paths}
    if "library_dependency_probe" not in evidence:
        raise ReportError("missing required construction evidence: library_dependency_probe.json")
    if not any(name.startswith("exact_target_search") for name in evidence):
        raise ReportError("missing exact-target-search construction evidence")
    construction_check = _resolve_construction_check(
        root,
        evidence_dir,
        evidence["library_dependency_probe"],
    )

    reviews = _load_review_records(
        root,
        metadata,
        config,
        required=bool(_selected_tasks(tasks)),
    )

    raw_shared_entries = manifest.get("controlled_shared_files")
    if not isinstance(raw_shared_entries, list) or not raw_shared_entries:
        raise ReportError("manifest has no controlled shared Lean files")
    shared_sources: list[str] = []
    for index, raw_entry in enumerate(raw_shared_entries):
        if not isinstance(raw_entry, Mapping):
            raise ReportError(f"controlled shared Lean entry {index} is invalid")
        shared_path = _find_repository_file(
            root, raw_entry.get("path"), f"controlled shared Lean file {index}"
        )
        shared_sources.append(shared_path.read_text(encoding="utf-8"))
    shared_source = "\n".join(shared_sources)

    result = ReportInputs(
        benchmark_root=root,
        config=config,
        environment=environment,
        manifest=manifest,
        run_order=run_order,
        papers=papers,
        tasks=tuple(tasks),
        evidence=evidence,
        construction_check=construction_check,
        freeze_check=freeze_check,
        release_manifest=release_manifest,
        compiled_environment_summary=compiled_environment_summary,
        packages_runtime_manifest=packages_runtime_manifest,
        source_manifest=source_manifest,
        compiled_manifest=compiled_manifest,
        reviews=reviews,
        analysis=analysis,
        shared_source=shared_source,
    )
    validate_report_inputs(result)
    return result


def _require_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReportError(f"incomplete analysis: {label} is not a list")
    return value


def _analysis_tables(analysis: Mapping[str, Any]) -> tuple[
    list[Mapping[str, Any]],
    list[Mapping[str, Any]],
    list[Mapping[str, Any]],
    list[Mapping[str, Any]],
    bool,
]:
    """Return the four result tables and whether they are observational."""

    official = analysis.get("official_scores_valid") is True
    if official:
        raw_tables = (
            analysis.get("condition_summaries"),
            analysis.get("per_task_summaries"),
            analysis.get("paired_comparisons"),
            analysis.get("per_task_paired_comparisons"),
        )
        observational = False
    else:
        pilot = analysis.get("observational_pilot_results")
        if not isinstance(pilot, Mapping):
            raise ReportError(
                "incomplete analysis: invalid official scores require a complete, clearly labeled observational result block"
            )
        label = str(pilot.get("label", "")).lower()
        if "observational" not in label or "not" not in label or "score" not in label:
            raise ReportError("incomplete analysis: the observational result block lacks its warning label")
        raw_tables = (
            pilot.get("condition_summaries"),
            pilot.get("per_task_summaries"),
            pilot.get("paired_comparisons"),
            pilot.get("per_task_paired_comparisons"),
        )
        observational = True
    tables: list[list[Mapping[str, Any]]] = []
    for name, raw in zip(
        ("condition summaries", "task summaries", "paired summaries", "task paired summaries"),
        raw_tables,
    ):
        values = _require_list(raw, name)
        if not values or not all(isinstance(row, Mapping) for row in values):
            raise ReportError(f"incomplete analysis: {name} is empty or malformed")
        tables.append(list(values))
    return tables[0], tables[1], tables[2], tables[3], observational


def _check_matrix_coverage(
    inputs: ReportInputs,
    selected_runs: Sequence[Mapping[str, Any]],
    condition_rows: Sequence[Mapping[str, Any]],
    task_rows: Sequence[Mapping[str, Any]],
    pair_rows: Sequence[Mapping[str, Any]],
    task_pair_rows: Sequence[Mapping[str, Any]],
) -> None:
    measured_tasks = _selected_tasks(inputs.tasks)
    task_ids = {str(task.get("task_id")) for task in measured_tasks}
    if not task_ids:
        raise ReportError(
            "the measured report requires at least one T1--T3 task; T4 is coverage-only"
        )
    repetitions = inputs.config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        raise ReportError("configuration metadata has no repetitions")
    repetition_ids = {
        item.get("id") for item in repetitions if isinstance(item, Mapping) and isinstance(item.get("id"), str)
    }
    if len(repetition_ids) != len(repetitions):
        raise ReportError("configuration metadata has malformed or repeated repetitions")
    expected = {
        (task_id, repetition_id, condition)
        for task_id in task_ids
        for repetition_id in repetition_ids
        for condition in ("N", "L")
    }
    actual = {
        (run.get("task_id"), run.get("repetition_id"), run.get("condition"))
        for run in selected_runs
    }
    if actual != expected or len(selected_runs) != len(expected):
        raise ReportError("incomplete analysis: selected final runs do not cover the fixed task matrix exactly")

    tier_scopes = {str(task.get("tier")) for task in measured_tasks}
    expected_scopes = {"overall", *tier_scopes}
    condition_scope_pairs = {
        (row.get("scope"), row.get("condition")) for row in condition_rows
    }
    if condition_scope_pairs != {
        (scope, condition)
        for scope in expected_scopes
        for condition in ("N", "L")
    }:
        raise ReportError(
            "incomplete analysis: T1--T3 overall/tier N and L rows are not exact"
        )
    task_conditions = {(row.get("task_id"), row.get("condition")) for row in task_rows}
    if task_conditions != {(task_id, condition) for task_id in task_ids for condition in ("N", "L")}:
        raise ReportError("incomplete analysis: each task needs both an N and an L summary")
    if {row.get("scope") for row in pair_rows} != expected_scopes:
        raise ReportError(
            "incomplete analysis: T1--T3 overall/tier paired rows are not exact"
        )
    if {row.get("task_id") for row in task_pair_rows} != task_ids:
        raise ReportError("incomplete analysis: each task needs a paired-change row")


def _bootstrap_paper_count(
    inputs: ReportInputs, row: Mapping[str, Any]
) -> int:
    """Return the exact paper population for one measured analysis row."""

    task_id = row.get("task_id")
    if isinstance(task_id, str) and task_id:
        return 1
    scope = row.get("scope")
    tasks = _selected_tasks(inputs.tasks)
    if scope == "overall":
        return len({str(task.get("paper_id")) for task in tasks})
    if scope in {"T1", "T2", "T3"}:
        return len(
            {
                str(task.get("paper_id"))
                for task in tasks
                if task.get("tier") == scope
            }
        )
    raise ReportError(f"incomplete analysis: unknown bootstrap scope {scope!r}")


def _release_file_hashes(inputs: ReportInputs) -> dict[str, str]:
    files = inputs.release_manifest.get("files")
    if not isinstance(files, list):
        raise ReportError("evaluation release manifest has no file list")
    result: dict[str, str] = {}
    for entry in files:
        if not isinstance(entry, Mapping):
            raise ReportError("evaluation release manifest contains a malformed entry")
        path = entry.get("path")
        digest = entry.get("sha256")
        if not isinstance(path, str) or not _hex_digest(digest) or path in result:
            raise ReportError("evaluation release manifest contains an invalid file identity")
        result[path] = digest
    return result


def _artifact_path_below_benchmark(
    inputs: ReportInputs, raw_path: Any, label: str
) -> str:
    path = _find_repository_file(inputs.benchmark_root, raw_path, label)
    try:
        return path.relative_to(inputs.benchmark_root).as_posix()
    except ValueError as error:
        raise ReportError(f"{label} is not inside the benchmark release") from error


def _validate_tree_summary(record: Any, label: str) -> tuple[int, int]:
    if not isinstance(record, Mapping):
        raise ReportError(f"compiled environment summary has no {label} tree")
    file_count = record.get("file_count")
    total_bytes = record.get("total_bytes")
    if (
        not isinstance(file_count, int)
        or isinstance(file_count, bool)
        or file_count <= 0
        or not isinstance(total_bytes, int)
        or isinstance(total_bytes, bool)
        or total_bytes < 0
        or not _hex_digest(record.get("tree_sha256"))
    ):
        raise ReportError(f"compiled environment summary has an invalid {label} identity")
    return file_count, total_bytes


def _validate_release_and_environment(inputs: ReportInputs) -> None:
    """Check the release manifest and the three separately frozen tree records."""

    try:
        release_check = verify_manifest(inputs.benchmark_root, dict(inputs.release_manifest))
    except BenchmarkToolError as error:
        raise ReportError(f"cannot verify the evaluation release manifest: {error}") from error
    if not release_check.get("ok"):
        raise ReportError(
            "evaluation release files changed after freezing: " + str(release_check)
        )

    frozen = inputs.config.get("frozen_environment")
    lean = inputs.environment.get("lean")
    if not isinstance(frozen, Mapping) or not isinstance(lean, Mapping):
        raise ReportError("frozen Lean environment metadata is missing")
    release_hashes = _release_file_hashes(inputs)
    required_release_paths = set(CONSTRUCTION_TOOL_PATHS)
    for path_field, digest_field, label in (
        (
            "numstability_source_manifest",
            "numstability_source_manifest_sha256",
            "NumStability source manifest",
        ),
        (
            "numstability_compiled_manifest",
            "numstability_compiled_manifest_sha256",
            "pruned NumStability compiled manifest",
        ),
        (
            "compiled_environment_summary",
            "compiled_environment_summary_sha256",
            "compiled Lean environment summary",
        ),
        (
            "packages_runtime_manifest",
            "packages_runtime_manifest_sha256",
            "pruned package-runtime manifest",
        ),
    ):
        relative = _artifact_path_below_benchmark(inputs, frozen.get(path_field), label)
        required_release_paths.add(relative)
        if release_hashes.get(relative) != frozen.get(digest_field):
            raise ReportError(f"evaluation release does not authenticate the {label}")
    missing = sorted(required_release_paths - set(release_hashes))
    if missing:
        raise ReportError(
            "evaluation release omits construction/runtime files: " + ", ".join(missing)
        )

    source_files = inputs.source_manifest.get("files")
    compiled_files = inputs.compiled_manifest.get("files")
    if (
        not isinstance(source_files, list)
        or not source_files
        or not all(
            isinstance(entry, Mapping)
            and (
                entry.get("path") == "NumStability.lean"
                or str(entry.get("path", "")).startswith("NumStability/")
            )
            for entry in source_files
        )
    ):
        raise ReportError("NumStability source manifest is empty or includes another tree")
    if (
        not isinstance(compiled_files, list)
        or not compiled_files
        or not all(
            isinstance(entry, Mapping)
            and str(entry.get("path", "")).startswith("NumStability/")
            for entry in compiled_files
        )
    ):
        raise ReportError("pruned compiled manifest is empty or includes another namespace")

    runtime_files = inputs.packages_runtime_manifest.get("files")
    runtime_paths = {
        str(entry.get("path"))
        for entry in runtime_files
        if isinstance(entry, Mapping)
    } if isinstance(runtime_files, list) else set()
    runtime_kinds = {
        path: _package_runtime_file_kind(path) for path in runtime_paths
    }
    bad_runtime_paths = {
        path for path, kind in runtime_kinds.items() if kind is None
    }
    if (
        not isinstance(runtime_files, list)
        or not runtime_files
        or len(runtime_paths) != len(runtime_files)
        or bad_runtime_paths
        or "mathlib/Mathlib.lean" not in runtime_paths
        or "olean" not in runtime_kinds.values()
        or "compiled_support" not in runtime_kinds.values()
    ):
        raise ReportError(
            "pruned package-runtime manifest is not exactly mathlib source plus "
            "package .olean, .olean.server, .olean.private, and .ir files"
        )

    runtime_environment = inputs.environment.get("runtime")
    python_record = (
        runtime_environment.get("python")
        if isinstance(runtime_environment, Mapping)
        else None
    )
    if (
        not isinstance(python_record, Mapping)
        or not isinstance(frozen.get("python_version"), str)
        or not frozen.get("python_version")
        or frozen.get("python_version") != python_record.get("version")
        or not _hex_digest(frozen.get("python_binary_sha256"))
        or frozen.get("python_binary_sha256") != python_record.get("binary_sha256")
    ):
        raise ReportError("Python executable identity is missing or inconsistent")

    summary = inputs.compiled_environment_summary
    if (
        summary.get("schema_version") != 1
        or summary.get("kind") != "highambench-compiled-environment-summary"
    ):
        raise ReportError("compiled Lean environment summary has the wrong format")
    toolchain_summary = summary.get("toolchain")
    _validate_tree_summary(toolchain_summary, "Lean toolchain")
    if not isinstance(toolchain_summary, Mapping) or toolchain_summary.get(
        "relative_root"
    ) != ".":
        raise ReportError("compiled environment summary does not cover the whole Lean toolchain")
    packages = summary.get("packages")
    if not isinstance(packages, list) or not packages:
        raise ReportError("compiled Lean environment summary has no package trees")
    package_names: set[str] = set()
    for package in packages:
        if not isinstance(package, Mapping) or not isinstance(package.get("package"), str):
            raise ReportError("compiled Lean environment summary has a malformed package")
        name = str(package["package"])
        if name in package_names:
            raise ReportError("compiled Lean environment summary repeats a package")
        package_names.add(name)
        _validate_tree_summary(package, f"{name} package")
    if "mathlib" not in package_names:
        raise ReportError("compiled Lean environment summary does not include mathlib")


def _identity_matches_manifest(
    identity: Any,
    manifest: Mapping[str, Any],
    *,
    expected_relative_path: str,
    expected_sha256: Any,
    label: str,
) -> None:
    files = manifest.get("files")
    if not isinstance(identity, Mapping) or not isinstance(files, list):
        raise ReportError(f"construction evidence has no {label} identity")
    file_count = len(files)
    total_bytes = sum(
        entry.get("bytes", -1) if isinstance(entry, Mapping) else -1 for entry in files
    )
    if (
        identity.get("path") != expected_relative_path
        or identity.get("sha256") != expected_sha256
        or identity.get("label") != manifest.get("label")
        or identity.get("file_count") != file_count
        or identity.get("verified") != file_count
        or identity.get("total_bytes") != total_bytes
        or identity.get("exact_tree") is not True
    ):
        raise ReportError(f"construction evidence has a stale or incomplete {label} identity")


def _validate_t4_construction_result(
    result: Mapping[str, Any],
    task: Mapping[str, Any],
    target: Mapping[str, Any],
) -> None:
    """Authenticate a T4 skeleton compile without inventing a private proof."""

    task_id = str(task.get("task_id"))
    condition = str(result.get("condition"))
    label = f"{task_id}/{condition} designated-hole T4 skeleton"
    task_validation = task.get("validation")
    lean_target = target.get("lean_target")
    if not isinstance(task_validation, Mapping) or not isinstance(lean_target, Mapping):
        raise ReportError(f"{label} lacks task or manifest validation metadata")
    required = task_validation.get("required_declarations")
    raw_sorries = task_validation.get("controlled_sorries")
    if not isinstance(required, list) or not isinstance(raw_sorries, list):
        raise ReportError(f"{label} lacks plural declarations or controlled holes")
    expected_sorries = [
        {
            key: raw.get(key)
            for key in (
                "placeholder_id",
                "declaration_id",
                "lean_name",
                "marker",
                "line",
                "column",
            )
        }
        for raw in raw_sorries
        if isinstance(raw, Mapping)
    ]
    validation = result.get("validation")
    if (
        len(expected_sorries) != len(raw_sorries)
        or result.get("tier") != "T4"
        or result.get("construction_kind") != "designated-hole-skeleton"
        or result.get("required_declarations") != required
        or result.get("controlled_sorries") != expected_sorries
        or result.get("helpers") != []
        or result.get("target_source_sha256")
        != lean_target.get("controlled_file_sha256")
        or result.get("pass") is not True
        or result.get("reasons") != []
        or not _hex_digest(result.get("manifest_sha256"))
        or not isinstance(validation, Mapping)
        or validation.get("pass") is not True
        or validation.get("failure_code") is not None
        or validation.get("compile_exit_code") != 0
        or validation.get("compile_timed_out") is not False
        or validation.get("compile_system_error") is not None
        or validation.get("olean_created") is not True
        or validation.get("required_declaration_count") != len(required)
        or validation.get("required_declarations_checked") != len(required)
        or validation.get("controlled_sorry_count") != len(raw_sorries)
        or validation.get("controlled_sorries_checked") != len(raw_sorries)
        or validation.get("static_finding_count") != 0
        or validation.get("static_findings") != []
        or validation.get("dependency_audit") is not None
    ):
        raise ReportError(f"{label} has an incomplete compile/hole record")
    if condition == "N":
        preflight = result.get("n_preflight")
        controlled = (
            preflight.get("controlled_files_verified_after_staging")
            if isinstance(preflight, Mapping)
            else None
        )
        probe = preflight.get("import_probe") if isinstance(preflight, Mapping) else None
        if (
            result.get("condition_n_library_arguments_omitted") is not True
            or not isinstance(preflight, Mapping)
            or preflight.get("ok") is not True
            or preflight.get("complete") is not True
            or preflight.get("controlled_manifest_sha256")
            != result.get("manifest_sha256")
            or preflight.get("filesystem_leaks") != []
            or not isinstance(controlled, Mapping)
            or controlled.get("ok") is not True
            or controlled.get("changed") != []
            or controlled.get("missing") != []
            or controlled.get("verified") != controlled.get("expected")
            or type(controlled.get("verified")) is not int
            or controlled["verified"] <= 0
            or not isinstance(probe, Mapping)
            or probe.get("attempted") is not True
            or probe.get("reliable") is not True
            or probe.get("importable") is not False
            or probe.get("timed_out") is not False
            or probe.get("system_error") is not None
        ):
            raise ReportError(f"{label} has an incomplete N isolation preflight")
    elif (
        condition != "L"
        or result.get("condition_n_library_arguments_omitted") is not False
        or result.get("n_preflight") is not None
    ):
        raise ReportError(f"{label} has invalid L isolation metadata")


def _validate_construction(inputs: ReportInputs) -> None:
    search_records = [
        record
        for name, record in inputs.evidence.items()
        if name.startswith("exact_target_search")
    ]
    all_findings: list[Mapping[str, Any]] = []
    recorded_hashes: dict[str, Any] = {}
    raw_manifest_shared = inputs.manifest.get("controlled_shared_files")
    if not isinstance(raw_manifest_shared, list):
        raise ReportError("manifest has no controlled shared Lean files")
    manifest_shared: dict[str, Mapping[str, Any]] = {}
    for raw_entry in raw_manifest_shared:
        if not isinstance(raw_entry, Mapping) or not isinstance(raw_entry.get("path"), str):
            raise ReportError("manifest has an invalid controlled shared Lean entry")
        manifest_shared[str(raw_entry["path"])] = raw_entry
    for search in search_records:
        conclusion = search.get("overall_conclusion")
        findings = search.get("task_findings")
        hashes = search.get("fixed_surface_hashes")
        if (
            not isinstance(conclusion, Mapping)
            or conclusion.get("tier_labels_supported_by_library_surface") is not True
            or any(
                value is not True
                for key, value in conclusion.items()
                if key.endswith("exact_targets_absent")
                or key.endswith("semantic_duplicates_absent")
            )
            or not isinstance(findings, list)
            or not findings
            or not all(isinstance(item, Mapping) for item in findings)
            or not isinstance(hashes, Mapping)
        ):
            raise ReportError("an exact-target-search record is incomplete or failed")
        if not all(
            item.get("exact_duplicate_found") is False
            and item.get("semantic_duplicate_found") is False
            for item in findings
        ):
            raise ReportError("an exact or semantic target duplicate was found")
        finding_papers = {
            str(item.get("task_id", "")).split("-", 1)[0]
            for item in findings
        }
        expected_shared = {
            path: entry.get("sha256")
            for path, entry in manifest_shared.items()
            if isinstance(entry.get("paper_ids"), list)
            and finding_papers.intersection(str(value) for value in entry["paper_ids"])
        }
        recorded_shared = hashes.get("shared_files")
        if not isinstance(recorded_shared, list) or any(
            not isinstance(item, Mapping) for item in recorded_shared
        ):
            raise ReportError("a target-absence search used a stale shared Lean surface")
        recorded_shared_map = {
            str(item.get("path")): item.get("sha256") for item in recorded_shared
        }
        if recorded_shared_map != expected_shared:
            raise ReportError("a target-absence search used a stale shared Lean surface")
        all_findings.extend(findings)
        for key, value in hashes.items():
            if key == "shared_files":
                continue
            if key in recorded_hashes:
                raise ReportError(f"target-absence searches repeat {key}")
            recorded_hashes[key] = value

    expected_task_ids = {task.get("task_id") for task in inputs.tasks}
    finding_ids = [item.get("task_id") for item in all_findings]
    if (
        not finding_ids
        or not set(finding_ids).issubset(expected_task_ids)
        or len(finding_ids) != len(set(finding_ids))
        or set(recorded_hashes) != set(finding_ids)
    ):
        raise ReportError(
            "the target-absence searches have empty, repeated, or unknown task coverage"
        )
    manifest_targets = {item.get("task_id"): item for item in _manifest_targets(inputs)}
    for task_id in finding_ids:
        target = manifest_targets[task_id]
        recorded = recorded_hashes.get(str(task_id))
        lean_target = target.get("lean_target")
        if (
            not isinstance(recorded, Mapping)
            or not isinstance(lean_target, Mapping)
            or recorded.get("sha256") != lean_target.get("controlled_file_sha256")
        ):
            raise ReportError(f"the target-absence search used a stale surface for {task_id}")

    check = inputs.construction_check
    summary = check.get("summary")
    results = check.get("results")
    task_count = len(inputs.tasks)
    proof_count = task_count * 2
    t4_tasks = [task for task in inputs.tasks if task.get("tier") == "T4"]
    private_task_count = task_count - len(t4_tasks)
    expected_construction_summary: dict[str, Any] = {
        "expected": proof_count,
        "checked": proof_count,
        "passed": proof_count,
        "condition_n_passed": task_count,
        "condition_l_passed": task_count,
    }
    if t4_tasks:
        t4_required_declarations = sum(
            len(task["validation"]["required_declarations"])
            for task in t4_tasks
            if isinstance(task.get("validation"), Mapping)
            and isinstance(task["validation"].get("required_declarations"), list)
        )
        t4_controlled_sorries = sum(
            len(task["validation"]["controlled_sorries"])
            for task in t4_tasks
            if isinstance(task.get("validation"), Mapping)
            and isinstance(task["validation"].get("controlled_sorries"), list)
        )
        expected_construction_summary.update(
            {
                "task_count": task_count,
                "required_declaration_count": private_task_count
                + t4_required_declarations,
                "t4_controlled_sorry_count": t4_controlled_sorries,
                "private_proof_task_count": private_task_count,
                "t4_skeleton_task_count": len(t4_tasks),
                "private_proof_result_count": private_task_count * 2,
                "t4_skeleton_result_count": len(t4_tasks) * 2,
            }
        )
    if (
        check.get("kind") != "highambench-private-construction-check"
        or check.get("pass") is not True
        or check.get("schema_version") != (2 if t4_tasks else 1)
        or not isinstance(summary, Mapping)
        or dict(summary) != expected_construction_summary
        or summary.get("expected") != proof_count
        or summary.get("checked") != proof_count
        or summary.get("passed") != proof_count
        or summary.get("condition_n_passed") != task_count
        or summary.get("condition_l_passed") != task_count
        or not isinstance(results, list)
        or len(results) != proof_count
        or not all(isinstance(result, Mapping) for result in results)
    ):
        raise ReportError("the private construction check is incomplete or failed")

    construction_isolation = check.get("isolation")
    if (
        not isinstance(construction_isolation, Mapping)
        or construction_isolation.get(
            "condition_n_preflight_after_complete_controlled_staging"
        )
        is not True
        or construction_isolation.get("condition_n_numstability_mounts_configured")
        is not False
        or construction_isolation.get("condition_l_numstability_mounts_configured")
        is not True
        or (
            bool(t4_tasks)
            and (
                construction_isolation.get("t4_private_gold_required") is not False
                or construction_isolation.get(
                    "t4_skeleton_staged_from_controlled_target"
                )
                is not True
                or construction_isolation.get("t4_designated_sorries_only")
                is not True
            )
        )
    ):
        raise ReportError("construction isolation order or condition mounts are not authenticated")

    basis = check.get("verification_basis")
    if not isinstance(basis, Mapping):
        raise ReportError("private construction check has no authenticated verification basis")
    tool_hashes = basis.get("tools")
    release_hashes = _release_file_hashes(inputs)
    if not isinstance(tool_hashes, Mapping) or set(tool_hashes) != set(
        CONSTRUCTION_TOOL_PATHS
    ):
        raise ReportError("construction evidence does not name the exact checker tool set")
    for relative in CONSTRUCTION_TOOL_PATHS:
        digest = tool_hashes.get(relative)
        if not _hex_digest(digest) or release_hashes.get(relative) != digest:
            raise ReportError(
                f"construction checker {relative} is not authenticated by the release"
            )

    environment_isolation = inputs.environment.get("isolation")
    if not isinstance(environment_isolation, Mapping):
        raise ReportError("environment isolation metadata is missing")
    for relative, field in (
        ("tools/lean_isolated.py", "lean_adapter_sha256"),
        ("tools/validator.py", "validator_sha256"),
        ("tools/dependency_audit.lean", "dependency_audit_sha256"),
    ):
        if tool_hashes.get(relative) != environment_isolation.get(field):
            raise ReportError(f"construction checker {relative} disagrees with the environment")

    frozen = inputs.config.get("frozen_environment")
    lean_environment = inputs.environment.get("lean")
    runtime_environment = inputs.environment.get("runtime")
    runtime_python = (
        runtime_environment.get("python")
        if isinstance(runtime_environment, Mapping)
        else None
    )
    if (
        not isinstance(frozen, Mapping)
        or not isinstance(lean_environment, Mapping)
        or not isinstance(runtime_environment, Mapping)
        or not isinstance(runtime_python, Mapping)
    ):
        raise ReportError("frozen runtime and library identities are missing")

    executables = basis.get("executables")
    python_executable = executables.get("python") if isinstance(executables, Mapping) else None
    bubblewrap = executables.get("bubblewrap") if isinstance(executables, Mapping) else None
    if (
        not isinstance(python_executable, Mapping)
        or not Path(str(python_executable.get("path", ""))).is_absolute()
        or python_executable.get("sha256") != frozen.get("python_binary_sha256")
        or python_executable.get("sha256") != runtime_python.get("binary_sha256")
        or python_executable.get("version") != frozen.get("python_version")
        or python_executable.get("version") != runtime_python.get("version")
        or not isinstance(bubblewrap, Mapping)
        or not Path(str(bubblewrap.get("path", ""))).is_absolute()
        or not _hex_digest(bubblewrap.get("sha256"))
        or bubblewrap.get("sha256")
        != environment_isolation.get("bubblewrap_binary_sha256")
    ):
        raise ReportError("construction executable identities are incomplete or inconsistent")

    source_relative = _artifact_path_below_benchmark(
        inputs, frozen.get("numstability_source_manifest"), "NumStability source manifest"
    )
    compiled_relative = _artifact_path_below_benchmark(
        inputs,
        frozen.get("numstability_compiled_manifest"),
        "pruned NumStability compiled manifest",
    )
    _identity_matches_manifest(
        basis.get("numstability_source"),
        inputs.source_manifest,
        expected_relative_path=source_relative,
        expected_sha256=frozen.get("numstability_source_manifest_sha256"),
        label="NumStability source manifest",
    )
    _identity_matches_manifest(
        basis.get("numstability_compiled"),
        inputs.compiled_manifest,
        expected_relative_path=compiled_relative,
        expected_sha256=frozen.get("numstability_compiled_manifest_sha256"),
        label="pruned NumStability compiled manifest",
    )
    packages_relative = _artifact_path_below_benchmark(
        inputs,
        frozen.get("packages_runtime_manifest"),
        "pruned package-runtime manifest",
    )
    _identity_matches_manifest(
        basis.get("packages_runtime"),
        inputs.packages_runtime_manifest,
        expected_relative_path=packages_relative,
        expected_sha256=frozen.get("packages_runtime_manifest_sha256"),
        label="pruned package-runtime manifest",
    )
    compiled_basis = basis.get("numstability_compiled")
    expected_mount = (
        inputs.benchmark_root.parent.parent / PRUNED_LIBRARY_OLEAN_ROOT
    ).resolve()
    if (
        not isinstance(compiled_basis, Mapping)
        or compiled_basis.get("only_numstability_namespace") is not True
        or not isinstance(compiled_basis.get("mount_root"), str)
        or not Path(str(compiled_basis.get("mount_root", ""))).is_absolute()
        or Path(str(compiled_basis["mount_root"])).resolve() != expected_mount
    ):
        raise ReportError("construction evidence did not use the exact pruned library mount")
    packages_basis = basis.get("packages_runtime")
    packages_manifest_files = inputs.packages_runtime_manifest.get("files")
    packages_manifest_paths = [
        str(entry.get("path"))
        for entry in packages_manifest_files
        if isinstance(entry, Mapping)
    ] if isinstance(packages_manifest_files, list) else []
    packages_source_count = sum(
        _package_runtime_file_kind(path) == "source"
        for path in packages_manifest_paths
    )
    packages_olean_count = sum(
        _package_runtime_file_kind(path) == "olean"
        for path in packages_manifest_paths
    )
    packages_support_count = sum(
        _package_runtime_file_kind(path) == "compiled_support"
        for path in packages_manifest_paths
    )
    expected_packages_mount = (
        inputs.benchmark_root.parent.parent / PACKAGES_RUNTIME_ROOT
    ).resolve()
    if (
        not isinstance(packages_basis, Mapping)
        or packages_basis.get(
            "only_mathlib_source_and_lean_compiled_artifacts"
        ) is not True
        or packages_basis.get("mathlib_source_file_count")
        != packages_source_count
        or packages_basis.get("base_olean_file_count") != packages_olean_count
        or packages_basis.get("compiled_support_file_count")
        != packages_support_count
        or not isinstance(packages_basis.get("mount_root"), str)
        or not Path(str(packages_basis.get("mount_root", ""))).is_absolute()
        or Path(str(packages_basis["mount_root"])).resolve()
        != expected_packages_mount
    ):
        raise ReportError("construction evidence did not use the exact pruned package mount")

    shared_olean = basis.get("shared_olean")
    environment_bundles = lean_environment.get("shared_olean_bundles")
    expected_shared_olean_count = (
        sum(len(bundle) for bundle in environment_bundles.values())
        if isinstance(environment_bundles, Mapping)
        and all(isinstance(bundle, Mapping) for bundle in environment_bundles.values())
        else -1
    )
    if (
        not isinstance(shared_olean, Mapping)
        or not isinstance(shared_olean.get("bundles"), Mapping)
        or dict(shared_olean["bundles"])
        != dict(environment_bundles or {})
        or shared_olean.get("exact_file_count") != expected_shared_olean_count
    ):
        raise ReportError("construction evidence used a stale or non-minimal shared Lean tree")

    freeze_lean = inputs.freeze_check.get("lean")
    if (
        not isinstance(freeze_lean, Mapping)
        or freeze_lean.get("source_files_verified")
        != len(inputs.source_manifest.get("files", []))
        or freeze_lean.get("compiled_files_verified")
        != len(inputs.compiled_manifest.get("files", []))
    ):
        raise ReportError("construction library counts disagree with the frozen run startup")

    task_tiers = {
        str(task.get("task_id")): str(task.get("tier")) for task in inputs.tasks
    }
    tasks_by_id = {str(task.get("task_id")): task for task in inputs.tasks}
    targets_by_id = {
        str(target.get("task_id")): target for target in _manifest_targets(inputs)
    }
    expected_results = {
        (task_id, condition)
        for task_id in task_tiers
        for condition in ("N", "L")
    }
    actual_results = {
        (result.get("task_id"), result.get("condition"))
        for result in results
    }
    if actual_results != expected_results or len(actual_results) != len(results):
        raise ReportError(
            "the construction check does not contain exactly one N and one L result for every task"
        )

    for result in results:
        task_id = str(result.get("task_id"))
        condition = str(result.get("condition"))
        label = f"{task_id}/{condition} private construction proof"
        if task_tiers[task_id] == "T4":
            _validate_t4_construction_result(
                result,
                tasks_by_id[task_id],
                targets_by_id[task_id],
            )
            continue
        validation = result.get("validation")
        audit = validation.get("dependency_audit") if isinstance(validation, Mapping) else None
        if (
            result.get("tier") != task_tiers[task_id]
            or result.get("pass") is not True
            or not isinstance(validation, Mapping)
            or validation.get("pass") is not True
            or type(validation.get("compile_exit_code")) is not int
            or validation.get("compile_exit_code") != 0
            or validation.get("compile_timed_out") is not False
            or validation.get("statement_unchanged") is not True
            or validation.get("controlled_before_ok") is not True
            or validation.get("controlled_hidden_ok") is not True
            or validation.get("failure_code") is not None
            or validation.get("static_finding_count") != 0
            or not isinstance(audit, Mapping)
            or audit.get("complete") is not True
            or type(audit.get("exit_code")) is not int
            or audit.get("exit_code") != 0
            or audit.get("format_version") != 2
            or audit.get("forbidden_dependency_count") != 0
            or audit.get("missing_helper_modules") != []
            or not isinstance(audit.get("library_declarations"), list)
        ):
            raise ReportError(f"{label} has an incomplete compile or dependency record")

        declarations = audit["library_declarations"]
        if condition == "N":
            n_preflight = result.get("n_preflight")
            import_probe = (
                n_preflight.get("import_probe")
                if isinstance(n_preflight, Mapping)
                else None
            )
            staged = (
                n_preflight.get("controlled_files_verified_after_staging")
                if isinstance(n_preflight, Mapping)
                else None
            )
            scan = (
                n_preflight.get("filesystem_scan")
                if isinstance(n_preflight, Mapping)
                else None
            )
            if (
                not isinstance(n_preflight, Mapping)
                or n_preflight.get("ok") is not True
                or n_preflight.get("complete") is not True
                or n_preflight.get("filesystem_leaks") != []
                or n_preflight.get("controlled_manifest_sha256")
                != result.get("manifest_sha256")
                or not _hex_digest(result.get("manifest_sha256"))
                or not isinstance(staged, Mapping)
                or staged.get("ok") is not True
                or not isinstance(staged.get("expected"), int)
                or isinstance(staged.get("expected"), bool)
                or staged.get("expected") <= 0
                or staged.get("verified") != staged.get("expected")
                or staged.get("missing") != []
                or staged.get("changed") != []
                or not isinstance(scan, Mapping)
                or scan.get("root") != "."
                or not isinstance(scan.get("regular_file_count"), int)
                or isinstance(scan.get("regular_file_count"), bool)
                or scan.get("regular_file_count") < staged.get("expected")
                or scan.get("symlink_count") != 0
                or not isinstance(scan.get("markers"), list)
                or "NumStability" not in scan.get("markers")
                or not isinstance(import_probe, Mapping)
                or import_probe.get("attempted") is not True
                or import_probe.get("reliable") is not True
                or import_probe.get("importable") is not False
            ):
                raise ReportError(
                    f"{label} did not scan the complete staged task before private gold was copied"
                )
            if (
                result.get("condition_n_library_arguments_omitted") is not True
                or audit.get("library_use") is not False
                or declarations != []
            ):
                raise ReportError(f"{label} does not prove NumStability was absent")
        elif (
            result.get("condition_n_library_arguments_omitted") is not False
            or audit.get("library_use") is not True
            or not declarations
            or not all(
                isinstance(declaration, Mapping)
                and isinstance(declaration.get("name"), str)
                and declaration.get("name")
                for declaration in declarations
            )
            or not any(
                str(declaration.get("name")).startswith("NumStability.")
                for declaration in declarations
            )
        ):
            raise ReportError(f"{label} does not record real NumStability library use")

    if not inputs.shared_source.strip() or "namespace HighamBench" not in inputs.shared_source:
        raise ReportError("the controlled shared Lean setting is empty or has the wrong namespace")
    if any(
        line.strip().startswith("import NumStability")
        for line in inputs.shared_source.splitlines()
    ):
        raise ReportError("the controlled shared Lean setting imports NumStability")


def _validate_hashes_and_reviews(inputs: ReportInputs) -> None:
    benchmark_ids = {
        inputs.config.get("benchmark_id"),
        inputs.manifest.get("benchmark_id"),
        inputs.run_order.get("benchmark_id"),
    }
    if None in benchmark_ids or len(benchmark_ids) != 1:
        raise ReportError("benchmark_id disagrees across final metadata")
    manifest_paper_ids, _manifest_task_records = _task_records(inputs.manifest)
    if [paper.get("paper_id") for paper in inputs.papers] != manifest_paper_ids:
        raise ReportError("paper metadata disagrees with the manifest")
    if any(
        paper.get("classification_frozen_before_runs") is not True
        for paper in inputs.papers
    ) or any(
        task.get("classification_frozen_before_runs") is not True for task in inputs.tasks
    ):
        raise ReportError("task classifications are not measurement-ready")

    manifest_papers = inputs.manifest["papers"]
    manifest_spec = inputs.manifest.get("specification")
    if not isinstance(manifest_spec, Mapping):
        raise ReportError("benchmark specification metadata is missing")
    for manifest_paper, paper in zip(manifest_papers, inputs.papers):
        manifest_source = manifest_paper.get("source")
        paper_source = paper.get("source")
        paper_spec = paper.get("benchmark_specification")
        if not isinstance(manifest_source, Mapping) or not isinstance(paper_source, Mapping):
            raise ReportError(f"{paper.get('paper_id')} paper source metadata is missing")
        if manifest_source.get("sha256") != paper_source.get("sha256") or not _hex_digest(
            manifest_source.get("sha256")
        ):
            raise ReportError(f"{paper.get('paper_id')} paper SHA-256 disagrees")
        if not isinstance(paper_spec, Mapping):
            raise ReportError(f"{paper.get('paper_id')} specification metadata is missing")
        if manifest_spec.get("sha256") != paper_spec.get("sha256") or not _hex_digest(
            manifest_spec.get("sha256")
        ):
            raise ReportError(f"{paper.get('paper_id')} specification SHA-256 disagrees")

    frozen = inputs.config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        raise ReportError("configuration metadata has no frozen environment")
    if frozen.get("environment_id") != inputs.environment.get("environment_id"):
        raise ReportError("environment_id disagrees across final metadata")
    if frozen.get("environment_bundle_sha256") != inputs.environment.get(
        "environment_bundle_sha256"
    ) or not _hex_digest(inputs.environment.get("environment_bundle_sha256")):
        raise ReportError("environment bundle SHA-256 is missing or inconsistent")
    corpus_slug = "-".join(paper_id.lower() for paper_id in manifest_paper_ids)
    if frozen.get("environment_id") != (
        f"highambench-{corpus_slug}-" + str(frozen.get("environment_bundle_sha256"))[:16]
    ):
        raise ReportError("environment_id is not derived from the frozen environment bundle")
    prompt_path = inputs.benchmark_root / "agent_prompt.md"
    if not prompt_path.is_file():
        raise ReportError(f"missing fixed agent prompt: {prompt_path}")
    _require_sha_match(prompt_path, frozen.get("prompt_sha256"), "fixed agent prompt")

    shared_entries = inputs.manifest.get("controlled_shared_files")
    if not isinstance(shared_entries, list) or not shared_entries:
        raise ReportError("manifest must bind controlled shared Lean files")
    for index, shared_entry in enumerate(shared_entries):
        if not isinstance(shared_entry, Mapping):
            raise ReportError(f"controlled shared Lean entry {index} is invalid")
        shared_path = _find_repository_file(
            inputs.benchmark_root,
            shared_entry.get("path"),
            f"controlled shared Lean file {index}",
        )
        _require_sha_match(
            shared_path,
            shared_entry.get("sha256"),
            f"controlled shared Lean file {index}",
        )

    for _paper_id, target in _manifest_task_records:
        lean_target = target.get("lean_target")
        if not isinstance(lean_target, Mapping):
            raise ReportError(f"manifest task {target.get('task_id')} has no Lean target binding")
        target_path = _find_repository_file(
            inputs.benchmark_root,
            lean_target.get("file"),
            f"controlled target {target.get('task_id')}",
        )
        _require_sha_match(
            target_path,
            lean_target.get("controlled_file_sha256"),
            f"controlled target {target.get('task_id')}",
        )

    # T4 claim-scoped reviews are embedded in task.json and authenticated by
    # the schema-0.4 validator.  The older two-record task-level review gate
    # applies only to measured T1--T3 tasks.
    _t4_coverage_rows(inputs.tasks)
    task_ids = {
        str(task.get("task_id")) for task in _selected_tasks(inputs.tasks)
    }
    override = inputs.config.get("private_measurement_review_override")
    override_enabled = (
        bool(task_ids)
        and isinstance(override, Mapping)
        and override.get("enabled") is True
    )
    ignored_rejections: set[str] = set()
    fresh_context_required = False
    source_fidelity_required = False
    if override_enabled:
        assert isinstance(override, Mapping)
        raw_ignored = override.get("ignored_rejection_task_ids")
        if (
            override.get("scope") != "exact-target novelty rejections only"
            or not isinstance(raw_ignored, list)
            or not raw_ignored
            or not all(isinstance(task_id, str) for task_id in raw_ignored)
            or len(raw_ignored) != len(set(raw_ignored))
            or not set(raw_ignored).issubset(task_ids)
        ):
            raise ReportError(
                "the private measurement review override has an invalid novelty-only scope"
            )
        ignored_rejections = set(raw_ignored)
        fresh_context_required = override.get("fresh_context_reviews_required") is True
        source_fidelity_required = override.get("source_fidelity_required") is True
        if not fresh_context_required or not source_fidelity_required:
            raise ReportError(
                "the private measurement review override must retain fresh-context source-fidelity checks"
            )

    review_coverage = {task_id: 0 for task_id in task_ids}
    review_ids: set[Any] = set()
    observed_novelty_rejections: set[str] = set()
    unfinished_words = (
        "preliminary",
        "pending",
        "provisional",
        "blocked",
        "not release-ready",
    )
    for review_index, review in enumerate(inputs.reviews):
        review_id = _review_identifier(review, review_index)
        if review_id in review_ids:
            raise ReportError("review records need distinct nonempty review_id values")
        review_ids.add(review_id)
        reviewer = review.get("reviewer")
        if fresh_context_required and (
            not isinstance(reviewer, Mapping) or reviewer.get("fresh_context") is not True
        ):
            raise ReportError(
                f"review {review_id} is not an authenticated fresh-context review"
            )
        overall_status = _review_decision(review)
        if not isinstance(overall_status, str) or not overall_status or any(
            word in overall_status.lower() for word in unfinished_words
        ):
            raise ReportError(f"review {review_id} is not final: {overall_status!r}")
        task_reviews = _review_task_records(review)
        covered = {str(item.get("task_id")) for item in task_reviews}
        if covered != task_ids or len(covered) != len(task_reviews):
            raise ReportError(f"review {review_id} has invalid task coverage")
        review_rejections: set[str] = set()
        for task_review in task_reviews:
            task_id = str(task_review.get("task_id"))
            review_coverage[task_id] += 1
            source_faithful = task_review.get("source_faithful")
            if source_fidelity_required and source_faithful is not True:
                raise ReportError(
                    f"review {review_id} did not pass source fidelity for {task_id}"
                )
            outcome = _task_review_decision(task_review)
            if not isinstance(outcome, str) or not outcome:
                raise ReportError(
                    f"review {review_id} has no final outcome for {task_id}"
                )
            lower_outcome = outcome.lower()
            exact_fields = (
                task_review.get("exact_target_absent_from_mathlib"),
                task_review.get("exact_target_absent_from_numstability"),
            )
            explicit_novelty_rejection = any(value is False for value in exact_fields)
            outcome_rejects = any(
                word in lower_outcome for word in ("fail", "reject", "collision")
            )
            if explicit_novelty_rejection or outcome_rejects:
                if (
                    not override_enabled
                    or task_id not in ignored_rejections
                    or not explicit_novelty_rejection
                    or source_faithful is not True
                ):
                    raise ReportError(
                        f"review {review_id} has an unapproved rejection for {task_id}: {outcome!r}"
                    )
                review_rejections.add(task_id)
                observed_novelty_rejections.add(task_id)
            elif not lower_outcome.startswith("pass"):
                raise ReportError(
                    f"review {review_id} has an unfinished outcome for {task_id}: {outcome!r}"
                )
            checks = task_review.get("checks")
            if isinstance(checks, Mapping):
                for name, record in checks.items():
                    status = (
                        record.get("status")
                        if isinstance(record, Mapping)
                        else "pass" if isinstance(record, str) and record.lower().startswith("pass") else None
                    )
                    if status != "pass":
                        check_name = str(name).lower()
                        allowed_novelty_check = (
                            override_enabled
                            and task_id in ignored_rejections
                            and any(word in check_name for word in ("exact", "novel"))
                            and source_faithful is True
                        )
                        if not allowed_novelty_check:
                            raise ReportError(
                                f"review {review_id} check {task_id}/{name} is not a final pass"
                            )
        if "fail" in overall_status.lower() and not (
            override_enabled and review_rejections
        ):
            raise ReportError(f"review {review_id} is not final: {overall_status!r}")
    missing_reviews = sorted(
        str(task_id) for task_id, count in review_coverage.items() if count < 2
    )
    if missing_reviews:
        raise ReportError(
            "each task requires two final review decisions; missing: "
            + ", ".join(missing_reviews)
        )
    if override_enabled and observed_novelty_rejections != ignored_rejections:
        missing = sorted(ignored_rejections - observed_novelty_rejections)
        extra = sorted(observed_novelty_rejections - ignored_rejections)
        raise ReportError(
            "the private measurement review override does not equal the retained novelty "
            f"rejection union (missing={missing}, extra={extra})"
        )


def _canary_artifact_path(
    evidence: Mapping[str, Any], project_root: Path, name: str, label: str
) -> Path:
    artifact_root_raw = evidence.get("artifact_root")
    artifacts = evidence.get("artifacts")
    descriptor = artifacts.get(name) if isinstance(artifacts, Mapping) else None
    if (
        not isinstance(artifact_root_raw, str)
        or not artifact_root_raw
        or not isinstance(descriptor, Mapping)
        or set(descriptor) != {"path", "sha256"}
        or not isinstance(descriptor.get("path"), str)
        or not descriptor["path"]
        or Path(str(descriptor["path"])).is_absolute()
        or ".." in Path(str(descriptor["path"])).parts
        or not _hex_digest(descriptor.get("sha256"))
    ):
        raise ReportError(f"{label} artifact descriptor is malformed")
    project = project_root.resolve()
    artifact_root = (project / artifact_root_raw).resolve()
    path = (artifact_root / str(descriptor["path"])).resolve()
    try:
        artifact_root.relative_to(project)
        path.relative_to(artifact_root)
    except ValueError as error:
        raise ReportError(f"{label} artifact escapes its authenticated root") from error
    if path.is_symlink() or not path.is_file() or _file_digest(path) != descriptor["sha256"]:
        raise ReportError(f"{label} artifact bytes failed authentication")
    return path


def _validate_token_control_canary(
    inputs: ReportInputs,
    freeze: Mapping[str, Any],
    *,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    """Authenticate the private synthetic sanitized-crossing token canary."""

    frozen = inputs.config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        raise ReportError("token-control canary has no frozen environment descriptor")
    descriptor = frozen.get("token_control_canary")
    environment_descriptor = inputs.environment.get("token_control_canary")
    if (
        not isinstance(descriptor, Mapping)
        or not isinstance(environment_descriptor, Mapping)
        or dict(descriptor) != dict(environment_descriptor)
        or set(descriptor) != {"path", "sha256", "status"}
        or descriptor.get("path") != TOKEN_CONTROL_CANARY_PATH
        or descriptor.get("status") != "passed"
        or not _hex_digest(descriptor.get("sha256"))
    ):
        raise ReportError(
            "token-control canary descriptor disagrees across config and environment"
        )
    evidence_path = _find_repository_file(
        inputs.benchmark_root,
        str(descriptor["path"]),
        "token-control canary evidence",
    )
    _require_sha_match(
        evidence_path,
        descriptor["sha256"],
        "token-control canary evidence",
    )
    try:
        release_relative = evidence_path.relative_to(inputs.benchmark_root).as_posix()
    except ValueError as error:
        raise ReportError(
            "token-control canary evidence is outside the benchmark release"
        ) from error
    if _release_file_hashes(inputs).get(release_relative) != descriptor["sha256"]:
        raise ReportError(
            "token-control canary evidence is not authenticated by the release manifest"
        )
    evidence = inputs.evidence.get(TOKEN_CONTROL_CANARY_KEY)
    disk_evidence = _object(evidence_path, "token-control canary evidence")
    if not isinstance(evidence, Mapping) or dict(evidence) != dict(disk_evidence):
        raise ReportError("loaded token-control canary evidence disagrees with its file")
    if (
        evidence.get("schema_version") != token_canary.EVIDENCE_SCHEMA_VERSION
        or evidence.get("kind") != token_canary.EVIDENCE_KIND
        or evidence.get("status") != "passed"
        or evidence.get("public_release") is not False
        or evidence.get("scored") is not False
        or evidence.get("matrix_assignment") is not False
        or evidence.get("synthetic_input") is not True
        or evidence.get("benchmark_task_bytes_used") is not False
        or evidence.get("canary_id") != token_canary.CANARY_ID
        or evidence.get("benchmark_id") != inputs.config.get("benchmark_id")
    ):
        raise ReportError("token-control canary evidence has a failed or invalid status")
    limits = inputs.config.get("limits")
    token_limit = limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
    if not isinstance(token_limit, int) or isinstance(token_limit, bool) or token_limit <= 0:
        raise ReportError("token-control canary has no frozen token ceiling")
    expected_agent = {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "binary_sha256": frozen.get("agent_binary_sha256"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
    }
    if frozen.get("ultra_orchestration") is not None:
        expected_agent["ultra_orchestration"] = frozen.get("ultra_orchestration")
    project_root = inputs.benchmark_root.parent.parent
    try:
        verified = token_canary.validate_attestation_document(
            evidence,
            project_root=project_root,
            expected_benchmark_id=str(inputs.config.get("benchmark_id")),
            expected_agent=expected_agent,
            expected_frozen_token_limit=token_limit,
        )
    except (OSError, BenchmarkToolError) as error:
        raise ReportError(
            f"synthetic token-control canary failed authentication: {error}"
        ) from error
    token_record_path = _canary_artifact_path(
        evidence, project_root, "record", "token-control runner record"
    )
    token_gate_path = _canary_artifact_path(
        evidence, project_root, "provider_gate", "token-control provider gate"
    )
    token_record = _object(token_record_path, "token-control runner record")
    token_gate_authentication = _authenticate_provider_gate_record(
        token_record,
        artifact_path=token_gate_path,
        label="token-control canary",
    )
    _validate_token_canary_provider_gate_shape(
        token_gate_authentication, "token-control canary"
    )
    _authenticate_token_canary_production_freeze(
        project_root,
        evidence,
        prompt_protocol=prompt_protocol,
        execution_components=execution_components,
    )
    summary = {
        "path": descriptor["path"],
        "sha256": descriptor["sha256"],
        **verified,
    }
    frozen_summary = freeze.get("token_control_canary")
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
        not isinstance(frozen_summary, Mapping)
        or dict(frozen_summary) != summary
        or set(summary) != _TOKEN_CANARY_SUMMARY_FIELDS
        or summary.get("status") != "passed"
        or type(summary.get("canary_limit_tokens")) is not int
        or summary.get("canary_limit_tokens") != token_canary.DEFAULT_CANARY_TOKEN_LIMIT
        or type(summary.get("first_crossing_tokens")) is not int
        or summary.get("first_crossing_tokens") < summary.get("canary_limit_tokens")
        or type(summary.get("final_endpoint_tokens")) is not int
        or summary.get("final_endpoint_tokens") != summary.get("first_crossing_tokens")
        or summary.get("first_crossing_tokens")
        != token_gate_authentication.get("completed_tokens")
        or summary.get("final_endpoint_tokens")
        != token_gate_authentication.get("completed_tokens")
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
        or not _valid_token_canary_prompt_release(summary.get("prompt_release"))
        or not isinstance(projection, Mapping)
        or set(projection) != expected_projection_fields
        or projection.get("accounting_projection_schema_version")
        != token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or projection.get("provider_gate_protocol") != runner.PROVIDER_GATE_PROTOCOL
        or projection.get("provider_gate_record_sha256")
        != token_gate_authentication.get("record_sha256")
        or projection.get("provider_gate_close_reason")
        != token_gate_authentication.get("close_reason")
        or projection.get("provider_gate_response_ids")
        != token_gate_authentication.get("response_ids")
        or projection.get("provider_gate_deliveries_reconciled")
        is not token_gate_authentication.get("appserver_deliveries_reconciled")
        or projection.get("provider_gate_setup_requests_empty")
        is not token_gate_authentication.get("setup_requests_empty")
        or projection.get("provider_requests_quiescent")
        is not token_gate_authentication.get("provider_requests_quiescent")
        or projection.get("adapter_teardown_complete")
        is not token_gate_authentication.get("adapter_teardown_complete")
        or projection.get("spawn_binding_source") != ACCOUNTING_SPAWN_BINDING_SOURCE
        or projection.get("root_expected_cumulative_baseline") != zero
        or projection.get("root_cumulative_projection_status")
        not in {"missing_cumulative", "cumulative_projection_mismatch"}
        or projection.get("root_only") is not True
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
        or not _hex_digest(projection.get("projection_payload_sha256"))
        or _document_digest(
            {
                key: value
                for key, value in projection.items()
                if key != "projection_payload_sha256"
            }
        )
        != projection.get("projection_payload_sha256")
        or not _hex_digest(summary.get("source_separation_audit_sha256"))
    ):
        raise ReportError(
            "frozen-run verification has an invalid token-control canary summary"
        )
    _validate_canary_projection_provider_reconciliation(
        projection, token_record, token_gate_authentication, "token-control canary"
    )
    artifacts = summary.get("artifacts")
    if not isinstance(artifacts, Mapping) or set(artifacts) != set(
        token_canary.ARTIFACT_LABELS
    ):
        raise ReportError("token-control canary artifact summary is incomplete")
    return evidence, summary


def _validate_ultra_orchestration_canary(
    inputs: ReportInputs,
    freeze: Mapping[str, Any],
    *,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Authenticate the synthetic delegation and first-valid-proof barrier probe."""

    frozen = inputs.config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        raise ReportError("Ultra canary has no frozen environment descriptor")
    config_descriptor = frozen.get("ultra_orchestration_canary")
    environment_descriptor = inputs.environment.get("ultra_orchestration_canary")
    if (
        not isinstance(config_descriptor, Mapping)
        or not isinstance(environment_descriptor, Mapping)
        or dict(config_descriptor) != dict(environment_descriptor)
        or set(config_descriptor) != {"path", "sha256", "status"}
        or config_descriptor.get("path") != ULTRA_ORCHESTRATION_CANARY_PATH
        or config_descriptor.get("status") != "passed"
        or not _hex_digest(config_descriptor.get("sha256"))
    ):
        raise ReportError(
            "Ultra orchestration canary descriptor is not one matching frozen pass"
        )
    evidence_path = _find_repository_file(
        inputs.benchmark_root,
        config_descriptor["path"],
        "Ultra orchestration canary evidence",
    )
    try:
        release_relative = evidence_path.relative_to(inputs.benchmark_root).as_posix()
    except ValueError as error:
        raise ReportError(
            "Ultra orchestration canary evidence is outside the benchmark release"
        ) from error
    _require_sha_match(
        evidence_path,
        config_descriptor["sha256"],
        "Ultra orchestration canary evidence",
    )
    evidence_document = _object(
        evidence_path, "Ultra orchestration canary evidence"
    )
    if _release_file_hashes(inputs).get(release_relative) != config_descriptor["sha256"]:
        raise ReportError(
            "Ultra orchestration canary evidence is not authenticated by the release"
        )
    limits = inputs.config.get("limits")
    token_limit = limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
    if not isinstance(token_limit, int) or isinstance(token_limit, bool) or token_limit <= 0:
        raise ReportError("Ultra orchestration canary has no frozen token ceiling")
    expected_agent = {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "binary_sha256": frozen.get("agent_binary_sha256"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
        "ultra_orchestration": frozen.get("ultra_orchestration"),
    }
    project_root = inputs.benchmark_root.parent.parent
    try:
        summary = ultra_canary.verify_frozen_attestation(
            project_root,
            config_descriptor,
            expected_benchmark_id=str(inputs.config.get("benchmark_id")),
            expected_agent=expected_agent,
            expected_token_limit=token_limit,
            expected_prompt_protocol=prompt_protocol,
            expected_execution_components=execution_components,
        )
    except BenchmarkToolError as error:
        raise ReportError(f"Ultra orchestration canary failed authentication: {error}") from error
    ultra_record_path = _canary_artifact_path(
        evidence_document,
        project_root,
        "runner_record",
        "Ultra orchestration runner record",
    )
    ultra_gate_path = _canary_artifact_path(
        evidence_document,
        project_root,
        "provider_gate",
        "Ultra orchestration provider gate",
    )
    ultra_record = _object(ultra_record_path, "Ultra orchestration runner record")
    ultra_gate_authentication = _authenticate_provider_gate_record(
        ultra_record,
        artifact_path=ultra_gate_path,
        label="Ultra orchestration canary",
    )
    frozen_summary = freeze.get("ultra_orchestration_canary")
    barrier = summary.get("barrier") if isinstance(summary, Mapping) else None
    dependency_audit = (
        summary.get("dependency_audit") if isinstance(summary, Mapping) else None
    )
    prompt_release = (
        summary.get("prompt_release") if isinstance(summary, Mapping) else None
    )
    if (
        not isinstance(frozen_summary, Mapping)
        or dict(frozen_summary) != dict(summary)
        or type(summary.get("thread_count")) is not int
        or type(summary.get("observed_descendant_thread_count")) is not int
        or type(summary.get("positive_usage_descendant_thread_count")) is not int
        or type(summary.get("response_count")) is not int
        or type(summary.get("total_model_tokens")) is not int
        or summary.get("response_count")
        != ultra_gate_authentication.get("response_count")
        or summary.get("total_model_tokens")
        != ultra_gate_authentication.get("completed_tokens")
        or summary.get("drain_complete") is not False
        or summary.get("measurement_exact") is not True
        or summary.get("submission_boundary_exact") is not True
        or not isinstance(barrier, Mapping)
        or barrier.get("retained_read_only") is not True
        or not isinstance(dependency_audit, Mapping)
        or dependency_audit.get("complete") is not True
        or not _hex_digest(dependency_audit.get("helper_sha256"))
        or not _hex_digest(dependency_audit.get("command_sha256"))
        or dependency_audit.get("library_use") is not False
        or dependency_audit.get("library_declarations") != []
        or dependency_audit.get("target_seen") is not True
        or dependency_audit.get("semantic_type_equal") is not True
        or not isinstance(prompt_release, Mapping)
        or prompt_release.get("schema_version") != 1
        or prompt_release.get("protocol_version")
        != PROMPT_RELEASE_PROTOCOL_VERSION
        or prompt_release.get("authenticated") is not True
        or prompt_release.get("timing_exact") is not True
        or prompt_release.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or prompt_release.get("startup_timeout_seconds") != 120
        or prompt_release.get("artifact_count") != 3
        or prompt_release.get("artifacts_reauthenticated") is not True
        or prompt_release.get("request_publication_timing_verified") is not True
        or not isinstance(prompt_release.get("released_at_monotonic_ns"), int)
        or isinstance(prompt_release.get("released_at_monotonic_ns"), bool)
        or not isinstance(
            prompt_release.get("measurement_deadline_monotonic_ns"), int
        )
        or isinstance(
            prompt_release.get("measurement_deadline_monotonic_ns"), bool
        )
        or not isinstance(
            prompt_release.get("request_published_at_monotonic_ns"), int
        )
        or isinstance(
            prompt_release.get("request_published_at_monotonic_ns"), bool
        )
        or not (
            0 < prompt_release["released_at_monotonic_ns"]
            <= prompt_release["request_published_at_monotonic_ns"]
            < prompt_release["measurement_deadline_monotonic_ns"]
        )
    ):
        raise ReportError(
            "frozen-run verification lacks the exact blocked Ultra submission canary"
        )
    outer_exec_observed = barrier.get("outer_raw_item_observed_at_monotonic_ns")
    if (
        type(outer_exec_observed) is not int
        or outer_exec_observed < prompt_release["released_at_monotonic_ns"]
        or outer_exec_observed > prompt_release["request_published_at_monotonic_ns"]
    ):
        raise ReportError(
            "Ultra orchestration canary outer-exec timer predates prompt release"
        )
    _validate_nested_submission_wire_v5(
        barrier,
        "Ultra orchestration canary barrier",
    )
    _validate_submission_event_order_v5(
        barrier,
        "Ultra orchestration canary barrier",
        require_event_timestamps=True,
    )
    gate_close = barrier.get("provider_gate_close")
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
        raise ReportError("Ultra orchestration canary lacks its schema-v5 gate close")
    projection = summary.get("accounting_projection")
    if not isinstance(projection, Mapping):
        raise ReportError("Ultra orchestration canary lacks projection-v6 evidence")
    if (
        projection.get("accounting_projection_schema_version")
        != ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or projection.get("provider_gate_protocol") != runner.PROVIDER_GATE_PROTOCOL
        or projection.get("provider_gate_record_sha256")
        != ultra_gate_authentication.get("record_sha256")
        or projection.get("provider_gate_close_reason")
        != ultra_gate_authentication.get("close_reason")
        or projection.get("provider_gate_response_ids")
        != ultra_gate_authentication.get("response_ids")
        or projection.get("provider_gate_deliveries_reconciled")
        is not ultra_gate_authentication.get("appserver_deliveries_reconciled")
        or projection.get("provider_gate_setup_requests_empty")
        is not ultra_gate_authentication.get("setup_requests_empty")
        or projection.get("provider_requests_quiescent")
        is not ultra_gate_authentication.get("provider_requests_quiescent")
        or projection.get("adapter_teardown_complete")
        is not ultra_gate_authentication.get("adapter_teardown_complete")
        or ultra_gate_authentication.get("endpoint") != "accepted_provider_gate_close"
    ):
        raise ReportError("Ultra orchestration canary projection-v6 gate binding is invalid")
    _validate_canary_projection_provider_reconciliation(
        projection, ultra_record, ultra_gate_authentication, "Ultra orchestration canary"
    )
    raw_ids = _projection_ids(projection.get("raw_spawn_call_ids"), "canary raw IDs")
    activity_ids = _projection_ids(
        projection.get("activity_spawn_call_ids"), "canary activity IDs"
    )
    collab_ids = _projection_ids(
        projection.get("collab_spawn_call_ids"), "canary collaboration IDs"
    )
    resolved_ids = _projection_ids(
        projection.get("resolved_spawn_call_ids"), "canary resolved IDs"
    )
    failed_ids = _projection_ids(
        projection.get("failed_spawn_call_ids"), "canary failed IDs"
    )
    blocked_ids = _projection_ids(
        projection.get("policy_blocked_spawn_call_ids"),
        "canary policy-blocked IDs",
    )
    unresolved_ids = _projection_ids(
        projection.get("unresolved_spawn_call_ids"), "canary unresolved IDs"
    )
    unsupported_ids = _projection_ids(
        projection.get("unsupported_spawn_call_ids"), "canary unsupported IDs"
    )
    child_ids = _projection_ids(
        projection.get("inference_child_thread_ids"), "canary child IDs"
    )
    raw_threads = projection.get("thread_accounting")
    known_threads = {
        str(thread.get("thread_id"))
        for thread in raw_threads
        if isinstance(thread, Mapping)
        and isinstance(thread.get("thread_id"), str)
        and thread.get("thread_id")
    } if isinstance(raw_threads, list) else set()
    calls = _rederive_ultra_fork_policy(
        projection,
        raw_ids=raw_ids,
        activity_ids=activity_ids,
        collab_ids=collab_ids,
        resolved_ids=resolved_ids,
        failed_ids=failed_ids,
        unsupported_ids=unsupported_ids,
        known_thread_ids=known_threads,
        response_ids=None,
    )
    if (
        len(resolved_ids) != 1
        or len(blocked_ids) != 2
        or failed_ids != blocked_ids
        or raw_ids != resolved_ids | blocked_ids
        or unresolved_ids
        or len(child_ids) != 1
    ):
        raise ReportError("Ultra orchestration canary has the wrong V8 fork topology")
    allowed = calls[next(iter(resolved_ids))]
    root_id = allowed.get("parent_thread_id")
    blocked_calls = [calls[call_id] for call_id in sorted(blocked_ids)]
    if (
        allowed.get("fork_turns") != "all"
        or not isinstance(root_id, str)
        or {call.get("parent_thread_id") for call in blocked_calls}
        != {root_id, next(iter(child_ids))}
        or any(call.get("fork_turns") != "3" for call in blocked_calls)
    ):
        raise ReportError("Ultra orchestration canary did not prove both V8 denials")
    return summary


def _validate_freeze_link(inputs: ReportInputs, result_check: Mapping[str, Any]) -> None:
    """Authenticate the startup check used by every accepted run."""

    freeze = inputs.freeze_check
    digest = _document_digest(freeze)
    frozen = inputs.config.get("frozen_environment")
    lean_environment = inputs.environment.get("lean")
    if not isinstance(frozen, Mapping) or not isinstance(lean_environment, Mapping):
        raise ReportError("frozen environment metadata is missing")
    hardware_policy = frozen.get("hardware_matching_policy")
    recorded_freeze_digest = result_check.get("freeze_check_sha256")
    if hardware_policy is None:
        if not _hex_digest(recorded_freeze_digest) or recorded_freeze_digest != digest:
            raise ReportError(
                "analysis is not linked to the adjacent frozen-run verification"
            )
    else:
        matrix = result_check.get("matrix_record_authentication")
        evidence = matrix.get("run_evidence") if isinstance(matrix, Mapping) else None
        embedded_digests = sorted(
            {
                str(wrapper.get("freeze_check_sha256"))
                for item in evidence or []
                if isinstance(item, Mapping)
                and isinstance(item.get("record"), Mapping)
                and isinstance(
                    wrapper := item["record"].get("frozen_run_verification"),
                    Mapping,
                )
                and _hex_digest(wrapper.get("freeze_check_sha256"))
            }
        )
        aggregate = _document_digest({"freeze_check_sha256s": embedded_digests})
        if (
            hardware_policy != getattr(run_matrix, "HARDWARE_MATCHING_POLICY", None)
            or inputs.environment.get("hardware_matching_policy") != hardware_policy
            or not embedded_digests
            or digest not in embedded_digests
            or recorded_freeze_digest != aggregate
        ):
            raise ReportError(
                "analysis is not linked to the authenticated paired-hardware freezes"
            )
    if (
        freeze.get("schema_version") != 1
        or freeze.get("kind") != "highambench-frozen-run-verification"
        or freeze.get("ok") is not True
        or freeze.get("benchmark_id") != inputs.config.get("benchmark_id")
        or freeze.get("environment_id") != frozen.get("environment_id")
        or freeze.get("environment_bundle_sha256")
        != frozen.get("environment_bundle_sha256")
    ):
        raise ReportError("the frozen-run verification has the wrong identity or status")

    expected_metadata = {
        "config": _document_digest(inputs.config),
        "environment": _document_digest(inputs.environment),
        "manifest": _document_digest(inputs.manifest),
        "run_order": _document_digest(inputs.run_order),
    }
    recorded_metadata = freeze.get("metadata_document_sha256")
    if not isinstance(recorded_metadata, Mapping) or any(
        recorded_metadata.get(name) != value for name, value in expected_metadata.items()
    ):
        raise ReportError("the frozen-run verification cites stale metadata")

    release = freeze.get("release_manifest")
    release_relative = _artifact_path_below_benchmark(
        inputs, frozen.get("release_manifest"), "evaluation release manifest"
    )
    release_count = len(inputs.release_manifest.get("files", []))
    release_verification = (
        release.get("verification") if isinstance(release, Mapping) else None
    )
    if (
        not isinstance(release, Mapping)
        or release.get("path") != release_relative
        or release.get("sha256") != frozen.get("release_manifest_sha256")
        or release.get("file_count") != release_count
        or not isinstance(release_verification, Mapping)
        or release_verification.get("ok") is not True
        or release_verification.get("expected") != release_count
        or release_verification.get("verified") != release_count
        or release_verification.get("missing") != []
        or release_verification.get("changed") != []
    ):
        raise ReportError("the frozen-run verification has incomplete release evidence")

    compiled = freeze.get("compiled_environment_summary")
    packages = inputs.compiled_environment_summary.get("packages")
    toolchain = inputs.compiled_environment_summary.get("toolchain")
    package_file_count = (
        sum(
            package.get("file_count", -1) if isinstance(package, Mapping) else -1
            for package in packages
        )
        if isinstance(packages, list)
        else -1
    )
    if (
        not isinstance(compiled, Mapping)
        or compiled.get("path") != frozen.get("compiled_environment_summary")
        or compiled.get("sha256") != frozen.get("compiled_environment_summary_sha256")
        or not isinstance(toolchain, Mapping)
        or compiled.get("toolchain_file_count") != toolchain.get("file_count")
        or not isinstance(packages, list)
        or compiled.get("package_count") != len(packages)
        or compiled.get("package_file_count") != package_file_count
    ):
        raise ReportError("the frozen-run verification has incomplete compiled-tree evidence")

    freeze_lean = freeze.get("lean")
    freeze_agent = freeze.get("agent")
    freeze_python = freeze.get("python")
    freeze_packages = freeze.get("packages_runtime")
    token_control = freeze.get("token_control")
    freeze_limits = freeze.get("limits")
    freeze_bubblewrap = freeze.get("bubblewrap")
    freeze_host = freeze.get("host_class")
    isolation = inputs.environment.get("isolation")
    environment_host = inputs.environment.get("host_class")
    limits = inputs.config.get("limits")
    limit_tokens = limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
    config_token_control = inputs.config.get("token_control")
    environment_token_control = inputs.environment.get("token_control")
    config_advisory = (
        config_token_control.get("advisory_rollout_budget")
        if isinstance(config_token_control, Mapping)
        else None
    )
    freeze_advisory = (
        token_control.get("advisory_rollout_budget")
        if isinstance(token_control, Mapping)
        else None
    )
    if (
        config_token_control != environment_token_control
        or not _valid_token_control(
            config_token_control, limit_tokens, require_feature_row=True
        )
        or not _valid_token_control(
            token_control, limit_tokens, require_feature_row=True
        )
        or not isinstance(config_advisory, Mapping)
        or not isinstance(freeze_advisory, Mapping)
        or freeze_advisory.get("feature_row")
        != config_advisory.get("feature_row")
    ):
        raise ReportError(
            "the frozen-run verification lacks the required live token-control evidence"
        )
    if (
        not isinstance(freeze_lean, Mapping)
        or freeze_lean.get("version") != lean_environment.get("version")
        or freeze_lean.get("commit") != lean_environment.get("commit")
        or freeze_lean.get("binary_sha256") != lean_environment.get("binary_sha256")
        or freeze_lean.get("mathlib_commit") != lean_environment.get("mathlib_commit")
        or freeze_lean.get("numstability_commit")
        != lean_environment.get("numstability_commit")
        or not isinstance(freeze_agent, Mapping)
        or freeze_agent.get("id") != frozen.get("agent_id")
        or freeze_agent.get("version") != frozen.get("agent_version")
        or freeze_agent.get("binary_sha256") != frozen.get("agent_binary_sha256")
        or freeze_agent.get("model") != frozen.get("model_version")
        or freeze_agent.get("reasoning_effort")
        != frozen.get("model_reasoning_effort")
        or not isinstance(freeze_python, Mapping)
        or freeze_python.get("version") != frozen.get("python_version")
        or freeze_python.get("binary_sha256") != frozen.get("python_binary_sha256")
        or not isinstance(limits, Mapping)
        or not isinstance(freeze_limits, Mapping)
        or freeze_limits.get("wall_clock_seconds") != limits.get("wall_clock_seconds")
        or freeze_limits.get("total_model_tokens") != limits.get("total_model_tokens")
        or not isinstance(freeze_bubblewrap, Mapping)
        or not isinstance(isolation, Mapping)
        or freeze_bubblewrap.get("version") != isolation.get("bubblewrap_version")
        or freeze_bubblewrap.get("binary_sha256")
        != isolation.get("bubblewrap_binary_sha256")
    ):
        raise ReportError("the frozen-run verification disagrees with the compiled setup")

    try:
        production_prompt_protocol, production_execution_components = (
            run_matrix.production_freeze_bindings(inputs.config, inputs.environment)
        )
    except BenchmarkToolError as error:
        raise ReportError(
            f"production prompt/execution freeze bindings are invalid: {error}"
        ) from error
    _validate_token_control_canary(
        inputs,
        freeze,
        prompt_protocol=production_prompt_protocol,
        execution_components=production_execution_components,
    )
    _validate_ultra_orchestration_canary(
        inputs,
        freeze,
        prompt_protocol=production_prompt_protocol,
        execution_components=production_execution_components,
    )

    runtime = inputs.environment.get("runtime")
    runtime_python = runtime.get("python") if isinstance(runtime, Mapping) else None
    runtime_files = inputs.packages_runtime_manifest.get("files")
    packages_verification = (
        freeze_packages.get("verification")
        if isinstance(freeze_packages, Mapping)
        else None
    )
    packages_count = len(runtime_files) if isinstance(runtime_files, list) else -1
    source_count = sum(
        str(entry.get("path", "")).endswith(".lean")
        for entry in runtime_files
        if isinstance(entry, Mapping)
    ) if isinstance(runtime_files, list) else -1
    olean_count = sum(
        str(entry.get("path", "")).endswith(".olean")
        for entry in runtime_files
        if isinstance(entry, Mapping)
    ) if isinstance(runtime_files, list) else -1
    compiled_support_count = sum(
        str(entry.get("path", "")).endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES)
        for entry in runtime_files
        if isinstance(entry, Mapping)
    ) if isinstance(runtime_files, list) else -1
    if (
        not isinstance(runtime, Mapping)
        or not isinstance(runtime_python, Mapping)
        or freeze_python != runtime_python
        or not isinstance(freeze_packages, Mapping)
        or freeze_packages.get("path") != frozen.get("packages_runtime_manifest")
        or freeze_packages.get("sha256")
        != frozen.get("packages_runtime_manifest_sha256")
        or freeze_packages.get("file_count") != packages_count
        or freeze_packages.get("source_file_count") != source_count
        or freeze_packages.get("olean_file_count") != olean_count
        or freeze_packages.get("compiled_support_file_count")
        != compiled_support_count
        or source_count + olean_count + compiled_support_count != packages_count
        or not isinstance(packages_verification, Mapping)
        or packages_verification.get("ok") is not True
        or packages_verification.get("expected") != packages_count
        or packages_verification.get("verified") != packages_count
        or packages_verification.get("missing") != []
        or packages_verification.get("changed") != []
    ):
        raise ReportError("the frozen-run verification has incomplete pruned-package evidence")
    host_fields = {
        "kernel",
        "virtualization",
        "cpu_vendor",
        "processor",
        "cpu_family",
        "cpu_model",
        "cpu_stepping",
        "online_logical_cpus",
        "allocated_physical_cores",
        "allocated_sockets",
        "allocated_threads_per_core",
        "visible_memory_bytes",
        "allocation_memory_limit_bytes",
        "slurm_num_nodes",
        "slurm_num_cpus",
        "slurm_num_tasks",
        "slurm_cpus_per_task",
        "slurm_allocated_memory_bytes",
    }
    exact_host_fields = host_fields
    if hardware_policy is not None:
        policy_host = hardware_policy.get("frozen_host_class")
        exact_host_fields = set(
            policy_host.get("exact_fields", [])
            if isinstance(policy_host, Mapping)
            else []
        )
    invalid_host = (
        not isinstance(freeze_host, Mapping)
        or not isinstance(environment_host, Mapping)
        or set(freeze_host) != host_fields
    )
    if hardware_policy is not None and freeze.get(
        "hardware_matching_policy"
    ) != hardware_policy:
        invalid_host = True
    if not invalid_host and any(
        environment_host.get(field) != freeze_host.get(field)  # type: ignore[union-attr]
        for field in exact_host_fields
    ):
        invalid_host = True
    if invalid_host:
        raise ReportError(
            "the frozen-run verification violates the paired-hardware invariants"
            if hardware_policy is not None
            else "the frozen-run verification disagrees with the measured host"
        )

    selected = result_check.get("selected_final_record_count")
    network_runs = result_check.get("network_violation_run_count")
    integrity_failures = result_check.get("network_integrity_failure_count")
    if (
        not isinstance(selected, int)
        or isinstance(selected, bool)
        or not isinstance(network_runs, int)
        or isinstance(network_runs, bool)
        or network_runs < 0
        or network_runs > selected
        or integrity_failures != 0
    ):
        raise ReportError("result set has incomplete or failed network-marker evidence")


def _validated_prompt_protocol(
    inputs: ReportInputs, result_check: Mapping[str, Any] | None = None
) -> Mapping[str, Any] | None:
    """Authenticate the optional signposted-library prompt treatment."""

    frozen = inputs.config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        raise ReportError("configuration metadata has no frozen environment")
    protocol = frozen.get("prompt_protocol")
    environment_agent = inputs.environment.get("agent")
    environment_protocol = (
        environment_agent.get("prompt_protocol")
        if isinstance(environment_agent, Mapping)
        else None
    )
    freeze_protocol = inputs.freeze_check.get("prompt_protocol")
    if protocol is None:
        if environment_protocol is not None or freeze_protocol is not None:
            raise ReportError("legacy prompt metadata disagrees across frozen records")
        if result_check is not None:
            summary = result_check.get("prompt_provenance")
            if isinstance(summary, Mapping) and summary.get("signposted") is True:
                raise ReportError("legacy result set claims signposted prompt provenance")
        return None
    if (
        not isinstance(protocol, Mapping)
        or environment_protocol != protocol
        or freeze_protocol != protocol
    ):
        raise ReportError("signposted prompt protocol disagrees across frozen records")
    expected_order = [
        "common_prompt",
        "condition_L_supplement_if_condition_L",
        "task_context",
        "fixed_target",
    ]
    if (
        protocol.get("version") != "signposted-library-v1"
        or protocol.get("composition_order") != expected_order
        or protocol.get("N_receives_condition_supplement") is not False
        or protocol.get("relevant_theorem_or_module_hints_supplied") is not False
    ):
        raise ReportError("signposted prompt protocol policy is invalid")
    common = protocol.get("common_prompt")
    supplements = protocol.get("condition_supplements")
    supplement = supplements.get("L") if isinstance(supplements, Mapping) else None
    if (
        not isinstance(common, Mapping)
        or common.get("path") != "agent_prompt.md"
        or common.get("sha256") != frozen.get("prompt_sha256")
        or type(common.get("bytes")) is not int
        or common.get("bytes") <= 0
        or not isinstance(supplements, Mapping)
        or set(supplements) != {"L"}
        or not isinstance(supplement, Mapping)
        or supplement.get("path") != "condition_prompts/L.md"
        or not _hex_digest(supplement.get("sha256"))
        or type(supplement.get("bytes")) is not int
        or supplement.get("bytes") <= 0
    ):
        raise ReportError("signposted prompt descriptors are invalid")
    common_path = inputs.benchmark_root / "agent_prompt.md"
    supplement_relative = _artifact_path_below_benchmark(
        inputs, supplement.get("path"), "condition-L prompt supplement"
    )
    supplement_path = inputs.benchmark_root / supplement_relative
    if (
        common_path.stat().st_size != common.get("bytes")
        or supplement_path.stat().st_size != supplement.get("bytes")
    ):
        raise ReportError("signposted prompt byte count changed after freezing")
    _require_sha_match(common_path, common.get("sha256"), "common prompt")
    _require_sha_match(
        supplement_path,
        supplement.get("sha256"),
        "condition-L prompt supplement",
    )
    release_hashes = _release_file_hashes(inputs)
    if (
        release_hashes.get("agent_prompt.md") != common.get("sha256")
        or release_hashes.get("condition_prompts/L.md") != supplement.get("sha256")
    ):
        raise ReportError("signposted prompt files are not authenticated by the release")
    if result_check is not None:
        summary = result_check.get("prompt_provenance")
        selected = result_check.get("selected_final_record_count")
        if (
            not isinstance(selected, int)
            or isinstance(selected, bool)
            or not isinstance(summary, Mapping)
            or summary.get("protocol_version") != "signposted-library-v1"
            or summary.get("signposted") is not True
            or summary.get("verified_final_runs") != selected
            or summary.get("expected_final_runs") != selected
            or summary.get("condition_n_supplement_count") != 0
            or summary.get("condition_l_supplement_count") != selected // 2
            or summary.get("complete") is not True
        ):
            raise ReportError("per-run signposted prompt provenance is incomplete")
    return protocol


def _projection_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ReportError(f"incomplete analysis: {label} is not a nonnegative integer")
    return value


def _projection_breakdown(value: Any, label: str) -> dict[str, int]:
    if not isinstance(value, Mapping):
        raise ReportError(f"incomplete analysis: {label} is not a token breakdown")
    result = {
        field: _projection_int(value.get(field), f"{label}.{field}")
        for field in ACCOUNTING_TOKEN_FIELDS
    }
    if (
        result["cached_input_tokens"] > result["input_tokens"]
        or result["cache_write_input_tokens"] > result["input_tokens"]
        or result["reasoning_output_tokens"] > result["output_tokens"]
        or result["total_tokens"]
        != result["input_tokens"] + result["output_tokens"]
    ):
        raise ReportError(f"incomplete analysis: {label} is inconsistent")
    return result


def _projection_optional_breakdown(
    value: Any, label: str
) -> dict[str, int] | None:
    return None if value is None else _projection_breakdown(value, label)


def _projection_ids(value: Any, label: str) -> set[str]:
    if (
        not isinstance(value, list)
        or any(not isinstance(item, str) or not item for item in value)
        or value != sorted(set(value))
    ):
        raise ReportError(
            f"incomplete analysis: {label} is not a sorted identifier set"
        )
    return set(value)


def _hook_trust_report_rows(
    projection: Mapping[str, Any],
) -> tuple[tuple[str, Any, str], ...]:
    """Render the three independently authenticated hook-trust facts."""

    policy = projection.get("fork_policy")
    if not isinstance(policy, Mapping):
        raise ReportError("validated Ultra canary fork policy is missing at render time")
    if (
        policy.get("hook_trust_bypass_cli_flag_present") is not True
        or policy.get("hook_trust_bypass_thread_config")
        != {"bypass_hook_trust": True}
        or policy.get("hook_trust_bypass_effective_source")
        != "thread_start_config"
    ):
        raise ReportError("validated Ultra canary hook-trust split is stale")
    return (
        (
            "Hook-trust CLI flag present",
            True,
            "The frozen app-server command carries the hook-trust-bypass flag; this records presence, not the pinned server's effective source.",
        ),
        (
            "Hook-trust thread config",
            json.dumps(
                policy["hook_trust_bypass_thread_config"],
                sort_keys=True,
                separators=(",", ":"),
            ),
            "The authenticated thread/start request supplies bypass_hook_trust=true.",
        ),
        (
            "Effective hook-trust source",
            policy["hook_trust_bypass_effective_source"],
            "The pinned app-server obtains the effective bypass from thread_start_config, not from CLI presence alone.",
        ),
    )


def _rederive_ultra_fork_policy(
    value: Mapping[str, Any],
    *,
    raw_ids: set[str],
    activity_ids: set[str],
    collab_ids: set[str],
    resolved_ids: set[str],
    failed_ids: set[str],
    unsupported_ids: set[str],
    known_thread_ids: set[str] | None,
    response_ids: set[str] | None,
    allow_incomplete: bool = False,
) -> dict[str, Mapping[str, Any]]:
    """Independently rederive every authenticated Ultra hook decision."""

    policy_blocked_ids = _projection_ids(
        value.get("policy_blocked_spawn_call_ids"), "policy-blocked spawn IDs"
    )
    hook_observed_ids = _projection_ids(
        value.get("hook_observed_spawn_call_ids"), "hook-observed spawn IDs"
    )
    hook_allowed_ids = _projection_ids(
        value.get("hook_allowed_spawn_call_ids"), "hook-allowed spawn IDs"
    )
    hook_blocked_ids = _projection_ids(
        value.get("hook_blocked_spawn_call_ids"), "hook-blocked spawn IDs"
    )
    hook_invalid_ids = _projection_ids(
        value.get("hook_invalid_spawn_call_ids"), "hook-invalid spawn IDs"
    )
    policy = value.get("fork_policy")
    expected_static = ultra_canary.codex_isolated.ultra_fork_policy_static_record()
    if (
        not isinstance(policy, Mapping)
        or set(policy) != set(expected_static) | {"call_evidence", "complete"}
    ):
        raise ReportError("incomplete analysis: Ultra fork-policy fields are not exact")
    static = dict(policy)
    raw_evidence = static.pop("call_evidence")
    complete = static.pop("complete")
    if static != expected_static or type(complete) is not bool:
        raise ReportError("incomplete analysis: Ultra fork-policy freeze is stale")
    if not isinstance(raw_evidence, list):
        raise ReportError("incomplete analysis: Ultra fork-policy calls are missing")

    calls: dict[str, Mapping[str, Any]] = {}
    for raw_call in raw_evidence:
        call_id = raw_call.get("call_id") if isinstance(raw_call, Mapping) else None
        if (
            not isinstance(raw_call, Mapping)
            or set(raw_call) != ULTRA_FORK_POLICY_CALL_FIELDS
            or not isinstance(call_id, str)
            or not call_id
            or call_id in calls
        ):
            raise ReportError(
                "incomplete analysis: Ultra fork-policy call evidence is malformed"
            )
        calls[call_id] = raw_call
    if list(calls) != sorted(calls) or set(calls) != raw_ids:
        raise ReportError(
            "incomplete analysis: Ultra fork-policy calls are not canonical"
        )

    if value.get("fork_policy_complete") is False:
        if not allow_incomplete or complete is not False:
            raise ReportError("incomplete analysis: Ultra fork-policy projection is incomplete")
        if (
            not hook_observed_ids <= raw_ids
            or not hook_allowed_ids <= raw_ids
            or not hook_blocked_ids <= raw_ids
            or not hook_invalid_ids <= raw_ids
            or hook_blocked_ids != policy_blocked_ids
            or not policy_blocked_ids <= failed_ids
            or not resolved_ids <= activity_ids
            or collab_ids & policy_blocked_ids
        ):
            raise ReportError(
                "incomplete analysis: token-crossing fork-policy identifiers disagree"
            )
        return calls

    allowed_failed_ids = failed_ids - policy_blocked_ids
    allowed_terminal_ids = resolved_ids | allowed_failed_ids
    if (
        value.get("fork_policy_complete") is not True
        or complete is not True
        or hook_observed_ids != raw_ids
        or hook_allowed_ids != allowed_terminal_ids
        or hook_blocked_ids != policy_blocked_ids
        or hook_invalid_ids
        or unsupported_ids
        or not policy_blocked_ids <= failed_ids
        or activity_ids != resolved_ids
        or collab_ids & policy_blocked_ids
        or not collab_ids <= allowed_terminal_ids
    ):
        raise ReportError(
            "incomplete analysis: Ultra fork-policy identifier projections disagree"
        )

    codex = ultra_canary.codex_isolated
    for call_id, call in calls.items():
        parent_id = call.get("parent_thread_id")
        turn_id = call.get("parent_turn_id")
        response_id = call.get("parent_response_id")
        if (
            not isinstance(parent_id, str)
            or not parent_id
            or not isinstance(turn_id, str)
            or not turn_id
            or not isinstance(response_id, str)
            or not response_id
            or (known_thread_ids is not None and parent_id not in known_thread_ids)
            or (response_ids is not None and response_id not in response_ids)
            or call.get("hook_run_id")
            != (
                f"pre-tool-use:{expected_static['display_order']}:"
                f"{expected_static['source_path']}:{call_id}"
            )
            or call.get("hook_source_path") != expected_static["source_path"]
            or call.get("hook_thread_id") != parent_id
            or call.get("hook_turn_id") != turn_id
            or call.get("hook_started_observed") is not True
            or call.get("hook_started_count") != 1
            or call.get("hook_completed_observed") is not True
            or call.get("hook_completed_count") != 1
        ):
            raise ReportError(
                f"incomplete analysis: Ultra hook binding for {call_id} is inexact"
            )
        child_observed = call.get("child_activity_observed")
        if child_observed is not (call_id in resolved_ids):
            raise ReportError(
                f"incomplete analysis: Ultra child activity for {call_id} disagrees"
            )
        fork_turns = call.get("fork_turns")
        if call_id in policy_blocked_ids:
            if (
                fork_turns in ("all", "none")
                or call.get("fork_semantics")
                not in (
                    "invalid_arguments",
                    "invalid_fork_turns",
                    "unsupported_positive_turn_suffix",
                )
                or call.get("hook_status") != codex.ULTRA_FORK_POLICY_BLOCK_STATUS
                or call.get("decision") != codex.ULTRA_FORK_POLICY_BLOCK_DECISION
                or call.get("feedback")
                != codex.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
                or call.get("resolution_status")
                != codex.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
                or child_observed is not False
            ):
                raise ReportError(
                    f"incomplete analysis: Ultra blocked call {call_id} disagrees"
                )
            continue
        semantics = {
            "all": "full_history_parent_pre_response",
            "none": "no_history_zero",
        }.get(fork_turns)
        resolution = (
            "resolved_child" if call_id in resolved_ids else "failed_without_child"
        )
        if (
            semantics is None
            or call.get("fork_semantics") != semantics
            or call.get("hook_status") != codex.ULTRA_FORK_POLICY_ALLOW_STATUS
            or call.get("decision") != codex.ULTRA_FORK_POLICY_ALLOW_DECISION
            or call.get("feedback") is not None
            or call.get("resolution_status") != resolution
        ):
            raise ReportError(
                f"incomplete analysis: Ultra allowed call {call_id} disagrees"
            )
    return calls


def _validate_projection_superseded_route_order(
    *,
    response_ids: Sequence[str],
    appserver_response_ids: Sequence[str],
    direct_calls: Sequence[Mapping[str, Any]],
    suppressed_evidence: Sequence[Mapping[str, Any]],
    superseded_evidence: Sequence[Mapping[str, Any]],
    discarded_evidence: Sequence[Mapping[str, Any]],
) -> None:
    """Authenticate supersession in per-thread/turn rather than global order."""

    if not superseded_evidence:
        return
    response_bindings: dict[str, tuple[str, str, str, str]] = {}

    def bind_response(
        response_id: Any,
        call_id: Any,
        thread_id: Any,
        turn_id: Any,
        request_kind: Any,
    ) -> None:
        if (
            any(
                not isinstance(item, str) or not item
                for item in (
                    response_id,
                    call_id,
                    thread_id,
                    turn_id,
                    request_kind,
                )
            )
            or response_id not in set(response_ids)
            or response_id in response_bindings
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 response route changed"
            )
        response_bindings[str(response_id)] = (
            str(call_id),
            str(thread_id),
            str(turn_id),
            str(request_kind),
        )

    for call in direct_calls:
        metadata = call.get("request_metadata")
        if not isinstance(metadata, Mapping):
            raise ReportError(
                "incomplete analysis: projection-v6 response route changed"
            )
        bind_response(
            call.get("response_id"),
            call.get("call_id"),
            metadata.get("thread_id"),
            metadata.get("turn_id"),
            metadata.get("request_kind"),
        )
    for items in (
        suppressed_evidence,
        superseded_evidence,
        discarded_evidence,
    ):
        for item in items:
            bind_response(
                item.get("response_id"),
                item.get("provider_call_id"),
                item.get("thread_id"),
                item.get("turn_id"),
                "turn",
            )
    if set(response_bindings) != set(response_ids) or len(
        {binding[0] for binding in response_bindings.values()}
    ) != len(response_bindings):
        raise ReportError(
            "incomplete analysis: projection-v6 response route ledger changed"
        )

    positions = {response_id: index for index, response_id in enumerate(response_ids)}
    superseded_by_response = {
        str(item["response_id"]): item for item in superseded_evidence
    }
    suppressed_by_response = {
        str(item["response_id"]): item for item in suppressed_evidence
    }
    superseded_ids = set(superseded_by_response)
    allowed_successors = (
        set(appserver_response_ids) | superseded_ids | set(suppressed_by_response)
    )
    for evidence in superseded_evidence:
        response_id = str(evidence["response_id"])
        successor_id = str(evidence["successor_response_id"])
        origin = response_bindings[response_id]
        successor = response_bindings.get(successor_id)
        origin_index = positions[response_id]
        successor_index = positions.get(successor_id, -1)
        if (
            successor is None
            or successor_id not in allowed_successors
            or successor_index <= origin_index
            or successor[0] != evidence.get("successor_call_id")
            or successor[1:] != origin[1:]
            or successor[3] != "turn"
            or any(
                response_bindings[intervening][1:3] == origin[1:3]
                for intervening in response_ids[origin_index + 1 : successor_index]
            )
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 superseded chain changed"
            )

    # A suppressed wait is a valid bridge only when its evidence names the
    # earliest later direct response on the identical thread/turn route.
    appserver_id_set = set(appserver_response_ids)
    for evidence in suppressed_evidence:
        response_id = str(evidence["response_id"])
        successor_id = str(evidence["successor_response_id"])
        origin = response_bindings[response_id]
        successor = response_bindings.get(successor_id)
        origin_index = positions[response_id]
        successor_index = positions.get(successor_id, -1)
        if (
            successor is None
            or successor_id not in appserver_id_set
            or successor_index <= origin_index
            or successor[0] != evidence.get("successor_call_id")
            or successor[1:] != origin[1:]
            or successor[3] != "turn"
            or any(
                intervening in appserver_id_set
                and response_bindings[intervening][1:3] == origin[1:3]
                for intervening in response_ids[origin_index + 1 : successor_index]
            )
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 suppressed bridge changed"
            )

    for origin_id in superseded_ids:
        cursor_id = origin_id
        seen_chain: set[str] = set()
        while (
            cursor_id in superseded_by_response
            or cursor_id in suppressed_by_response
        ):
            if cursor_id in seen_chain:
                raise ReportError(
                    "incomplete analysis: projection-v6 superseded chain is cyclic"
                )
            seen_chain.add(cursor_id)
            edge = (
                superseded_by_response[cursor_id]
                if cursor_id in superseded_by_response
                else suppressed_by_response[cursor_id]
            )
            cursor_id = str(edge["successor_response_id"])
        if cursor_id not in set(appserver_response_ids):
            raise ReportError(
                "incomplete analysis: projection-v6 superseded chain has no direct end"
            )


def _rederive_projection_v4_gate(
    value: Mapping[str, Any],
    *,
    accepted: bool,
    response_ids: list[str],
    response_count: int,
    top_totals: Mapping[str, int],
) -> dict[str, Any]:
    """Rebind projection-v6 rows to provider totals and structural app events."""

    gate = _gate_object(
        value.get("provider_token_gate"),
        runner.ULTRA_PROVIDER_GATE_SUMMARY_KEYS,
        "incomplete analysis: projection-v6 provider gate",
    )
    terminal = _gate_object(
        gate.get("terminal"),
        runner.PROVIDER_GATE_STATE_KEYS,
        "incomplete analysis: projection-v6 terminal gate",
    )
    if (
        gate.get("enabled") is not True
        or gate.get("response_token_bound") != runner.PROVIDER_RESPONSE_TOKEN_BOUND
        or type(gate.get("response_token_bound")) is not int
        or not isinstance(gate.get("artifact_path"), str)
        or not Path(str(gate.get("artifact_path"))).is_absolute()
        or not _hex_digest(gate.get("record_sha256"))
        or gate.get("final_attached") is not True
        or gate.get("exact_for_usage") is not True
        or not isinstance(gate.get("live"), Mapping)
        or terminal.get("phase") != "CLOSED"
        or terminal.get("open_request_ids") != []
        or terminal.get("all_complete") is not True
        or terminal.get("no_post_close_upstream") is not True
        or terminal.get("poisoned") is not False
        or terminal.get("poison_reasons") != []
        or terminal.get("active_handler_count") != 0
        or type(terminal.get("active_handler_count")) is not int
        or terminal.get("handlers_quiescent") is not True
        or terminal.get("completed_tokens") != top_totals["total_tokens"]
        or type(terminal.get("completed_tokens")) is not int
    ):
        raise ReportError("incomplete analysis: projection-v6 gate is not exact and quiescent")
    close_reason = terminal.get("close_reason")
    teardown = _gate_object(
        value.get("adapter_teardown"),
        runner.ULTRA_ADAPTER_TEARDOWN_KEYS,
        "incomplete analysis: projection-v6 adapter teardown",
    )
    if (
        teardown.get("process_group_isolated") is not True
        or teardown.get("immediate") is not (close_reason != "natural_end")
        or teardown.get("stdin_closed") is not True
        or teardown.get("completed") is not True
        or type(teardown.get("returncode")) is not int
    ):
        raise ReportError("incomplete analysis: projection-v6 teardown disagrees with its endpoint")

    appserver_count = _projection_int(
        value.get("appserver_response_count"), "app-server response count"
    )
    appserver_ids_raw = value.get("appserver_response_ids")
    if (
        not isinstance(appserver_ids_raw, list)
        or len(appserver_ids_raw) != appserver_count
        or any(not isinstance(item, str) or not item for item in appserver_ids_raw)
        or len(set(appserver_ids_raw)) != appserver_count
    ):
        raise ReportError("incomplete analysis: projection-v6 app-server IDs changed")
    appserver_ids = list(appserver_ids_raw)
    ledger = value.get("appserver_response_ledger")
    if not isinstance(ledger, list) or len(ledger) != appserver_count:
        raise ReportError("incomplete analysis: projection-v6 response ledger has the wrong size")
    seen_responses: list[str] = []
    seen_response_ids: set[str] = set()
    seen_calls: set[str] = set()
    totals = {field: 0 for field in ACCOUNTING_TOKEN_FIELDS}
    calls: list[Mapping[str, Any]] = []
    for index, raw_response in enumerate(ledger):
        response = _gate_object(
            raw_response,
            runner.ULTRA_RESPONSE_LEDGER_KEYS,
            f"incomplete analysis: projection-v6 response {index}",
        )
        response_id = response.get("response_id")
        thread_id = response.get("thread_id")
        turn_id = response.get("turn_id")
        if (
            not isinstance(response_id, str)
            or not response_id
            or response_id in seen_response_ids
            or not isinstance(thread_id, str)
            or not thread_id
            or not isinstance(turn_id, str)
            or not turn_id
            or response.get("raw_response_notification_sequence") != index + 1
            or type(response.get("raw_response_notification_sequence")) is not int
        ):
            raise ReportError("incomplete analysis: projection-v6 response identity changed")
        usage = _gate_usage(response.get("usage"), f"projection response {response_id}")
        call = _gate_object(
            response.get("provider_gate_call"),
            runner.PROVIDER_GATE_CALL_KEYS,
            f"projection response {response_id} provider call",
        )
        call_id = call.get("call_id")
        metadata = call.get("request_metadata")
        crossbind = call.get("appserver_crossbind")
        delivery = call.get("appserver_delivery")
        _gate_validate_response_output_manifest(
            call.get("response_output_manifest"), str(response_id),
            f"projection response {response_id}",
        )
        if (
            not isinstance(call_id, str)
            or not call_id
            or call_id in seen_calls
            or call.get("response_id") != response_id
            or call.get("response_bound") != runner.PROVIDER_RESPONSE_TOKEN_BOUND
            or type(call.get("response_bound")) is not int
            or call.get("normalized_usage") != usage
            or call.get("client_release_complete") is not True
            or call.get("error") is not None
            or not isinstance(metadata, Mapping)
            or set(metadata) != set(runner.PROVIDER_GATE_REQUEST_METADATA_KEYS)
            or any(
                not isinstance(metadata.get(field), str) or not metadata.get(field)
                for field in runner.PROVIDER_GATE_REQUEST_METADATA_KEYS
            )
            or metadata.get("request_kind") not in {"turn", "compaction"}
            or metadata.get("thread_id") != thread_id
            or metadata.get("turn_id") != turn_id
            or not isinstance(crossbind, Mapping)
            or set(crossbind) != set(runner.PROVIDER_GATE_CROSSBIND_KEYS)
            or crossbind.get("thread_id") != thread_id
            or crossbind.get("turn_id") != turn_id
            or crossbind.get("event_sequence") != index + 1
            or type(crossbind.get("event_sequence")) is not int
            or crossbind.get("normalized_usage") != usage
            or not isinstance(delivery, Mapping)
            or set(delivery)
            != set(provider_token_gate.PROVIDER_GATE_APPSERVER_DELIVERY_KEYS)
            or delivery.get("kind")
            != provider_token_gate.PROVIDER_GATE_DELIVERY_DIRECT
            or delivery.get("successor_call_id") is not None
            or delivery.get("successor_response_id") is not None
            or delivery.get("bind_unix_ns") != crossbind.get("bind_unix_ns")
            or delivery.get("bind_monotonic_ns")
            != crossbind.get("bind_monotonic_ns")
        ):
            raise ReportError("incomplete analysis: projection-v6 direct delivery changed")
        for field in ACCOUNTING_TOKEN_FIELDS:
            totals[field] += usage[field]
        seen_responses.append(response_id)
        seen_response_ids.add(response_id)
        seen_calls.add(call_id)
        calls.append(call)
    if seen_responses != appserver_ids:
        raise ReportError("incomplete analysis: projection-v6 app-server order changed")

    reconciliation = _gate_object(
        value.get("provider_usage_reconciliation"),
        codex_isolated.PROVIDER_USAGE_RECONCILIATION_KEYS,
        "incomplete analysis: projection-v6 provider reconciliation",
    )
    provider_usage = _gate_usage(
        reconciliation.get("provider_usage"), "projection provider usage"
    )
    appserver_usage = _gate_usage(
        reconciliation.get("appserver_usage"), "projection app-server usage"
    )
    suppressed_usage = _gate_usage(
        reconciliation.get("suppressed_collaboration_wait_usage"),
        "projection suppressed-wait usage",
    )
    superseded_usage = _gate_usage(
        reconciliation.get("superseded_by_collaboration_message_usage"),
        "projection superseded-message usage",
    )
    discarded_usage = _gate_usage(
        reconciliation.get("discarded_after_explicit_child_interrupt_usage"),
        "projection explicit-child-interrupt discard usage",
    )
    suppressed_count = _projection_int(
        reconciliation.get("suppressed_collaboration_wait_response_count"),
        "suppressed-wait response count",
    )
    suppressed_ids_raw = reconciliation.get(
        "suppressed_collaboration_wait_response_ids"
    )
    evidence_raw = reconciliation.get("suppressed_collaboration_wait_evidence")
    superseded_count = _projection_int(
        reconciliation.get(
            "superseded_by_collaboration_message_response_count"
        ),
        "superseded-message response count",
    )
    superseded_ids_raw = reconciliation.get(
        "superseded_by_collaboration_message_response_ids"
    )
    superseded_evidence_raw = reconciliation.get(
        "superseded_by_collaboration_message_evidence"
    )
    discarded_count = _projection_int(
        reconciliation.get("discarded_after_explicit_child_interrupt_response_count"),
        "explicit-child-interrupt discard response count",
    )
    discarded_ids_raw = reconciliation.get(
        "discarded_after_explicit_child_interrupt_response_ids"
    )
    discarded_evidence_raw = reconciliation.get(
        "discarded_after_explicit_child_interrupt_evidence"
    )
    if (
        reconciliation.get("schema_version")
        != codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
        or type(reconciliation.get("schema_version")) is not int
        or reconciliation.get("provider_response_count") != response_count
        or type(reconciliation.get("provider_response_count")) is not int
        or reconciliation.get("appserver_response_count") != appserver_count
        or type(reconciliation.get("appserver_response_count")) is not int
        or reconciliation.get("provider_response_ids") != response_ids
        or reconciliation.get("appserver_response_ids") != appserver_ids
        or value.get("discarded_after_explicit_child_interrupt_response_count")
        != discarded_count
        or value.get("discarded_after_explicit_child_interrupt_response_ids")
        != discarded_ids_raw
        or value.get("discarded_after_explicit_child_interrupt_usage")
        != discarded_usage
        or value.get("discarded_after_explicit_child_interrupt_evidence")
        != discarded_evidence_raw
        or provider_usage != dict(top_totals)
        or appserver_usage != totals
        or any(
            provider_usage[field]
            != appserver_usage[field]
            + suppressed_usage[field]
            + superseded_usage[field]
            + discarded_usage[field]
            for field in ACCOUNTING_TOKEN_FIELDS
        )
        or response_count
        != appserver_count + suppressed_count + superseded_count + discarded_count
        or not isinstance(suppressed_ids_raw, list)
        or len(suppressed_ids_raw) != suppressed_count
        or any(not isinstance(item, str) or not item for item in suppressed_ids_raw)
        or len(set(suppressed_ids_raw)) != suppressed_count
        or not isinstance(superseded_ids_raw, list)
        or len(superseded_ids_raw) != superseded_count
        or any(not isinstance(item, str) or not item for item in superseded_ids_raw)
        or len(set(superseded_ids_raw)) != superseded_count
        or not isinstance(discarded_ids_raw, list)
        or len(discarded_ids_raw) != discarded_count
        or any(not isinstance(item, str) or not item for item in discarded_ids_raw)
        or len(set(discarded_ids_raw)) != discarded_count
        or set(response_ids)
        != set(appserver_ids)
        | set(suppressed_ids_raw)
        | set(superseded_ids_raw)
        | set(discarded_ids_raw)
        or set(appserver_ids) & set(suppressed_ids_raw)
        or set(appserver_ids) & set(superseded_ids_raw)
        or set(suppressed_ids_raw) & set(superseded_ids_raw)
        or set(appserver_ids) & set(discarded_ids_raw)
        or set(suppressed_ids_raw) & set(discarded_ids_raw)
        or set(superseded_ids_raw) & set(discarded_ids_raw)
        or not isinstance(evidence_raw, list)
        or len(evidence_raw) != suppressed_count
        or not isinstance(superseded_evidence_raw, list)
        or len(superseded_evidence_raw) != superseded_count
        or not isinstance(discarded_evidence_raw, list)
        or len(discarded_evidence_raw) != discarded_count
    ):
        raise ReportError("incomplete analysis: projection-v6 usage partition changed")
    calls_by_response = {str(call["response_id"]): call for call in calls}
    used_messages: set[str] = set()
    for index, raw_evidence in enumerate(evidence_raw):
        evidence = _gate_object(
            raw_evidence,
            codex_isolated.SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS,
            f"incomplete analysis: projection-v6 suppressed evidence {index}",
        )
        successor = calls_by_response.get(str(evidence.get("successor_response_id")))
        message_id = evidence.get("agent_message_item_id")
        if (
            evidence.get("response_id") != suppressed_ids_raw[index]
            or not isinstance(successor, Mapping)
            or evidence.get("successor_call_id") != successor.get("call_id")
            or evidence.get("agent_message_recipient") != "/root"
            or not isinstance(evidence.get("agent_message_author"), str)
            or not str(evidence.get("agent_message_author")).startswith("/root/")
            or not isinstance(message_id, str)
            or not message_id
            or message_id in used_messages
            or not _hex_digest(evidence.get("agent_message_sha256"))
            or _gate_positive(
                evidence.get("agent_message_observed_at_unix_ns"),
                "projection child-result wall time",
            )
            <= 0
            or _gate_positive(
                evidence.get("agent_message_observed_at_monotonic_ns"),
                "projection child-result time",
            )
            <= 0
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 suppressed wait is not proven"
            )
        used_messages.add(message_id)
    for index, raw_evidence in enumerate(superseded_evidence_raw):
        evidence = _gate_object(
            raw_evidence,
            codex_isolated.SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS,
            f"incomplete analysis: projection-v6 superseded evidence {index}",
        )
        response_id = evidence.get("response_id")
        successor_id = evidence.get("successor_response_id")
        if (
            response_id != superseded_ids_raw[index]
            or not isinstance(response_id, str)
            or not isinstance(successor_id, str)
            or successor_id not in response_ids
            or response_ids.index(successor_id) <= response_ids.index(response_id)
            or any(
                not isinstance(evidence.get(field), str)
                or not evidence.get(field)
                for field in (
                    "provider_call_id",
                    "thread_id",
                    "turn_id",
                    "successor_call_id",
                )
            )
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 superseded chain changed"
            )
        raw_messages = evidence.get("collaboration_messages")
        if not isinstance(raw_messages, list) or not raw_messages:
            raise ReportError(
                "incomplete analysis: projection-v6 superseded message evidence is empty"
            )
        messages: list[dict[str, Any]] = []
        for message_index, raw_message in enumerate(raw_messages):
            message = _gate_object(
                raw_message,
                codex_isolated.COLLABORATION_MESSAGE_EVIDENCE_KEYS,
                "incomplete analysis: projection-v6 superseded message "
                f"{index}:{message_index}",
            )
            message_id = message.get("item_id")
            if (
                not isinstance(message_id, str)
                or not message_id
                or message_id in used_messages
                or not _hex_digest(message.get("item_sha256"))
                or not isinstance(message.get("author"), str)
                or not _rooted_collaboration_route_matches(
                    thread_id=evidence.get("thread_id"),
                    author=message.get("author"),
                    recipient=message.get("recipient"),
                    thread_accounting=value.get("thread_accounting"),
                    root_thread_id=value.get("root_thread_id"),
                )
                or _gate_positive(
                    message.get("observed_at_monotonic_ns"),
                    "projection superseded child-message time",
                )
                <= 0
                or _gate_positive(
                    message.get("observed_at_unix_ns"),
                    "projection superseded child-message wall time",
                )
                <= 0
            ):
                raise ReportError(
                    "incomplete analysis: projection-v6 superseded message changed"
                )
            used_messages.add(message_id)
            messages.append(message)
        if messages != sorted(
            messages,
            key=lambda message: (
                message["observed_at_monotonic_ns"],
                message["observed_at_unix_ns"],
                message["item_id"],
            ),
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 superseded messages are out of order"
            )
    used_interrupt_items: set[str] = set()
    used_interrupt_outputs: set[str] = set()
    discarded_evidence: list[dict[str, Any]] = []
    for index, raw_evidence in enumerate(discarded_evidence_raw):
        interrupting = calls_by_response.get(
            str(raw_evidence.get("interrupting_response_id"))
            if isinstance(raw_evidence, Mapping)
            else ""
        )
        if not isinstance(interrupting, Mapping):
            raise ReportError(
                "incomplete analysis: projection-v6 interrupt discard lacks its direct call"
            )
        evidence = _validate_projected_explicit_child_interrupt_evidence(
            evidence_value=raw_evidence,
            discarded_response_id=discarded_ids_raw[index],
            interrupting=interrupting,
            thread_accounting=value.get("thread_accounting"),
            root_thread_id=value.get("root_thread_id"),
            label=f"incomplete analysis: projection-v6 interrupt evidence {index}",
        )
        function_item_id = str(evidence["interrupt_function_item_id"])
        output_item_id = str(evidence["interrupt_output_item_id"])
        if (
            function_item_id in used_interrupt_items
            or output_item_id in used_interrupt_outputs
        ):
            raise ReportError(
                "incomplete analysis: projection-v6 interrupt evidence reuses an item"
            )
        used_interrupt_items.add(function_item_id)
        used_interrupt_outputs.add(output_item_id)
        discarded_evidence.append(evidence)

    # Provider completion order is global across concurrently active routes.
    # Require adjacency only after projecting that order onto one thread/turn.
    _validate_projection_superseded_route_order(
        response_ids=response_ids,
        appserver_response_ids=appserver_ids,
        direct_calls=calls,
        suppressed_evidence=evidence_raw,
        superseded_evidence=superseded_evidence_raw,
        discarded_evidence=discarded_evidence,
    )
    crossing = terminal.get("crossing")
    first_crossing = value.get("first_crossing")
    if accepted:
        endpoint = "accepted_boundary"
        if (
            close_reason != "accepted_submission"
            or crossing is not None
            or first_crossing is not None
            or value.get("stop_reason") != "first_valid_proof"
            or value.get("drain_complete") is not False
            or any(call.get("release_kind") != "byte_identity" for call in calls)
        ):
            raise ReportError("incomplete analysis: accepted projection/gate endpoint disagrees")
    elif close_reason == "token_limit":
        endpoint = "token_gate_crossing"
        if (
            not isinstance(crossing, Mapping)
            or set(crossing) != set(runner.PROVIDER_GATE_CROSSING_KEYS)
            or not isinstance(first_crossing, Mapping)
            or first_crossing.get("response_id") != crossing.get("response_id")
            or first_crossing.get("tokens") != crossing.get("completed_tokens")
            or crossing.get("sole_inflight") is not True
            or crossing.get("release_kind")
            not in {
                runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
                runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            }
            or crossing.get("response_id") not in calls_by_response
            or value.get("stop_reason") != "token_limit"
            or value.get("drain_complete") is not False
            or len([call for call in calls if call.get("crossed_cap") is True]) != 1
            or discarded_count != 0
            or discarded_ids_raw != []
            or discarded_evidence_raw != []
            or calls_by_response[crossing["response_id"]].get("release_kind")
            != crossing.get("release_kind")
            or calls_by_response[crossing["response_id"]].get("release_kind")
            != {
                "turn": runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
                "compaction": runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            }.get(crossing.get("request_kind"))
        ):
            raise ReportError("incomplete analysis: token projection/gate endpoint disagrees")
    else:
        endpoint = "natural_drain"
        if (
            close_reason != "natural_end"
            or crossing is not None
            or first_crossing is not None
            or value.get("drain_complete") is not True
            or any(call.get("release_kind") != "byte_identity" for call in calls)
        ):
            raise ReportError("incomplete analysis: natural projection/gate endpoint disagrees")
    return {
        "outcome": endpoint,
        "protocol": runner.PROVIDER_GATE_PROTOCOL,
        "record_sha256": gate["record_sha256"],
        "response_ids": response_ids,
        "appserver_response_ids": appserver_ids,
        "suppressed_collaboration_wait_response_ids": list(suppressed_ids_raw),
        "superseded_by_collaboration_message_response_ids": list(
            superseded_ids_raw
        ),
        "discarded_after_explicit_child_interrupt_response_ids": list(
            discarded_ids_raw
        ),
        "close_reason": close_reason,
        "appserver_deliveries_reconciled": True,
        "adapter_teardown_complete": True,
    }


def _rederive_ultra_accounting_evidence(value: Any) -> dict[str, Any]:
    """Recompute projection-v6 without trusting the result checker's verdict."""

    if not isinstance(value, Mapping):
        raise ReportError("incomplete analysis: Ultra projection evidence is not an object")
    if (
        value.get("accounting_projection_schema_version")
        != ACCOUNTING_PROJECTION_SCHEMA_VERSION
    ):
        raise ReportError("incomplete analysis: Ultra accounting projection is not schema v6")
    if value.get("spawn_binding_source") != ACCOUNTING_SPAWN_BINDING_SOURCE:
        raise ReportError("incomplete analysis: Ultra spawn binding has the wrong source")
    root_id = value.get("root_thread_id")
    if not isinstance(root_id, str) or not root_id:
        raise ReportError("incomplete analysis: Ultra accounting has no root thread")
    response_ids_raw = value.get("response_ids")
    if (
        not isinstance(response_ids_raw, list)
        or any(not isinstance(item, str) or not item for item in response_ids_raw)
        or len(response_ids_raw) != len(set(response_ids_raw))
    ):
        raise ReportError("incomplete analysis: Ultra response IDs are malformed")
    response_ids = list(response_ids_raw)
    response_count = _projection_int(value.get("response_count"), "response count")
    appserver_ids_raw = value.get("appserver_response_ids")
    appserver_count = _projection_int(
        value.get("appserver_response_count"), "app-server response count"
    )
    if (
        len(response_ids) != response_count
        or value.get("call_count") != response_count
        or value.get("provider_response_count") != response_count
        or value.get("provider_response_ids") != response_ids
        or not isinstance(appserver_ids_raw, list)
        or len(appserver_ids_raw) != appserver_count
        or any(not isinstance(item, str) or not item for item in appserver_ids_raw)
        or len(set(appserver_ids_raw)) != appserver_count
    ):
        raise ReportError("incomplete analysis: Ultra response totals disagree")
    appserver_ids = list(appserver_ids_raw)

    boundary = value.get("submission_boundary")
    accepted = bool(
        value.get("submission_boundary_exact") is True
        and isinstance(boundary, Mapping)
        and boundary.get("status") == "accepted"
        and boundary.get("exact") is True
        and boundary.get("authenticated") is True
    )
    if accepted:
        boundary_response = boundary.get("response_id")
        if boundary.get("thread_id") != root_id or boundary_response not in appserver_ids:
            raise ReportError("incomplete analysis: Ultra boundary is not the rooted response")
    else:
        boundary_response = None
        if boundary is not None or value.get("submission_boundary_exact") is not False:
            raise ReportError("incomplete analysis: natural Ultra evidence carries a boundary")
    gate_hint = value.get("provider_token_gate")
    terminal_hint = gate_hint.get("terminal") if isinstance(gate_hint, Mapping) else None
    token_endpoint_hint = bool(
        not accepted
        and isinstance(terminal_hint, Mapping)
        and terminal_hint.get("close_reason") == "token_limit"
    )

    raw_threads = value.get("thread_accounting")
    thread_count = _projection_int(value.get("thread_count"), "thread count")
    if not isinstance(raw_threads, list) or len(raw_threads) != thread_count or not raw_threads:
        raise ReportError("incomplete analysis: Ultra thread ledger has the wrong size")
    zero = {field: 0 for field in ACCOUNTING_TOKEN_FIELDS}
    totals = dict(zero)
    total_responses = 0
    threads: dict[str, dict[str, Any]] = {}
    for raw in raw_threads:
        if not isinstance(raw, Mapping):
            raise ReportError("incomplete analysis: Ultra thread ledger is malformed")
        thread_id = raw.get("thread_id")
        if not isinstance(thread_id, str) or not thread_id or thread_id in threads:
            raise ReportError("incomplete analysis: Ultra thread IDs are invalid")
        parent_id = raw.get("parent_thread_id")
        if parent_id is not None and (not isinstance(parent_id, str) or not parent_id):
            raise ReportError("incomplete analysis: Ultra parent thread ID is invalid")
        raw_sum = {
            field: _projection_int(raw.get(field), f"thread {thread_id}.{field}")
            for field in ACCOUNTING_TOKEN_FIELDS
        }
        if (
            raw_sum["cached_input_tokens"] > raw_sum["input_tokens"]
            or raw_sum["cache_write_input_tokens"] > raw_sum["input_tokens"]
            or raw_sum["reasoning_output_tokens"] > raw_sum["output_tokens"]
            or raw_sum["total_tokens"]
            != raw_sum["input_tokens"] + raw_sum["output_tokens"]
        ):
            raise ReportError("incomplete analysis: Ultra thread raw sum is inconsistent")
        for field in ACCOUNTING_TOKEN_FIELDS:
            totals[field] += raw_sum[field]
        total_responses += _projection_int(
            raw.get("response_count"), f"thread {thread_id} response count"
        )

        baseline = _projection_optional_breakdown(
            raw.get("expected_cumulative_baseline"),
            f"thread {thread_id} expected baseline",
        )
        is_root = thread_id == root_id
        exempt_id = raw.get("cumulative_projection_exempt_response_id")
        exempt_usage = _projection_optional_breakdown(
            raw.get("cumulative_projection_exempt_response_usage"),
            f"thread {thread_id} exempt response usage",
        )
        if accepted and is_root:
            if exempt_id != boundary_response or exempt_usage is None:
                raise ReportError("incomplete analysis: accepted root exception is missing")
        elif exempt_id is not None or exempt_usage is not None:
            raise ReportError("incomplete analysis: non-root/natural projection has an exception")
        last = _projection_optional_breakdown(
            raw.get("last_cumulative"), f"thread {thread_id} last cumulative"
        )
        observations = _projection_int(
            raw.get("cumulative_observation_count"),
            f"thread {thread_id} cumulative observation count",
        )
        if (observations == 0) != (last is None):
            raise ReportError("incomplete analysis: cumulative observation count disagrees")
        if baseline is None:
            if is_root or not token_endpoint_hint:
                raise ReportError(
                    "incomplete analysis: unresolved Ultra baseline outside a token crossing"
                )
            full = _projection_optional_breakdown(
                raw.get("full_cumulative_projection"),
                f"thread {thread_id} full projection",
            )
            expected = _projection_optional_breakdown(
                raw.get("expected_cumulative_projection"),
                f"thread {thread_id} expected projection",
            )
            if full is not None or expected is not None:
                raise ReportError(
                    "incomplete analysis: unresolved token-crossing baseline has a projection"
                )
            projection_match = False
            observed_baseline = None
            baseline_match = False
            status = "unresolved_expected_baseline"
        else:
            full = {
                field: baseline[field] + raw_sum[field]
                for field in ACCOUNTING_TOKEN_FIELDS
            }
            if _projection_optional_breakdown(
                raw.get("full_cumulative_projection"),
                f"thread {thread_id} full projection",
            ) != full:
                raise ReportError("incomplete analysis: Ultra full projection disagrees")
            projected_raw = dict(raw_sum)
            if exempt_usage is not None:
                projected_raw = {
                    field: raw_sum[field] - exempt_usage[field]
                    for field in ACCOUNTING_TOKEN_FIELDS
                }
                if any(amount < 0 for amount in projected_raw.values()):
                    raise ReportError("incomplete analysis: root exception exceeds raw usage")
            expected = {
                field: baseline[field] + projected_raw[field]
                for field in ACCOUNTING_TOKEN_FIELDS
            }
            if _projection_optional_breakdown(
                raw.get("expected_cumulative_projection"),
                f"thread {thread_id} expected projection",
            ) != expected:
                raise ReportError("incomplete analysis: Ultra expected projection disagrees")
            if last is None:
                projection_match = bool(
                    accepted and is_root and expected == zero and baseline == zero
                )
                observed_baseline = None
                baseline_match = projection_match
                status = (
                    "zero_pre_response_without_cumulative_notification"
                    if projection_match
                    else "missing_cumulative"
                )
            else:
                compare_raw = (
                    raw_sum if exempt_usage is not None and last == full else projected_raw
                )
                differences = {
                    field: last[field] - compare_raw[field]
                    for field in ACCOUNTING_TOKEN_FIELDS
                }
                observed_baseline = (
                    differences
                    if all(amount >= 0 for amount in differences.values())
                    else None
                )
                baseline_match = observed_baseline == baseline
                projection_match = bool(
                    baseline_match
                    and (
                        last in (expected, full)
                        if exempt_usage is not None
                        else last == expected
                    )
                )
                if exempt_usage is not None and last == full:
                    status = "matched_full_including_exempt_response"
                elif exempt_usage is not None and last == expected:
                    status = "matched_pre_exempt_response"
                elif exempt_usage is None and last == expected:
                    status = "matched_full_projection"
                else:
                    status = "cumulative_projection_mismatch"
        if (
            raw.get("observed_cumulative_baseline") != observed_baseline
            or raw.get("cumulative_baseline_matches_expected") != baseline_match
            or raw.get("cumulative_projection_match") != projection_match
            or raw.get("cumulative_projection_status") != status
        ):
            raise ReportError("incomplete analysis: Ultra projection status is stale")

        spawn = (
            raw.get("spawn_call_id"),
            raw.get("spawn_parent_turn_id"),
            raw.get("spawn_parent_response_id"),
            raw.get("spawn_fork_turns"),
            raw.get("spawn_fork_semantics"),
        )
        if is_root:
            binding = bool(
                parent_id is None
                and raw.get("spawn_binding_status") == "root_zero"
                and all(item is None for item in spawn)
                and baseline == zero
            )
        else:
            call_id, parent_turn, parent_response, fork_turns, fork_semantics = spawn
            expected_semantics = {
                "none": "no_history_zero",
                "all": "full_history_parent_pre_response",
            }.get(fork_turns)
            binding = bool(
                raw.get("spawn_binding_status") == "resolved"
                and isinstance(call_id, str) and call_id
                and isinstance(parent_turn, str) and parent_turn
                and isinstance(parent_response, str) and parent_response in response_ids
                and expected_semantics is not None
                and fork_semantics == expected_semantics
                and (fork_turns != "none" or baseline == zero)
            )
        complete = bool(binding and projection_match)
        if raw.get("accounting_complete") != complete:
            raise ReportError("incomplete analysis: Ultra thread completeness is stale")
        threads[thread_id] = {
            "parent": parent_id,
            "spawn_call_id": raw.get("spawn_call_id"),
            "baseline": baseline,
            "projection_match": projection_match,
            "complete": complete,
        }

    if root_id not in threads or threads[root_id]["parent"] is not None:
        raise ReportError("incomplete analysis: Ultra root ledger is invalid")
    for thread_id, thread in threads.items():
        if thread_id == root_id:
            continue
        parent = thread["parent"]
        if parent not in threads or parent == thread_id:
            raise ReportError("incomplete analysis: Ultra child parent is invalid")
        ancestry: set[str] = set()
        current: str | None = thread_id
        while current is not None:
            if current in ancestry:
                raise ReportError("incomplete analysis: Ultra thread graph is cyclic")
            ancestry.add(current)
            parent_value = threads[current]["parent"]
            current = parent_value if isinstance(parent_value, str) else None
    provider_top = {
        "input_tokens": value.get("input_tokens"),
        "cached_input_tokens": value.get("cached_input_tokens"),
        "cache_write_input_tokens": value.get("cache_write_input_tokens"),
        "output_tokens": value.get("output_tokens"),
        "reasoning_output_tokens": value.get("reasoning_output_tokens"),
        "total_tokens": value.get("model_tokens"),
    }
    provider_usage = _gate_usage(value.get("provider_usage"), "projection provider usage")
    appserver_usage = _gate_usage(
        value.get("appserver_usage"), "projection app-server usage"
    )
    suppressed_usage = _gate_usage(
        value.get("suppressed_collaboration_wait_usage"),
        "projection suppressed-wait usage",
    )
    superseded_usage = _gate_usage(
        value.get("superseded_by_collaboration_message_usage"),
        "projection superseded-message usage",
    )
    if (
        provider_usage != provider_top
        or totals != appserver_usage
        or total_responses != appserver_count
        or any(
            provider_usage[field]
            != appserver_usage[field]
            + suppressed_usage[field]
            + superseded_usage[field]
            for field in ACCOUNTING_TOKEN_FIELDS
        )
    ):
        raise ReportError("incomplete analysis: Ultra per-thread totals disagree")
    gate_projection = _rederive_projection_v4_gate(
        value,
        accepted=accepted,
        response_ids=response_ids,
        response_count=response_count,
        top_totals=provider_usage,
    )

    raw_ids = _projection_ids(value.get("raw_spawn_call_ids"), "raw spawn IDs")
    activity_ids = _projection_ids(value.get("activity_spawn_call_ids"), "activity spawn IDs")
    collab_ids = _projection_ids(value.get("collab_spawn_call_ids"), "collaboration spawn IDs")
    resolved_ids = _projection_ids(value.get("resolved_spawn_call_ids"), "resolved spawn IDs")
    failed_ids = _projection_ids(value.get("failed_spawn_call_ids"), "failed spawn IDs")
    policy_blocked_ids = _projection_ids(
        value.get("policy_blocked_spawn_call_ids"), "policy-blocked spawn IDs"
    )
    unresolved_ids = _projection_ids(value.get("unresolved_spawn_call_ids"), "unresolved spawn IDs")
    unsupported_ids = _projection_ids(value.get("unsupported_spawn_call_ids"), "unsupported spawn IDs")
    inference_children = _projection_ids(value.get("inference_child_thread_ids"), "inference child IDs")
    children = set(threads) - {root_id}
    child_spawn_ids = {
        str(threads[thread_id]["spawn_call_id"])
        for thread_id in children
        if threads[thread_id]["spawn_call_id"] is not None
    }
    terminal = resolved_ids | failed_ids
    _rederive_ultra_fork_policy(
        value,
        raw_ids=raw_ids,
        activity_ids=activity_ids,
        collab_ids=collab_ids,
        resolved_ids=resolved_ids,
        failed_ids=failed_ids,
        unsupported_ids=unsupported_ids,
        known_thread_ids=set(threads),
        response_ids=response_ids,
        allow_incomplete=token_endpoint_hint,
    )
    spawn_complete = bool(
        not (resolved_ids & failed_ids)
        and raw_ids == terminal
        and activity_ids == resolved_ids
        and collab_ids <= terminal
        and not unresolved_ids
        and not unsupported_ids
        and inference_children == children
        and child_spawn_ids == resolved_ids
        and len(child_spawn_ids) == len(children)
        and policy_blocked_ids <= failed_ids
        and value.get("fork_policy_complete") is True
    )
    descendants_complete = all(threads[item]["complete"] for item in children)
    cumulative_complete = all(item["projection_match"] for item in threads.values())
    accounting_complete = bool(
        spawn_complete and cumulative_complete and all(item["complete"] for item in threads.values())
    )
    derived = {
        "spawn_linkage_complete": spawn_complete,
        "descendant_accounting_complete": descendants_complete,
        "cumulative_projection_complete": cumulative_complete,
        "fork_policy_complete": value.get("fork_policy_complete"),
        "accounting_complete": accounting_complete,
    }
    if any(value.get(field) != expected for field, expected in derived.items()):
        raise ReportError("incomplete analysis: Ultra top-level accounting is not complete")
    if gate_projection["outcome"] != "token_gate_crossing" and not all(derived.values()):
        raise ReportError("incomplete analysis: non-token Ultra accounting is not complete")
    return {
        "outcome": gate_projection["outcome"],
        "provider_gate": gate_projection,
        "thread_count": len(threads),
        "child_thread_count": len(children),
        "resolved_spawn_count": len(resolved_ids),
        "policy_blocked_spawn_count": len(policy_blocked_ids),
        "nonzero_inherited_child_baseline_count": sum(
            isinstance(threads[thread_id]["baseline"], Mapping)
            and any(threads[thread_id]["baseline"].values())
            for thread_id in children
        ),
        **derived,
    }


def _validate_ultra_accounting_summary(
    check: Mapping[str, Any], selected_runs: Sequence[Mapping[str, Any]]
) -> Mapping[str, Any]:
    summary = check.get("ultra_accounting_projections")
    if not isinstance(summary, Mapping):
        raise ReportError("incomplete analysis: Ultra accounting summary is missing")
    evidence = summary.get("run_evidence")
    if not isinstance(evidence, list) or len(evidence) != len(selected_runs):
        raise ReportError("incomplete analysis: Ultra accounting evidence count is wrong")
    selected_by_id = {run.get("run_id"): run for run in selected_runs}
    seen: set[str] = set()
    accepted = 0
    natural = 0
    token_crossing = 0
    for audit in evidence:
        if not isinstance(audit, Mapping) or audit.get("valid") is not True:
            raise ReportError("incomplete analysis: an Ultra projection audit failed")
        run_id = audit.get("run_id")
        if not isinstance(run_id, str) or run_id not in selected_by_id or run_id in seen:
            raise ReportError("incomplete analysis: Ultra projection run identity is invalid")
        seen.add(run_id)
        derived = _rederive_ultra_accounting_evidence(audit.get("evidence"))
        for field in (
            "outcome",
            "provider_gate",
            "thread_count",
            "child_thread_count",
            "resolved_spawn_count",
            "policy_blocked_spawn_count",
            "nonzero_inherited_child_baseline_count",
            "spawn_linkage_complete",
            "descendant_accounting_complete",
            "cumulative_projection_complete",
            "fork_policy_complete",
            "accounting_complete",
        ):
            if audit.get(field) != derived[field]:
                raise ReportError("incomplete analysis: Ultra projection audit is stale")
        expected_outcome = (
            "accepted_boundary"
            if selected_by_id[run_id].get("pass") is True
            else "token_gate_crossing"
            if selected_by_id[run_id].get("failure_code") == "TOKEN_LIMIT"
            else "natural_drain"
        )
        if derived["outcome"] != expected_outcome:
            raise ReportError("incomplete analysis: Ultra projection outcome disagrees")
        accepted += derived["outcome"] == "accepted_boundary"
        natural += derived["outcome"] == "natural_drain"
        token_crossing += derived["outcome"] == "token_gate_crossing"
    if (
        seen != set(selected_by_id)
        or summary.get("schema_version") != ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or summary.get("spawn_binding_source") != ACCOUNTING_SPAWN_BINDING_SOURCE
        or summary.get("selected_ultra_run_count") != len(selected_runs)
        or summary.get("complete_projection_count") != len(selected_runs)
        or summary.get("accepted_boundary_projection_count") != accepted
        or summary.get("natural_drain_projection_count") != natural
        or summary.get("token_gate_crossing_projection_count") != token_crossing
        or summary.get("all_selected_ultra_projections_complete") is not True
    ):
        raise ReportError("incomplete analysis: Ultra accounting summary is inconsistent")
    return summary


def _validate_ultra_boundary_summary(
    check: Mapping[str, Any], selected_runs: Sequence[Mapping[str, Any]]
) -> Mapping[str, Any]:
    """Require the result checker's exact per-outcome Ultra boundary totals."""

    if any(run.get("failure_code") == "TIME_LIMIT" for run in selected_runs):
        raise ReportError(
            "incomplete analysis: an Ultra TIME_LIMIT cannot be an exact "
            "natural-drain final"
        )

    boundary_summary = check.get("ultra_submission_boundaries")
    passing = sum(run.get("pass") is True for run in selected_runs)
    failures = len(selected_runs) - passing
    token_failures = sum(
        run.get("pass") is not True and run.get("failure_code") == "TOKEN_LIMIT"
        for run in selected_runs
    )
    natural_failures = failures - token_failures
    if (
        not isinstance(boundary_summary, Mapping)
        or boundary_summary.get("protocol") != "authenticated-submit-proof-v1"
        or boundary_summary.get("selected_ultra_run_count") != len(selected_runs)
        or boundary_summary.get("passing_ultra_run_count") != passing
        or boundary_summary.get("verified_accepted_boundary_count") != passing
        or boundary_summary.get("naturally_drained_failure_count") != natural_failures
        or boundary_summary.get("provider_gate_crossing_failure_count")
        != token_failures
        or boundary_summary.get("invalid_or_inexact_outcome_count") != 0
        or boundary_summary.get("retained_artifact_set_count") != passing
        or boundary_summary.get("retained_artifact_file_count") != passing * 5
        or boundary_summary.get("retained_artifacts_reauthenticated") is not True
        or boundary_summary.get("pass_drain_complete") is not False
        or boundary_summary.get("failure_natural_drain_complete") is not True
        or boundary_summary.get("root_active_at_pass_boundary") is not True
        or boundary_summary.get("descendants_quiescent_at_pass_boundary") is not True
        or boundary_summary.get(
            "later_model_response_possible_after_pass_boundary"
        )
        is not False
        or boundary_summary.get("all_selected_ultra_outcomes_exact") is not True
    ):
        raise ReportError(
            "incomplete analysis: authenticated Ultra submission-boundary summary is invalid"
        )
    return boundary_summary


def _validate_matrix_record_summary(
    check: Mapping[str, Any],
    selected_runs: Sequence[Mapping[str, Any]],
    *,
    ultra: bool = False,
) -> Mapping[str, Any]:
    """Independently reauthenticate every orchestrator-owned final record."""

    summary = check.get("matrix_record_authentication")
    evidence = summary.get("run_evidence") if isinstance(summary, Mapping) else None
    if not isinstance(evidence, list) or len(evidence) != len(selected_runs):
        raise ReportError(
            "incomplete analysis: matrix final-record authentication is missing"
        )
    selected_by_id = {run.get("run_id"): run for run in selected_runs}
    seen: set[str] = set()
    for audit in evidence:
        record = audit.get("record") if isinstance(audit, Mapping) else None
        run_id = audit.get("run_id") if isinstance(audit, Mapping) else None
        if (
            not isinstance(audit, Mapping)
            or audit.get("valid") is not True
            or not isinstance(run_id, str)
            or run_id not in selected_by_id
            or run_id in seen
            or not isinstance(record, Mapping)
            or record.get("run_id") != run_id
            or audit.get("matrix_attempt") not in (1, 2)
            or isinstance(audit.get("matrix_attempt"), bool)
            or record.get("matrix_attempt") != audit.get("matrix_attempt")
            or (
                ultra
                and not (
                    type(record.get("agent_exit_code")) is int
                    and record.get("agent_exit_code") == 0
                )
            )
            or not _hex_digest(audit.get("matrix_record_sha256"))
            or record.get("matrix_record_sha256")
            != audit.get("matrix_record_sha256")
            or audit.get("recomputed_matrix_record_sha256")
            != audit.get("matrix_record_sha256")
            or _document_digest(
                {
                    key: value
                    for key, value in record.items()
                    if key != "matrix_record_sha256"
                }
            )
            != audit.get("matrix_record_sha256")
        ):
            raise ReportError(
                "incomplete analysis: a matrix final record failed self-authentication"
            )
        if ultra:
            _authenticate_provider_gate_record(
                record,
                label=f"selected Ultra run {run_id}",
            )
        flattened = selected_by_id[run_id]
        for field in (
            "run_id",
            "pair_id",
            "paper_id",
            "task_id",
            "tier",
            "repetition_id",
            "condition",
            "pair_order",
            "order_index",
            "pass",
            "failure_code",
        ):
            expected = record.get(field)
            if field == "pass":
                expected = expected is True
            if flattened.get(field) != expected:
                raise ReportError(
                    "incomplete analysis: authenticated matrix record disagrees "
                    "with the per-run table"
                )
        seen.add(run_id)
    if (
        seen != set(selected_by_id)
        or summary.get("schema_version") != 1
        or summary.get("hash_field") != "matrix_record_sha256"
        or summary.get("canonicalization")
        != "compact_sorted_key_utf8_json_remove_only_hash_field"
        or summary.get("selected_final_record_count") != len(selected_runs)
        or summary.get("authenticated_final_record_count") != len(selected_runs)
        or summary.get("all_selected_final_records_authenticated") is not True
    ):
        raise ReportError(
            "incomplete analysis: matrix final-record authentication summary is inconsistent"
        )
    return summary


def _prompt_command_option(command: Sequence[Any], option: str) -> str | None:
    positions = [index for index, item in enumerate(command) if item == option]
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        return None
    value = command[positions[0] + 1]
    return value if isinstance(value, str) else None


def _prompt_turn_start_wire(
    *, prompt: str, root_thread_id: str, model: str, reasoning_effort: str
) -> bytes:
    request = {
        "id": 3,
        "method": "turn/start",
        "params": {
            "approvalPolicy": "never",
            "cwd": "/workspace",
            "effort": reasoning_effort,
            "input": [{"type": "text", "text": prompt}],
            "model": model,
            "sandboxPolicy": {"type": "dangerFullAccess"},
            "threadId": root_thread_id,
        },
    }
    return (
        json.dumps(request, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def _sealed_prompt_artifact(path_value: Any, repository_root: Path, label: str) -> Path:
    if not isinstance(path_value, str) or not path_value or not Path(path_value).is_absolute():
        raise ReportError(f"incomplete analysis: {label} has no absolute retained path")
    unresolved = Path(path_value)
    try:
        details = unresolved.lstat()
    except OSError as error:
        raise ReportError(f"incomplete analysis: {label} is missing: {error}") from error
    if stat.S_ISLNK(details.st_mode) or not stat.S_ISREG(details.st_mode):
        raise ReportError(f"incomplete analysis: {label} is not a regular non-symlink file")
    if stat.S_IMODE(details.st_mode) != 0o444:
        raise ReportError(f"incomplete analysis: {label} is not sealed mode 0444")
    path = unresolved.resolve()
    try:
        path.relative_to(repository_root.resolve())
    except ValueError as error:
        raise ReportError(
            f"incomplete analysis: {label} escapes the repository/results root"
        ) from error
    return path


def _effective_prompt_text(
    inputs: ReportInputs,
    protocol: Mapping[str, Any],
    record: Mapping[str, Any],
) -> str:
    task_id = record.get("task_id")
    task = next((item for item in inputs.tasks if item.get("task_id") == task_id), None)
    if not isinstance(task, Mapping):
        raise ReportError(f"incomplete analysis: no task metadata for prompt {task_id}")
    common = protocol.get("common_prompt")
    supplements = protocol.get("condition_supplements")
    supplement = supplements.get("L") if isinstance(supplements, Mapping) else None
    formal = task.get("formal_statement")
    context_raw = task.get("context_file")
    target_raw = formal.get("target_file") if isinstance(formal, Mapping) else None
    if not isinstance(context_raw, str) or not isinstance(target_raw, str):
        raise ReportError(f"incomplete analysis: task {task_id} omits prompt source paths")
    if not isinstance(common, Mapping) or not isinstance(common.get("path"), str):
        raise ReportError("incomplete analysis: common prompt descriptor is malformed")
    common_path = _find_repository_file(
        inputs.benchmark_root, common.get("path"), "common prompt"
    )
    context_path = _find_repository_file(
        inputs.benchmark_root, context_raw, f"{task_id} prompt context"
    )
    target_path = _find_repository_file(
        inputs.benchmark_root, target_raw, f"{task_id} fixed target"
    )
    try:
        sections = [common_path.read_text(encoding="utf-8").rstrip()]
        if record.get("condition") == "L":
            if not isinstance(supplement, Mapping) or not isinstance(
                supplement.get("path"), str
            ):
                raise ReportError("incomplete analysis: condition L has no prompt supplement")
            supplement_path = _find_repository_file(
                inputs.benchmark_root,
                supplement.get("path"),
                "condition-L prompt supplement",
            )
            sections.append(supplement_path.read_text(encoding="utf-8").rstrip())
        elif record.get("condition") != "N":
            raise ReportError("incomplete analysis: prompt record has an invalid condition")
        sections.extend(
            (
                "## Task context\n\n" + context_path.read_text(encoding="utf-8").rstrip(),
                "## Fixed Lean target\n\n```lean\n"
                + target_path.read_text(encoding="utf-8").rstrip()
                + "\n```",
            )
        )
    except (OSError, UnicodeError) as error:
        raise ReportError(f"incomplete analysis: cannot reconstruct prompt bytes: {error}") from error
    return "\n\n".join(sections) + "\n"


def _rederive_prompt_release_evidence(
    record: Mapping[str, Any],
    config: Mapping[str, Any],
    effective_prompt: str,
    *,
    repository_root: Path,
) -> dict[str, Any]:
    """Independently rederive one authenticated measurement clock origin."""

    run_id = record.get("run_id")
    top = record.get("prompt_release")
    limits = config.get("limits")
    if (
        not isinstance(limits, Mapping)
        or limits.get("prompt_startup_timeout_seconds") != 120
        or isinstance(limits.get("prompt_startup_timeout_seconds"), bool)
    ):
        raise ReportError(
            "incomplete analysis: prompt startup timeout is not frozen separately at 120 seconds"
        )
    wall_limit = limits.get("wall_clock_seconds")
    if (
        not isinstance(wall_limit, (int, float))
        or isinstance(wall_limit, bool)
        or wall_limit <= 0
    ):
        raise ReportError("incomplete analysis: the scored wall limit is invalid")
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
    prompt_bytes = effective_prompt.encode("utf-8")
    prompt_sha = hashlib.sha256(prompt_bytes).hexdigest()
    if (
        not isinstance(top, Mapping)
        or set(top) != expected_top_fields
        or top.get("schema_version") != 1
        or top.get("protocol_version") != PROMPT_RELEASE_PROTOCOL_VERSION
        or top.get("required") is not True
        or top.get("status") != "released_authenticated"
        or top.get("authenticated") is not True
        or top.get("timing_exact") is not True
        or top.get("useful_work_basis") != "authenticated_release"
        or top.get("startup_timeout_seconds") != PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS
        or top.get("startup_timeout_triggered") is not False
        or top.get("go_minimum_release_window_seconds")
        != PROMPT_RELEASE_GO_MINIMUM_WINDOW_SECONDS
        or not _hex_digest(top.get("handshake_nonce"))
        or top.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or top.get("effective_prompt_sha256") != prompt_sha
        or top.get("effective_prompt_bytes") != len(prompt_bytes)
        or top.get("error") is not None
    ):
        raise ReportError(
            f"incomplete analysis: run {run_id} has an inexact prompt-release summary"
        )
    provenance = record.get("prompt_provenance")
    effective = provenance.get("effective_prompt") if isinstance(provenance, Mapping) else None
    if (
        not isinstance(effective, Mapping)
        or effective.get("sha256") != prompt_sha
        or effective.get("bytes") != len(prompt_bytes)
    ):
        raise ReportError(
            f"incomplete analysis: run {run_id} prompt release is not provenance-bound"
        )
    stale = top.get("stale_artifacts_removed")
    if (
        not isinstance(stale, list)
        or stale != sorted(set(stale))
        or any(not isinstance(item, str) or not Path(item).is_absolute() for item in stale)
    ):
        raise ReportError(f"incomplete analysis: run {run_id} has invalid stale artifacts")

    paths = top.get("artifact_paths")
    command = record.get("agent_command")
    if (
        not isinstance(paths, Mapping)
        or set(paths) != {"ready", "go", "release"}
        or not isinstance(command, list)
        or not all(isinstance(item, str) for item in command)
    ):
        raise ReportError(f"incomplete analysis: run {run_id} lacks prompt command binding")
    command_paths = {
        "ready": _prompt_command_option(command, "--prompt-ready-output"),
        "go": _prompt_command_option(command, "--prompt-go-input"),
        "release": _prompt_command_option(command, "--prompt-release-output"),
    }
    nonce = top.get("handshake_nonce")
    if (
        command_paths != dict(paths)
        or any(not isinstance(value, str) or not Path(value).is_absolute() for value in command_paths.values())
        or _prompt_command_option(command, "--prompt-handshake-nonce") != nonce
        or _prompt_command_option(command, "--prompt-run-id") != run_id
    ):
        raise ReportError(f"incomplete analysis: run {run_id} prompt paths/identity are unbound")
    usage_output = _prompt_command_option(command, "--usage-output")
    if not isinstance(usage_output, str) or not Path(usage_output).is_absolute():
        raise ReportError(f"incomplete analysis: run {run_id} has no trusted usage path")
    usage_path = Path(usage_output)
    suffix = ".usage.json"
    base = usage_path.name[: -len(suffix)] if usage_path.name.endswith(suffix) else usage_path.stem
    expected_names = {
        "ready": f"{base}.prompt-ready.json",
        "go": f"{base}.prompt-go.json",
        "release": f"{base}.prompt-release.json",
    }
    if not base or base in (".", "..") or any(
        Path(command_paths[name]).parent != usage_path.parent
        or Path(command_paths[name]).name != expected_names[name]
        for name in expected_names
    ):
        raise ReportError(f"incomplete analysis: run {run_id} prompt paths are not usage-derived")

    agent = record.get("agent")
    usage = record.get("token_usage")
    root_thread_id = usage.get("root_thread_id") if isinstance(usage, Mapping) else None
    if not isinstance(agent, Mapping) or not isinstance(root_thread_id, str) or not root_thread_id:
        raise ReportError(f"incomplete analysis: run {run_id} has no rooted agent identity")
    common = {
        "schema_version": 1,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "handshake_nonce": nonce,
        "run_id": run_id,
        "condition": record.get("condition"),
        "model": agent.get("model"),
        "reasoning_effort": agent.get("reasoning_effort"),
        "root_thread_id": root_thread_id,
        "turn_start_request_id": 3,
        "effective_prompt_sha256": prompt_sha,
        "effective_prompt_bytes": len(prompt_bytes),
        "adapter_name": "codex_isolated.py",
        "adapter_version": "1",
        "app_server_client_name": "highambench-isolated",
        "app_server_client_version": "1",
        "elapsed_clock": "CLOCK_MONOTONIC",
    }
    records: dict[str, Mapping[str, Any]] = {}
    for name, (hash_field, kind, expected_suffix) in PROMPT_RELEASE_ARTIFACTS.items():
        path_name = "release" if name == "released" else name
        descriptor = top.get(name)
        nested = descriptor.get("record") if isinstance(descriptor, Mapping) else None
        extra = {
            "ready": {"kind", "turn_start_write_state", "ready_at_monotonic_ns", "ready_at_unix_ns"},
            "go": {
                "kind",
                "ready_sha256",
                "turn_start_write_authorized",
                "authorized_at_monotonic_ns",
                "authorized_at_unix_ns",
            },
            "released": {
                "kind",
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
        }[name]
        if (
            not isinstance(descriptor, Mapping)
            or set(descriptor) != {"path", "file_sha256", "record_sha256", "record"}
            or descriptor.get("path") != paths.get(path_name)
            or not str(descriptor.get("path", "")).endswith(expected_suffix)
            or not _hex_digest(descriptor.get("file_sha256"))
            or not _hex_digest(descriptor.get("record_sha256"))
            or not isinstance(nested, Mapping)
            or set(nested) != PROMPT_RELEASE_COMMON_FIELDS | extra | {hash_field}
            or any(nested.get(field) != value for field, value in common.items())
            or nested.get("kind") != kind
            or nested.get(hash_field) != descriptor.get("record_sha256")
            or _document_digest({key: value for key, value in nested.items() if key != hash_field})
            != nested.get(hash_field)
        ):
            raise ReportError(f"incomplete analysis: run {run_id} prompt {name} record is invalid")
        path = _sealed_prompt_artifact(
            descriptor.get("path"), repository_root, f"run {run_id} prompt {name} artifact"
        )
        payload = path.read_bytes()
        canonical = (
            json.dumps(nested, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        if payload != canonical or hashlib.sha256(payload).hexdigest() != descriptor.get("file_sha256"):
            raise ReportError(f"incomplete analysis: run {run_id} prompt {name} file was altered")
        records[name] = nested

    ready, go, released = records["ready"], records["go"], records["released"]
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
    if any(not isinstance(value, int) or isinstance(value, bool) or value <= 0 for value in timestamps):
        raise ReportError(f"incomplete analysis: run {run_id} prompt timestamps are invalid")
    if not (timestamps[0] <= timestamps[2] <= timestamps[4] <= timestamps[6] and timestamps[5] <= timestamps[7]):
        raise ReportError(f"incomplete analysis: run {run_id} prompt timestamp order is invalid")
    if (
        ready.get("turn_start_write_state") != "not_started"
        or go.get("ready_sha256") != ready.get("ready_sha256")
        or go.get("turn_start_write_authorized") is not True
        or released.get("ready_sha256") != ready.get("ready_sha256")
        or released.get("go_sha256") != go.get("go_sha256")
        or released.get("turn_start_write_state") != "flushed"
        or released.get("timestamp_capture_point") != "immediately_before_turn_start_write"
    ):
        raise ReportError(f"incomplete analysis: run {run_id} prompt chain is inconsistent")
    wire = _prompt_turn_start_wire(
        prompt=effective_prompt,
        root_thread_id=root_thread_id,
        model=str(agent.get("model")),
        reasoning_effort=str(agent.get("reasoning_effort")),
    )
    if (
        released.get("turn_start_request_sha256") != hashlib.sha256(wire).hexdigest()
        or released.get("turn_start_request_bytes") != len(wire)
    ):
        raise ReportError(f"incomplete analysis: run {run_id} released the wrong prompt wire")

    release_ns = released["released_at_monotonic_ns"]
    deadline_ns = release_ns + int(float(wall_limit) * 1_000_000_000)
    first_valid = record.get("first_valid_seconds")
    if "authenticated CLOCK_MONOTONIC turn/start write" not in str(record.get("time_measurement")):
        raise ReportError(f"incomplete analysis: run {run_id} has the wrong timing origin")
    if record.get("pass") is True:
        if (
            not isinstance(first_valid, (int, float))
            or isinstance(first_valid, bool)
            or first_valid < 0
            or first_valid >= wall_limit
            or record.get("scored_elapsed_seconds") != first_valid
            or record.get("actual_stop_seconds", first_valid) < first_valid
        ):
            raise ReportError(f"incomplete analysis: run {run_id} has invalid elapsed timing")
    elif first_valid is not None:
        raise ReportError(f"incomplete analysis: failed run {run_id} has first-valid timing")

    frozen = config.get("frozen_environment")
    is_ultra = isinstance(frozen, Mapping) and frozen.get("model_reasoning_effort") == "ultra"
    ultra_timing: bool | None = None
    if is_ultra and record.get("pass") is True:
        boundary = usage.get("submission_boundary") if isinstance(usage, Mapping) else None
        ultra_summary = record.get("ultra_submission_boundary")
        barrier_artifacts = ultra_summary.get("artifacts") if isinstance(ultra_summary, Mapping) else None
        request_descriptor = barrier_artifacts.get("request") if isinstance(barrier_artifacts, Mapping) else None
        if not isinstance(boundary, Mapping) or not isinstance(request_descriptor, Mapping):
            raise ReportError(f"incomplete analysis: run {run_id} lacks publication evidence")
        request_path = _sealed_prompt_artifact(
            request_descriptor.get("path"), repository_root, f"run {run_id} submission request"
        )
        request_payload = request_path.read_bytes()
        try:
            request = json.loads(request_payload)
        except (UnicodeError, json.JSONDecodeError) as error:
            raise ReportError(f"incomplete analysis: run {run_id} request is malformed") from error
        if (
            not isinstance(request, Mapping)
            or not _hex_digest(request_descriptor.get("file_sha256"))
            or hashlib.sha256(request_payload).hexdigest() != request_descriptor.get("file_sha256")
            or request.get("request_sha256") != request_descriptor.get("record_sha256")
            or request.get("request_sha256") != boundary.get("request_sha256")
            or _document_digest({key: value for key, value in request.items() if key != "request_sha256"})
            != request.get("request_sha256")
            or request_payload
            != (
                json.dumps(request, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
                + "\n"
            ).encode("utf-8")
            or request.get("request_published_at_monotonic_ns")
            != boundary.get("request_published_at_monotonic_ns")
            or request.get("request_published_at_unix_ns")
            != boundary.get("request_published_at_unix_ns")
        ):
            raise ReportError(f"incomplete analysis: run {run_id} request publication is unbound")
        _validate_nested_submission_wire_v5(
            request,
            f"run {run_id} submission request",
        )
        _validate_nested_submission_wire_v5(
            boundary,
            f"run {run_id} submission boundary",
        )
        request_order = _validate_submission_event_order_v5(
            request,
            f"run {run_id} submission request",
            require_event_timestamps=True,
        )
        boundary_order = _validate_submission_event_order_v5(
            boundary,
            f"run {run_id} submission boundary",
            require_event_timestamps=False,
        )
        if boundary_order != request_order or any(
            boundary.get(field) != request.get(field)
            for field in (
                "submission_event_order",
                "dynamic_call_observed_before_raw_response_completed",
                "raw_response_completed_before_dynamic_call_observed",
            )
        ):
            raise ReportError(
                f"incomplete analysis: run {run_id} request/boundary event order is unbound"
            )
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
            raise ReportError(
                f"incomplete analysis: run {run_id} lacks its schema-v5 provider close"
            )
        published = request.get("request_published_at_monotonic_ns")
        outer_exec_observed = request.get(
            "outer_raw_item_observed_at_monotonic_ns"
        )
        if (
            not isinstance(published, int)
            or isinstance(published, bool)
            or not isinstance(outer_exec_observed, int)
            or isinstance(outer_exec_observed, bool)
            or outer_exec_observed < release_ns
            or outer_exec_observed > published
            or published < release_ns
            or published >= deadline_ns
            or first_valid != round((published - release_ns) / 1_000_000_000, 6)
        ):
            raise ReportError(f"incomplete analysis: run {run_id} publication timing is invalid")
        ultra_timing = True
    verified = record.get("protocol", {}).get("verified") if isinstance(record.get("protocol"), Mapping) else None
    if not isinstance(verified, Mapping) or verified.get("authenticated_prompt_release") is not True:
        raise ReportError(f"incomplete analysis: run {run_id} protocol omits prompt release")
    return {
        "run_id": run_id,
        "valid": True,
        "artifact_set_count": 1,
        "artifact_file_count": 3,
        "artifact_content_verified": True,
        "released_at_monotonic_ns": release_ns,
        "measurement_deadline_monotonic_ns": deadline_ns,
        "ultra_request_publication_timing_verified": ultra_timing,
    }


def _validate_prompt_release_summary(
    inputs: ReportInputs,
    check: Mapping[str, Any],
    matrix_summary: Mapping[str, Any],
    selected_runs: Sequence[Mapping[str, Any]],
    protocol: Mapping[str, Any],
) -> Mapping[str, Any]:
    summary = check.get("prompt_release_authentication")
    evidence = summary.get("run_evidence") if isinstance(summary, Mapping) else None
    matrix_evidence = matrix_summary.get("run_evidence")
    if not isinstance(evidence, list) or not isinstance(matrix_evidence, list):
        raise ReportError("incomplete analysis: prompt-release authentication is missing")
    records = {
        item.get("run_id"): item.get("record")
        for item in matrix_evidence
        if isinstance(item, Mapping) and isinstance(item.get("record"), Mapping)
    }
    selected_ids = {run.get("run_id") for run in selected_runs}
    derived = []
    for run_id in sorted(selected_ids):
        record = records.get(run_id)
        if not isinstance(record, Mapping):
            raise ReportError("incomplete analysis: prompt release lacks a matrix record")
        prompt = _effective_prompt_text(inputs, protocol, record)
        derived.append(
            _rederive_prompt_release_evidence(
                record,
                inputs.config,
                prompt,
                repository_root=inputs.benchmark_root.parent.parent,
            )
        )
    recorded_by_id = {
        item.get("run_id"): item for item in evidence if isinstance(item, Mapping)
    }
    derived_by_id = {item["run_id"]: item for item in derived}
    if recorded_by_id != derived_by_id:
        raise ReportError(
            "incomplete analysis: prompt-release evidence was not independently reproducible"
        )
    count = len(selected_runs)
    if (
        not isinstance(summary, Mapping)
        or summary.get("schema_version") != 1
        or summary.get("protocol_version") != PROMPT_RELEASE_PROTOCOL_VERSION
        or summary.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or summary.get("timing_origin") != "authenticated_turn_start_write"
        or summary.get("ultra_success_endpoint")
        != (
            "authenticated_nested_submission_boundary_publication_after_"
            "outer_exec_raw_response_completion"
        )
        or summary.get("startup_timeout_seconds")
        != PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS
        or summary.get("startup_timeout_separate_from_scored_wall_limit") is not True
        or summary.get("selected_final_run_count") != count
        or summary.get("authenticated_release_count") != count
        or summary.get("retained_artifact_set_count") != count
        or summary.get("retained_artifact_file_count") != count * 3
        or summary.get("retained_artifacts_reauthenticated") is not True
        or summary.get("all_selected_final_releases_authenticated") is not True
    ):
        raise ReportError("incomplete analysis: prompt-release summary is inconsistent")
    return summary


def validate_report_inputs(inputs: ReportInputs) -> None:
    """Reject stale metadata, weak construction evidence, or partial measurements."""

    _validate_hashes_and_reviews(inputs)
    _validate_release_and_environment(inputs)
    analysis = inputs.analysis
    if analysis.get("kind") != "highambench-analysis":
        raise ReportError("incomplete analysis: input is not a highambench-analysis document")
    expected_t4_coverage = _t4_coverage_rows(inputs.tasks)
    observed_t4_coverage = analysis.get("whole_paper_t4_coverage", [])
    if observed_t4_coverage != expected_t4_coverage:
        raise ReportError(
            "incomplete analysis: T4 whole-paper coverage is missing or stale"
        )
    if analysis.get("malformed_input_lines") != []:
        raise ReportError("incomplete analysis: malformed input lines were not ruled out")
    check = analysis.get("result_set_check")
    if not isinstance(check, Mapping) or check.get("ok") is not True:
        raise ReportError("incomplete analysis: the result-set completeness check did not pass")
    _validate_freeze_link(inputs, check)
    prompt_protocol = _validated_prompt_protocol(inputs, check)
    _validate_construction(inputs)
    if check.get("system_error_handling_complete") is not True:
        raise ReportError("incomplete analysis: system-error rerun handling is unresolved")
    if analysis.get("pair_problems") != []:
        raise ReportError("incomplete analysis: paired-run problems remain")

    recorded_digests = check.get("metadata_document_sha256")
    if not isinstance(recorded_digests, Mapping):
        raise ReportError("incomplete analysis: frozen metadata digests are missing")
    current_digests = {
        "config": _document_digest(inputs.config),
        "manifest": _document_digest(inputs.manifest),
        "run_order": _document_digest(inputs.run_order),
    }
    if any(recorded_digests.get(name) != digest for name, digest in current_digests.items()):
        raise ReportError("stale analysis: config, manifest, or run order changed after analysis")

    expected_agents = check.get("expected_agents")
    expected_per_agent = check.get("expected_final_runs_per_agent")
    selected_count = check.get("selected_final_record_count")
    if (
        not isinstance(expected_agents, int)
        or isinstance(expected_agents, bool)
        or expected_agents <= 0
        or not isinstance(expected_per_agent, int)
        or isinstance(expected_per_agent, bool)
        or expected_per_agent <= 0
        or selected_count != expected_agents * expected_per_agent
    ):
        raise ReportError("incomplete analysis: final record count does not equal the planned matrix")

    per_run = _require_list(analysis.get("per_run_results"), "per-run results")
    if not all(isinstance(run, Mapping) for run in per_run):
        raise ReportError("incomplete analysis: per-run results are malformed")
    if analysis.get("input_run_count") != len(per_run):
        raise ReportError("incomplete analysis: raw run count disagrees with the per-run table")
    selected_ids = check.get("selected_final_run_ids")
    if (
        not isinstance(selected_ids, list)
        or len(selected_ids) != selected_count
        or len(set(selected_ids)) != len(selected_ids)
    ):
        raise ReportError("incomplete analysis: selected final run IDs are missing or repeated")
    runs_by_id = {run.get("run_id"): run for run in per_run if isinstance(run.get("run_id"), str)}
    if any(run_id not in runs_by_id for run_id in selected_ids):
        raise ReportError("incomplete analysis: a selected final run is absent from per-run results")
    selected_runs = [runs_by_id[run_id] for run_id in selected_ids]

    frozen = inputs.config.get("frozen_environment")
    is_ultra = bool(
        isinstance(frozen, Mapping)
        and frozen.get("model_reasoning_effort") == "ultra"
    )
    matrix_record_summary = _validate_matrix_record_summary(
        check, selected_runs, ultra=is_ultra
    )
    if prompt_protocol is not None:
        _validate_prompt_release_summary(
            inputs,
            check,
            matrix_record_summary,
            selected_runs,
            prompt_protocol,
        )

    if is_ultra:
        _validate_ultra_accounting_summary(check, selected_runs)
        _validate_ultra_boundary_summary(check, selected_runs)

    condition_rows, task_rows, pair_rows, task_pair_rows, observational = _analysis_tables(analysis)
    reference = check.get("reference_compliant") is True
    if reference != (analysis.get("official_scores_valid") is True):
        raise ReportError("incomplete analysis: official-score status is inconsistent")
    if observational:
        if check.get("analysis_profile") != "observational_pilot":
            raise ReportError("incomplete analysis: non-reference data lacks the observational profile")
        pilot = analysis["observational_pilot_results"]
        if pilot.get("official_scores_valid") is not False or pilot.get("run_count") != selected_count:
            raise ReportError("incomplete analysis: observational run count or score label is inconsistent")
        reasons = pilot.get("nonreference_reasons")
        if not isinstance(reasons, list) or not reasons:
            raise ReportError("incomplete analysis: observational data has no recorded protocol reasons")
        for rows in (condition_rows, task_rows, pair_rows, task_pair_rows):
            if any(row.get("result_status") != "observational_not_reference_score" for row in rows):
                raise ReportError("incomplete analysis: an observational row lacks its non-score label")
        if any(
            analysis.get(name) != []
            for name in (
                "condition_summaries",
                "per_task_summaries",
                "paired_comparisons",
                "per_task_paired_comparisons",
            )
        ):
            raise ReportError("incomplete analysis: invalid official-score tables must remain empty")
    elif check.get("analysis_profile") != "reference":
        raise ReportError("incomplete analysis: official data lacks the reference profile")

    _check_matrix_coverage(
        inputs, selected_runs, condition_rows, task_rows, pair_rows, task_pair_rows
    )
    for row in (*pair_rows, *task_pair_rows):
        paper_count = _bootstrap_paper_count(inputs, row)
        informative_bootstrap = paper_count > 1
        bootstrap = row.get("bootstrap")
        if (
            not isinstance(bootstrap, Mapping)
            or bootstrap.get("paper_count") != paper_count
            or bootstrap.get("informative") is not informative_bootstrap
            or (paper_count == 1 and not bootstrap.get("note"))
        ):
            raise ReportError(
                "incomplete analysis: paired bootstrap metadata disagrees with the paper corpus"
            )

    deviations = inputs.environment.get("known_reference_protocol_deviations")
    if not isinstance(deviations, list) or not all(isinstance(item, str) for item in deviations):
        raise ReportError("environment metadata has no reference-protocol deviation list")
    joined = " ".join(deviations).lower()
    for topic in ("seed", "oci", "provider connection", "token"):
        if topic not in joined:
            raise ReportError(f"environment metadata does not explain the {topic} deviation")
    if prompt_protocol is not None and not any(
        topic in joined for topic in ("prompt", "signpost")
    ):
        raise ReportError(
            "environment metadata does not explain the signposted-prompt deviation"
        )


def latex_escape(value: Any) -> str:
    if value is None:
        return "--"
    text = str(value).translate(
        str.maketrans(
            {
                "–": "--",
                "—": "---",
                "’": "'",
                "“": '"',
                "”": '"',
                "×": " x ",
                "≤": " less than or equal to ",
                "≥": " greater than or equal to ",
                "γ": "gamma",
                "Ŝ": "S-hat",
            }
        )
    )
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


def _hash_tex(value: Any) -> str:
    if not isinstance(value, str):
        return "--"
    chunks = [latex_escape(value[index : index + 8]) for index in range(0, len(value), 8)]
    return r"\texttt{" + r"\allowbreak{}".join(chunks) + "}"


def _inline_code(value: Any) -> str:
    text = latex_escape(value)
    text = text.replace(".", r".\allowbreak{}")
    return r"\texttt{" + text + "}"


def _ascii_lean(source: str) -> str:
    replacements = {
        "ℕ": "Nat",
        "ℝ": "Real",
        "∀": "forall",
        "∃": "exists",
        "→": "->",
        "≤": "<=",
        "≥": ">=",
        "∧": "/\\",
        "∨": "\\/",
        "∑": "sum",
        "δ": "delta",
        "α": "alpha",
        "β": "beta",
        "γ": "gamma",
        "ₙ": "_n",
        "Ŝ": "S_hat",
        "…": "...",
    }
    for old, new in replacements.items():
        source = source.replace(old, new)
    source = "".join(character if ord(character) < 128 else "?" for character in source)
    # Do not let source text terminate the LaTeX listing that contains it.
    return source.replace(r"\end{lstlisting}", r"\end {lstlisting}")


def _fmt_number(value: Any, digits: int = 3) -> str:
    if value is None:
        return "--"
    if isinstance(value, bool):
        return "yes" if value else "no"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def _fmt_bytes(value: Any) -> str:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        return "--"
    return f"{value} bytes ({value / (1024 ** 3):.1f} GiB)"


def _fmt_rate(value: Any) -> str:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return "--"
    return f"{100 * float(value):.1f}\\%"


def _fmt_delta(value: Any, *, scale: float = 1.0, digits: int = 1) -> str:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return "--"
    return f"{scale * float(value):+.{digits}f}"


def _range(row: Mapping[str, Any], metric: str, *, scale: float = 1.0, digits: int = 1) -> str:
    bootstrap = row.get("bootstrap")
    ranges = bootstrap.get("ranges") if isinstance(bootstrap, Mapping) else None
    interval = ranges.get(metric) if isinstance(ranges, Mapping) else None
    if not isinstance(interval, Mapping):
        return "--"
    low, high = interval.get("low"), interval.get("high")
    if not all(isinstance(value, (int, float)) and not isinstance(value, bool) for value in (low, high)):
        return "--"
    return f"[{scale * float(low):.{digits}f}, {scale * float(high):.{digits}f}]"


def _longtable(
    caption: str,
    specification: str,
    headers: Sequence[str],
    rows: Iterable[Sequence[str]],
    *,
    size: str = "small",
) -> list[str]:
    header = " & ".join(headers) + r" \\"
    lines = [
        rf"\begin{{{size}}}",
        rf"\begin{{longtable}}{{{specification}}}",
        rf"\caption{{{caption}}}\\",
        r"\toprule",
        header,
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        header,
        r"\midrule",
        r"\endhead",
    ]
    for row in rows:
        lines.append(" & ".join(row) + r" \\")
    lines.extend([r"\bottomrule", r"\end{longtable}", rf"\end{{{size}}}"])
    return lines


def _manifest_targets(inputs: ReportInputs) -> list[Mapping[str, Any]]:
    return [target for _paper_id, target in _task_records(inputs.manifest)[1]]


def _condition_values(row: Mapping[str, Any], observational: bool) -> tuple[Any, ...]:
    if observational:
        return (
            row.get("observational_runs"),
            row.get("observed_passes"),
            row.get("observed_pass_rate"),
            row.get("median_observed_seconds"),
            row.get("median_observed_model_tokens"),
            row.get("observed_passed_library_use"),
        )
    return (
        row.get("scored_runs"),
        row.get("passes"),
        row.get("pass_rate"),
        row.get("median_scored_seconds"),
        row.get("median_model_tokens"),
        row.get("passed_library_use"),
    )


def _pair_values(row: Mapping[str, Any], observational: bool) -> tuple[Any, Any, Any]:
    if observational:
        return (
            row.get("observed_pass_rate_change"),
            row.get("median_observed_paired_time_change"),
            row.get("median_observed_paired_token_change"),
        )
    return (
        row.get("pass_rate_change"),
        row.get("median_paired_time_change"),
        row.get("median_paired_token_change"),
    )


def render_report(inputs: ReportInputs) -> str:
    """Render a validated input bundle as one standalone LaTeX document."""

    # Validate again so callers cannot construct a ReportInputs object by hand
    # and bypass the final-matrix refusal.
    validate_report_inputs(inputs)
    analysis = inputs.analysis
    check = analysis["result_set_check"]
    conditions, tasks, pairs, task_pairs, observational = _analysis_tables(analysis)
    selected_ids = set(check["selected_final_run_ids"])
    selected_runs = [
        run for run in analysis["per_run_results"] if run.get("run_id") in selected_ids
    ]
    manifest_papers = list(inputs.manifest["papers"])
    paper_records = {str(paper["paper_id"]): paper for paper in inputs.papers}
    paper_count = len(manifest_papers)
    task_count = len(inputs.tasks)
    measured_tasks = _selected_tasks(inputs.tasks)
    measured_task_count = len(measured_tasks)
    measured_paper_count = len(
        {str(task.get("paper_id")) for task in measured_tasks}
    )
    t4_coverage = _t4_coverage_rows(inputs.tasks)
    repetitions = inputs.config.get("repetitions", [])
    pair_count = measured_task_count * len(repetitions)
    run_count = pair_count * 2
    specification = inputs.manifest["specification"]
    frozen = inputs.config["frozen_environment"]
    prompt_protocol = _validated_prompt_protocol(inputs, check)
    environment = inputs.environment
    isolation = environment.get("isolation", {})
    limits = inputs.config.get("limits", {})
    token_canary = inputs.evidence[TOKEN_CONTROL_CANARY_KEY]
    token_canary_summary = inputs.freeze_check["token_control_canary"]
    token_canary_controls = token_canary["controls"]
    token_canary_outcome = token_canary["outcome"]
    token_canary_prompt_release = token_canary_summary["prompt_release"]
    prompt_release_summary = check.get("prompt_release_authentication")
    ultra_token_accounting = _uses_ultra_token_control(
        inputs.config.get("token_control")
    )
    ultra_submission_accounting = (
        ultra_token_accounting
        and frozen.get("model_reasoning_effort") == "ultra"
    )
    ultra_canary_summary = (
        inputs.freeze_check.get("ultra_orchestration_canary")
        if ultra_submission_accounting
        else None
    )
    ultra_boundary_summary = (
        check.get("ultra_submission_boundaries")
        if ultra_submission_accounting
        else None
    )
    ultra_accounting_summary = (
        check.get("ultra_accounting_projections")
        if ultra_submission_accounting
        else None
    )

    lines: list[str] = [
        r"\documentclass[10pt]{article}",
        r"\usepackage[margin=0.68in]{geometry}",
        r"\usepackage[T1]{fontenc}",
        r"\usepackage[utf8]{inputenc}",
        r"\usepackage{amsmath,amssymb}",
        r"\usepackage{array,booktabs,longtable,tabularx}",
        r"\usepackage[table]{xcolor}",
        r"\usepackage{listings}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\setlength{\LTpre}{4pt}",
        r"\setlength{\LTpost}{8pt}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{5pt}",
        r"\newcolumntype{P}[1]{>{\raggedright\arraybackslash}p{#1}}",
        r"\lstset{basicstyle=\ttfamily\footnotesize,breaklines=true,columns=fullflexible,keepspaces=true,showstringspaces=false}",
        r"\sloppy",
        r"\title{HighamBench: Construction and Measurement Report}",
        r"\author{Benchmark construction and annotation performed by Codex at the project owner's request}",
        r"\date{}",
        r"\begin{document}",
        r"\maketitle",
    ]

    lines.extend(
        [
            r"\begin{center}",
            r"\fbox{\parbox{0.92\linewidth}{\centering\textbf{Private benchmark measurement.} This report records the complete checked matrix and is not approved for public release.}}",
            r"\end{center}",
        ]
    )

    lines.extend(
        [
            r"\section{What was built}",
            "A benchmark is a fixed test used to compare two setups. This benchmark asks whether access to the NumStability library, meaning a reusable collection of Lean definitions and proofs, helps one proof-making agent finish the same Lean tasks. An agent is a program that asks a language model to do the work and can use allowed local tools. A language model is the text-producing service behind the agent. Lean is a language whose checker verifies each proof step.",
            "This measurement snapshot contains "
            + latex_escape(paper_count)
            + " paper(s) and "
            + latex_escape(task_count)
            + " formalized task record(s), of which "
            + latex_escape(measured_task_count)
            + " T1--T3 task(s) form the measured matrix and "
            + latex_escape(len(t4_coverage))
            + " T4 record(s) form a separate whole-paper coverage stratum: "
            + "; ".join(
                latex_escape(paper.get("paper_id"))
                + ", ``"
                + latex_escape(
                    paper.get("citation", {}).get(
                        "title", paper_records[str(paper["paper_id"])].get("title")
                    )
                )
                + ".''"
                for paper in manifest_papers
            )
            + " Each paper version is fixed for this measurement snapshot. A theorem is a mathematical claim together with a proof. A task is one fixed theorem statement plus the short paper context needed to understand it. N is the setup with no NumStability files. L is the setup with NumStability available."
            + (
                " This snapshot uses the frozen signposted-library-v1 prompt treatment: only L receives a neutral library-location and search/import supplement."
                if prompt_protocol is not None
                else ""
            ),
            "Codex performed the requested source labeling and the recorded fresh-context reviews. In this sentence, labeling means choosing the paper result, recording its exact location, and assigning its difficulty type before measurement. Review outcomes, including retained novelty rejections, are reported without alteration. The private construction proofs were used only to check that each task was possible. They were never shown during a measured run.",
            r"\subsection{Source identity and fixed fingerprints}",
            "SHA-256 is a 64-character content fingerprint. If checked content changes, its fingerprint should change. Most rows below fingerprint exact file bytes. The environment bundle and frozen-run check first put their JSON data, meaning structured text records, into one fixed key order so harmless spacing does not change the identity. Together these fingerprints tie this report to the exact source and setup.",
        ]
    )
    hash_rows: list[Sequence[str]] = [
        (
            "Paper PDF " + latex_escape(paper.get("paper_id")),
            _hash_tex(paper.get("source", {}).get("sha256")),
            latex_escape(paper.get("source", {}).get("local_path")),
        )
        for paper in manifest_papers
    ] + [
        (
            "Benchmark specification PDF",
            _hash_tex(specification.get("sha256")),
            latex_escape(specification.get("local_path")),
        ),
        (
            "Environment bundle",
            _hash_tex(environment.get("environment_bundle_sha256")),
            latex_escape(environment.get("environment_id")),
        ),
        (
            "Common agent prompt" if prompt_protocol is not None else "Agent prompt",
            _hash_tex(frozen.get("prompt_sha256")),
            (
                "The fixed common instructions sent in every run"
                if prompt_protocol is not None
                else "The fixed instructions sent in every run"
            ),
        ),
    ] + (
        [
            (
                "Condition-L prompt supplement",
                _hash_tex(
                    prompt_protocol["condition_supplements"]["L"]["sha256"]
                ),
                latex_escape(prompt_protocol["condition_supplements"]["L"]["path"]),
            )
        ]
        if prompt_protocol is not None
        else []
    ) + [
        (
            "Evaluation release",
            _hash_tex(frozen.get("release_manifest_sha256")),
            latex_escape(frozen.get("release_manifest")),
        ),
        (
            "Frozen-run check",
            _hash_tex(_document_digest(inputs.freeze_check)),
            latex_escape("freeze_check.json beside the measured result set"),
        ),
        (
            "Compiled Lean setup",
            _hash_tex(frozen.get("compiled_environment_summary_sha256")),
            latex_escape(frozen.get("compiled_environment_summary")),
        ),
        (
            "Python executable",
            _hash_tex(frozen.get("python_binary_sha256")),
            "Python " + latex_escape(frozen.get("python_version")),
        ),
        (
            "Pruned package view list",
            _hash_tex(frozen.get("packages_runtime_manifest_sha256")),
            latex_escape(frozen.get("packages_runtime_manifest")),
        ),
        (
            "NumStability source list",
            _hash_tex(frozen.get("numstability_source_manifest_sha256")),
            latex_escape(frozen.get("numstability_source_manifest")),
        ),
        (
            "Pruned NumStability compiled list",
            _hash_tex(frozen.get("numstability_compiled_manifest_sha256")),
            latex_escape(frozen.get("numstability_compiled_manifest")),
        ),
    ]
    for shared in inputs.manifest.get("controlled_shared_files", []):
        hash_rows.append(
            ("Shared Lean setting", _hash_tex(shared.get("sha256")), latex_escape(shared.get("path")))
        )
    for target in sorted(_manifest_targets(inputs), key=lambda item: str(item.get("tier"))):
        lean_target = target.get("lean_target", {})
        hash_rows.append(
            (
                str(target.get("task_id")) + " target",
                _hash_tex(lean_target.get("controlled_file_sha256")),
                latex_escape(lean_target.get("file")),
            )
        )
    lines.extend(
        _longtable(
            "Fixed source and setup fingerprints",
            "P{0.19\\linewidth}P{0.42\\linewidth}P{0.32\\linewidth}",
            ("Item", "SHA-256 fingerprint", "Meaning or file"),
            hash_rows,
            size="footnotesize",
        )
    )
    for paper in manifest_papers:
        source = paper.get("source", {})
        rights_note = source.get("rights_note") if isinstance(source, Mapping) else None
        if rights_note:
            lines.append(
                "Source-copy note for "
                + latex_escape(paper.get("paper_id"))
                + ": "
                + latex_escape(rights_note)
            )

    lines.extend(
        [
            r"\section{T1--T3 difficulty tasks and T4 whole-paper coverage}",
            "T1, T2, and T3 are difficulty labels fixed before measurement. T1 means direct use: a close library result already exists. T2 means combine: several existing facts and small new steps must be joined. T3 means extend: the library does not contain the complete result, so a substantial new proof step is required. T4 is not a harder difficulty tier; it is a separate whole-paper formalization corpus and is not included in the T1--T3 overall score.",
        ]
    )
    manifest_by_task = {item.get("task_id"): item for item in _manifest_targets(inputs)}
    for task in inputs.tasks:
        task_id = str(task.get("task_id"))
        target = manifest_by_task[task_id]
        tier = str(task.get("tier"))
        if tier == "T4":
            continue
        lines.extend(
            [
                rf"\subsection{{{latex_escape(task_id)}: {latex_escape(target.get('title'))}}}",
                "Decision: this paper has a "
                + latex_escape(tier)
                + " result. "
                + latex_escape(task.get("tier_rationale", target.get("tier_reason"))),
                "Chosen claim: " + latex_escape(task.get("informal_statement", target.get("informal_statement_paraphrase"))),
                "Paper anchors, meaning the exact places used to check the claim:",
                r"\begin{itemize}",
            ]
        )
        locations = task.get("source_locations")
        if not isinstance(locations, list) or not locations:
            locations = target.get("source_locations", [])
        for location in locations:
            if not isinstance(location, Mapping):
                continue
            anchor = location.get("equation") or location.get("anchor") or "nearby text"
            lines.append(
                r"\item "
                + latex_escape(location.get("section"))
                + ", "
                + latex_escape(anchor)
                + "; journal/printed page "
                + latex_escape(location.get("printed_page", location.get("journal_page")))
                + ", PDF page "
                + latex_escape(location.get("pdf_page"))
                + ". Role: "
                + latex_escape(location.get("role"))
                + "."
            )
        lines.extend([r"\end{itemize}", "Fixed Lean theorem statement:"])
        formal = task.get("formal_statement")
        if not isinstance(formal, Mapping) or not isinstance(formal.get("lean_header"), str):
            raise ReportError(f"task {task_id} has no fixed Lean theorem header")
        lines.extend(
            [
                r"\begin{lstlisting}",
                _ascii_lean(formal["lean_header"]),
                r"\end{lstlisting}",
                "Plain meaning: " + latex_escape(formal.get("plain_language")) + " "
                + latex_escape(task.get("interpretation_warning", "")),
            ]
        )

    if t4_coverage:
        lines.extend(
            [
                r"\subsection{T4 whole-paper formalization coverage}",
                "Every included paper claim is assigned to a review unit, every required Lean declaration is covered, and every recorded claim review is accepted. The designated holes are the public theorem/lemma skeletons compiled in both N and L; they are not private gold proofs.",
            ]
        )
        lines.extend(
            _longtable(
                "Authenticated T4 inventory, declaration, and review-unit coverage",
                "P{0.13\\linewidth}rrrrrrrr",
                (
                    "Task",
                    "Inventory",
                    "Included",
                    "Excluded",
                    "Decls.",
                    "Units",
                    "Accepted",
                    "Holes",
                    "Ready",
                ),
                (
                    (
                        latex_escape(row["task_id"]),
                        latex_escape(row["source_inventory_count"]),
                        latex_escape(row["included_source_count"]),
                        latex_escape(row["excluded_source_count"]),
                        latex_escape(row["declaration_count"]),
                        latex_escape(row["review_unit_count"]),
                        latex_escape(row["accepted_review_count"]),
                        latex_escape(row["controlled_sorry_count"]),
                        latex_escape(row["measurement_ready"]),
                    )
                    for row in t4_coverage
                ),
                size="footnotesize",
            )
        )

    search_rows: list[Sequence[str]] = []
    search_task_ids: set[str] = set()
    for evidence_name, target_search in sorted(inputs.evidence.items()):
        if not evidence_name.startswith("exact_target_search"):
            continue
        for finding in target_search.get("task_findings", []):
            search_task_ids.add(str(finding.get("task_id")))
            search_rows.append(
                (
                    latex_escape(finding.get("task_id")),
                    "no" if finding.get("exact_duplicate_found") is False else "yes",
                    "no" if finding.get("semantic_duplicate_found") is False else "yes",
                    latex_escape(finding.get("tier_assessment")),
                )
            )
    lines.extend(
        [
            r"\subsection{Search for already existing complete results}",
            "An exact duplicate has the same fixed Lean claim. A semantic duplicate may use different names but still says the same mathematical thing with the same assumptions. The separately authenticated exact-target-search artifacts cover "
            + latex_escape(len(search_task_ids))
            + " of "
            + latex_escape(measured_task_count)
            + " measured T1--T3 tasks ("
            + ", ".join(latex_escape(task_id) for task_id in sorted(search_task_ids))
            + "). For those tasks, the frozen NumStability and mathlib source trees were searched and plausible nearby results were compared by meaning. The fresh-context review records later in this report provide the separate corpus-wide review. Text search alone was not treated as proof that a duplicate was absent.",
        ]
    )
    lines.extend(
        _longtable(
            "Authenticated duplicate-search evidence for "
            + str(len(search_task_ids))
            + " task(s)",
            "P{0.11\\linewidth}P{0.12\\linewidth}P{0.14\\linewidth}P{0.55\\linewidth}",
            ("Task", "Exact duplicate", "Same-meaning duplicate", "Tier conclusion"),
            search_rows,
            size="footnotesize",
        )
    )

    lines.extend(
        [
            r"\section{The exact shared Lean setting}",
            "Both conditions receive the same small, library-neutral setting. Library-neutral means that its names and statements do not mention NumStability. This prevents the theorem wording itself from favoring condition L.",
            "The shared file contains exactly the neutral models, algorithms, and notation needed by the tasks in the current manifest. When another paper needs an additional neutral definition, this file and every affected fingerprint are regenerated for the whole corpus.",
            "The next listing records the complete controlled shared file. ASCII is the small basic computer character set. For dependable PDF building only, symbols outside ASCII are written as words such as Real, Nat, and alpha. The file fingerprint above is the exact byte record; a byte is one stored unit of file data.",
            r"\begin{lstlisting}",
            _ascii_lean(inputs.shared_source),
            r"\end{lstlisting}",
        ]
    )

    paired_hardware_policy = inputs.environment.get("hardware_matching_policy")
    hardware_pair_clause = (
        "same exact authenticated Slurm allocation within each N/L pair; hardware "
        "may differ between pairs"
        if paired_hardware_policy is not None
        else "same frozen machine class"
    )
    if prompt_protocol is not None:
        prompt_condition_text = (
            "Both sides receive the same common prompt, context, target, shared file, "
            "Lean version, mathlib version, time limit, and token limit, with the "
            + hardware_pair_clause
            + ". "
            "Condition L alone additionally receives the exact frozen neutral supplement "
            "condition_prompts/L.md, which names the frozen NumStability snapshot and "
            "generic ways to search, import, and inspect it without recommending any "
            "theorem or module. Condition N receives no supplement path, bytes, hash, "
            "argument, or mount. This signposted-library-v1 treatment deliberately differs "
            "from the earlier identical-prompt raw-access protocol and those results must "
            "not be mixed."
        )
        n_diagram = (
            r"\fbox{\parbox{0.39\linewidth}{\centering \textbf{N}\newline "
            r"Common prompt only\newline Lean + mathlib; NumStability import must fail}}"
        )
        l_diagram = (
            r"\fbox{\parbox{0.39\linewidth}{\centering \textbf{L}\newline "
            r"Common prompt + frozen neutral supplement\newline Frozen NumStability; library use is checked}}"
        )
    else:
        prompt_condition_text = (
            "The same target, context, shared file, agent prompt, Lean version, mathlib "
            "version, time limit, and token limit are used on both sides, with the "
            + hardware_pair_clause
            + ". "
            "Mathlib is Lean's main collection of already proved mathematics."
        )
        n_diagram = (
            r"\fbox{\parbox{0.39\linewidth}{\centering \textbf{N}\newline Lean + "
            r"mathlib only\newline NumStability import must fail}}"
        )
        l_diagram = (
            r"\fbox{\parbox{0.39\linewidth}{\centering \textbf{L}\newline Same files "
            r"+ frozen NumStability\newline Library use is checked}}"
        )

    lines.extend(
        [
            r"\section{The two conditions and their isolation}",
            "Condition N means no NumStability file, compiled file, documentation, name list, search entry, or cache is visible. Condition L means the frozen NumStability source and compiled files are visible as read-only files. Read-only means a run can inspect them but cannot change them.",
            "Isolation means separating one run from files and messages that it is not allowed to see. "
            + prompt_condition_text,
            "Both sides receive the same pruned package view. Pruned means it contains only the mathlib source needed for local reading and the package compiled files needed by Lean. A base .olean file holds a compiled Lean module. Its .olean.server, .olean.private, and .ir support files hold extra compiler data that Lean 4.29 needs when it loads some modules. The full package build folders and caches are not exposed to an attempt.",
            r"\begin{center}",
            r"\fbox{\parbox{0.78\linewidth}{\centering Fixed paper context + fixed Lean target + fixed shared setting}}",
            r"\\[3pt]$\Downarrow$\\[3pt]",
            r"\fbox{\parbox{0.78\linewidth}{\centering New conversation + new restricted file and process view}}",
            r"\\[3pt]$\Downarrow$\\[-2pt]",
            r"\begin{tabular}{P{0.43\linewidth}cP{0.43\linewidth}}",
            n_diagram + r" & $\Longleftrightarrow$ & " + l_diagram + r" \\",
            r"\end{tabular}",
            r"\\[3pt]$\Downarrow$\\[3pt]",
            r"\fbox{\parbox{0.78\linewidth}{\centering Shared validator checks the unchanged statement, proof rules, compilation, and dependencies}}",
            r"\end{center}",
            r"\subsection{Filesystem and network boundary}",
            "Bubblewrap is a Linux tool that gives a process a restricted view of files and processes. A fresh bubblewrap view is made for each attempt. Seccomp is a rule enforced by the Linux kernel, the central part of the operating system, that blocks selected requests from a program. Here it blocks socket calls, which are requests to open network connections, from model-generated shell commands.",
            "The Codex control process is separate from the model-generated shell. It keeps the provider connection needed to send the prompt to the model service and receive the answer. This limit is important: the model's shell and web tools are offline, but the outer control process is not fully offline.",
            "For each run, the outer runner creates a fresh secret marker file and asks the Linux kernel to watch it. A blocked network request writes an event before returning an error. The kernel watch remains owned by the outer runner, so a model shell cannot erase an event by clearing or deleting the file. The result-set checker required a complete marker record for every final run.",
            "The private gold proofs and source PDFs are not mounted in either measured condition. A mount is a file tree made visible inside the restricted run.",
        ]
    )
    freeze_release = inputs.freeze_check["release_manifest"]
    freeze_compiled = inputs.freeze_check["compiled_environment_summary"]
    freeze_packages = inputs.freeze_check["packages_runtime"]
    freeze_lean = inputs.freeze_check["lean"]
    freeze_host = inputs.freeze_check["host_class"]
    hardware_rows = [
        (
            "Processor",
            freeze_host.get("processor"),
            "Vendor "
            + str(freeze_host.get("cpu_vendor"))
            + "; family/model/stepping "
            + "/".join(
                str(freeze_host.get(field))
                for field in ("cpu_family", "cpu_model", "cpu_stepping")
            ),
        ),
        (
            "Allocated CPU topology",
            str(freeze_host.get("online_logical_cpus"))
            + " logical threads on "
            + str(freeze_host.get("allocated_physical_cores"))
            + " physical cores",
            str(freeze_host.get("allocated_sockets"))
            + " socket(s); allocated threads per core "
            + str(freeze_host.get("allocated_threads_per_core")),
        ),
        (
            "Allocation memory limit",
            _fmt_bytes(freeze_host.get("allocation_memory_limit_bytes")),
            "The cgroup memory ceiling that must match before a resumed chunk starts.",
        ),
        (
            "Slurm allocation",
            str(freeze_host.get("slurm_num_nodes"))
            + " node(s), "
            + str(freeze_host.get("slurm_num_tasks"))
            + " task(s), "
            + str(freeze_host.get("slurm_num_cpus"))
            + " CPU(s)",
            str(freeze_host.get("slurm_cpus_per_task"))
            + " CPUs per task; "
            + _fmt_bytes(freeze_host.get("slurm_allocated_memory_bytes"))
            + " allocated memory.",
        ),
        (
            "Visible host memory",
            _fmt_bytes(freeze_host.get("visible_memory_bytes")),
            "Recorded separately from the smaller allocation memory ceiling.",
        ),
        (
            "Kernel and virtualization",
            freeze_host.get("kernel"),
            str(freeze_host.get("virtualization"))
            + (
                "; invariant allocation fields match the reference, while every pair "
                "retains its full authenticated host class."
                if inputs.environment.get("hardware_matching_policy") is not None
                else "; every accepted run cites a startup check matching all frozen host fields."
            ),
        ),
    ]
    lines.extend(
        [
            r"\subsection{Paired hardware and allocation provenance}"
            if paired_hardware_policy is not None
            else r"\subsection{Frozen hardware and allocation class}",
            (
                "Each N/L pair is required to use one exact authenticated Slurm "
                "allocation descriptor and job. Hardware may differ between pairs; "
                "the table shows the adjacent authenticated allocation, while every "
                "pair retains its own host-class evidence. Pooled absolute elapsed-time "
                "summaries are descriptive; within-pair L-minus-N changes are the "
                "principal time estimand."
                if paired_hardware_policy is not None
                else "A resumed measurement chunk is admitted only after its processor "
                "identity, allocated topology, memory ceiling, visible memory, kernel, "
                "and virtualization match this frozen class. Hostname and logical CPU "
                "numbers may differ; the measured hardware class may not."
            ),
        ]
    )
    lines.extend(
        _longtable(
            (
                "Reference hardware and invariant allocation fields"
                if paired_hardware_policy is not None
                else "Hardware and allocation fields enforced across chunks"
            ),
            "P{0.23\\linewidth}P{0.31\\linewidth}P{0.38\\linewidth}",
            ("Field", "Frozen value", "Continuity meaning"),
            (
                (latex_escape(field), latex_escape(value), latex_escape(meaning))
                for field, value, meaning in hardware_rows
            ),
            size="footnotesize",
        )
    )
    frozen_setup_rows = [
        (
            "Release files",
            freeze_release.get("file_count"),
            "Every listed benchmark and checker file passed its recorded fingerprint.",
        ),
        (
            "Construction checker files",
            len(CONSTRUCTION_TOOL_PATHS),
            "Their fingerprints matched both the construction record and the release list.",
        ),
        (
            "Lean toolchain files",
            freeze_compiled.get("toolchain_file_count"),
            "The whole Lean toolchain, meaning the compiler and its standard files, matched the frozen tree summary.",
        ),
        (
            "Package files",
            freeze_compiled.get("package_file_count"),
            str(freeze_compiled.get("package_count"))
            + " compiled package trees, including mathlib, matched their frozen summaries.",
        ),
        (
            "Files exposed in the pruned package view",
            freeze_packages.get("file_count"),
            str(freeze_packages.get("source_file_count"))
            + " mathlib source files and "
            + str(freeze_packages.get("olean_file_count"))
            + " base compiled package files and "
            + str(freeze_packages.get("compiled_support_file_count"))
            + " matching compiled support files were exposed; the rest of the package checkout was absent.",
        ),
        (
            "Online logical processors",
            inputs.freeze_check.get("host_class", {}).get("online_logical_cpus"),
            "The measured machine matched every recorded host field before the matrix started.",
        ),
        (
            "Model-token ceiling per run",
            limits.get("total_model_tokens"),
            (
                "The enforcing Ultra control summed each unique completed provider response once over the rooted coordinator/subagent tree. A pass ended after the exact outer exec raw response started an authenticated inner submit_proof call, which remained blocked; a failure required a natural exact drain. The first cap crossing was latched. Input already included cached tokens, and the rollout budget was advisory only."
                if ultra_submission_accounting
                else (
                    "The enforcing control summed each unique completed provider response over the rooted response tree and required a natural exact drain for this earlier completed-response protocol. Input already included cached tokens, and the rollout budget was advisory only."
                    if ultra_token_accounting
                    else "The enforcing control used live cumulative app-server thread usage. The trusted adapter froze the first threshold-crossing update and stopped the app-server; the outer runner polled that external log before submission validation. Input already included cached tokens. The rollout budget was advisory only."
                )
            ),
        ),
        (
            "NumStability source files",
            freeze_lean.get("source_files_verified"),
            "The exact source manifest passed before the run matrix started.",
        ),
        (
            "Pruned NumStability compiled files",
            freeze_lean.get("compiled_files_verified"),
            "Only paths below the NumStability namespace were in the L-side compiled mount.",
        ),
        (
            "Runs with a blocked network attempt",
            check.get("network_violation_run_count"),
            "Each such run is kept as a failure and cannot pass. A higher-priority limit failure may supply its short failure code. Zero means no attempt was seen.",
        ),
        (
            "Runs with damaged marker evidence",
            check.get("network_integrity_failure_count"),
            "This must be zero before the result set is accepted.",
        ),
    ]
    lines.extend(
        _longtable(
            "Authenticated release, compiled setup, and network evidence",
            "P{0.32\\linewidth}rP{0.52\\linewidth}",
            ("Item", "Count", "What the count proves"),
            (
                (latex_escape(item), latex_escape(count), latex_escape(meaning))
                for item, count, meaning in frozen_setup_rows
            ),
            size="footnotesize",
        )
    )
    canary_limit = token_canary_controls["outer_canary_token_limit"]
    advisory_limit = token_canary_controls[
        "nested_advisory_rollout_budget_limit"
    ]
    observed_tokens = token_canary_outcome["total_model_tokens"]
    crossing_tokens = (
        token_canary_outcome["first_crossing_tokens"]
        if ultra_token_accounting
        else observed_tokens
    )
    canary_overshoot = token_canary_outcome["overshoot_tokens"]
    canary_assignment = token_canary["assignment"]
    canary_rows = (
        (
            "Status",
            token_canary_summary["status"],
            "Both frozen descriptors, the release file hash, the evidence status, and the startup summary agree.",
        ),
        (
            "Outer canary ceiling",
            canary_limit,
            "The enforcing outer control used this deliberately low diagnostic ceiling.",
        ),
        (
            "Advisory rollout budget",
            advisory_limit,
            "It remained at the full benchmark limit, so it could not have caused the low-cap stop.",
        ),
        (
            "Cached-inclusive input",
            token_canary_outcome["input_tokens_including_cached"],
            "Cached input was already part of this input count and was not added again.",
        ),
        (
            "Cached input component",
            token_canary_outcome["cached_input_tokens"],
            "Recorded separately for audit only.",
        ),
        (
            "Output",
            token_canary_outcome["output_tokens"],
            "Generated tokens across the exact below-cap turn and sanitized compaction crossing."
            if ultra_token_accounting
            else "Generated tokens in the frozen threshold-crossing update.",
        ),
        (
            "Observed total",
            crossing_tokens,
            "The trusted first response-ID-deduplicated tree aggregate at or above the cap caused TOKEN_LIMIT."
            if ultra_token_accounting
            else "The trusted first threshold-crossing cumulative update caused TOKEN_LIMIT.",
        ),
        (
            "First-crossing overshoot" if ultra_token_accounting else "One-response overshoot",
            canary_overshoot,
            "Observed total minus the outer canary ceiling.",
        ),
        *(
            (
                (
                    "Provider-gate terminal total",
                    observed_tokens,
                    "The exact CLOSED-gate total at the sole compaction crossing; this is not a terminal app-server-tree total.",
                ),
                (
                    "Provider-gate overshoot",
                    token_canary_outcome["final_overshoot_tokens"],
                    "The CLOSED-gate total minus the cap after one below-cap response and one crossing response.",
                ),
                (
                    "Rooted threads",
                    token_canary_outcome["thread_count"],
                    "Exactly one root remained active on a distinct compaction turn; no descendant was created.",
                ),
                (
                    "Unique completed responses",
                    token_canary_outcome["response_count"],
                    "The byte-identical below-cap turn and sanitized compaction crossing were cross-bound and deduplicated.",
                ),
                (
                    "Closed provider gate; active tree",
                    token_canary_summary.get("provider_gate_quiescent")
                    and not token_canary_outcome["drain_complete"],
                    "Provider requests were quiescent and exact while tree drain and cumulative accounting intentionally remained incomplete.",
                ),
            )
            if ultra_token_accounting
            else ()
        ),
        (
            "Live notifications",
            token_canary_outcome["notification_count_in_audit_log"],
            "The audit log and trusted notification sequence agreed.",
        ),
        (
            "Actual stop time",
            _fmt_number(token_canary_outcome["actual_stop_seconds"], 3) + " seconds",
            "The canary stopped within its frozen diagnostic wall time.",
        ),
        (
            "Startup-verified artifacts",
            len(token_canary_summary["artifacts"]),
            "Every source-separation, prompt-provenance, invocation, freeze, runner, log, usage, controlled-input, and sealed provider-gate artifact was fingerprinted.",
        ),
        (
            "Authenticated prompt release",
            token_canary_prompt_release["status"],
            "Three sealed READY/GO/RELEASED records bind the exact synthetic turn/start wire and timing origin.",
        ),
        (
            "Measured-time origin",
            token_canary_prompt_release["measurement_time_origin"],
            "The diagnostic deadline was derived from the authenticated pre-write RELEASED monotonic timestamp.",
        ),
    )
    lines.extend(
        [
            r"\subsection{Authenticated live token-control canary}",
            "Before the scored matrix, one real provider canary used "
            + _inline_code(token_canary["canary_id"])
            + " on "
            + _inline_code(canary_assignment["task_id"])
            + " in condition "
            + _inline_code(canary_assignment["condition"])
            + ". It used protocol "
            + _inline_code(token_canary["prompt"]["protocol"])
            + ", was not a scored matrix assignment, and supplied no benchmark task bytes.",
            "The authenticated canary stopped with TOKEN_LIMIT at "
            + f"{crossing_tokens:,}"
            + " total model tokens against a "
            + f"{canary_limit:,}"
            + "-token outer cap, a "
            + f"{canary_overshoot:,}"
            + (
                "-token first-crossing overshoot. A below-cap turn was released byte-for-byte; the sole crossing was a distinct compaction request whose fully buffered response was replaced by exactly one opaque compaction item and a minimal completion. It released no provider answer, messages, tool frames, or interrupts. The provider gate was CLOSED and quiescent at "
                + f"{observed_tokens:,}"
                + " tokens while the rooted app-server tree and cumulative accounting intentionally remained incomplete. Its nested advisory rollout budget remained "
                if ultra_token_accounting
                else "-token one-response overshoot. Its nested advisory rollout budget remained "
            )
            + f"{advisory_limit:,}"
            + " tokens. This directly demonstrates that live app-server usage and the outer controller, rather than the advisory rollout budget, caused the low-cap stop.",
            "The frozen-run check reauthenticated the canary evidence, the mode-0444 self-hashed provider-gate record, and every referenced artifact before the measured matrix began. The evidence is a private synthetic control check outside the scored benchmark matrix; nothing is designated for public release.",
        ]
    )
    lines.extend(
        _longtable(
            "Observed token-control canary result",
            "P{0.28\\linewidth}P{0.18\\linewidth}P{0.46\\linewidth}",
            ("Canary field", "Observed value", "Meaning"),
            (
                (latex_escape(field), latex_escape(value), latex_escape(meaning))
                for field, value, meaning in canary_rows
            ),
            size="footnotesize",
        )
    )
    if ultra_submission_accounting:
        if not isinstance(ultra_canary_summary, Mapping):
            raise ReportError("validated Ultra canary summary is missing at render time")
        barrier = ultra_canary_summary.get("barrier")
        canary_projection = ultra_canary_summary.get("accounting_projection")
        canary_prompt_release = ultra_canary_summary.get("prompt_release")
        if not isinstance(barrier, Mapping):
            raise ReportError("validated Ultra canary barrier is missing at render time")
        if not isinstance(canary_projection, Mapping):
            raise ReportError("validated Ultra canary projection is missing at render time")
        if not isinstance(canary_prompt_release, Mapping):
            raise ReportError("validated Ultra canary prompt release is missing at render time")
        ultra_canary_rows = (
            ("Status", ultra_canary_summary.get("status"), "The synthetic probe and all retained artifacts were reauthenticated."),
            ("Rooted threads", ultra_canary_summary.get("thread_count"), "The root plus its delegated descendants were included."),
            ("Positive-usage descendants", ultra_canary_summary.get("positive_usage_descendant_thread_count"), "At least one completed child contributed provider usage."),
            ("Unique completed responses", ultra_canary_summary.get("response_count"), "Response IDs were replayed and deduplicated."),
            ("Model tokens at boundary", ultra_canary_summary.get("total_model_tokens"), "Cached-inclusive input plus output through the outer exec response containing the nested submission."),
            ("Exact submission boundary", ultra_canary_summary.get("submission_boundary_exact"), "The frozen outer custom exec and root-only inner submit_proof call were authenticated."),
            ("Nested wire", barrier.get("submission_transport"), "Replay proved the exact 104-byte rejection-forwarding outer custom exec and one of the two schema-v5 timestamp-authenticated inner-call/raw-response observation orders before publication."),
            ("Submission event order", barrier.get("submission_event_order"), "The enum agrees with exactly one of the two order flags and the retained monotonic timestamps."),
            ("Frozen exec bytes", barrier.get("outer_exec_program_bytes"), "The sole final model tool item used the frozen 104-byte source."),
            ("Frozen exec SHA-256", barrier.get("outer_exec_program_sha256"), "The exact code-mode wrapper source was fingerprinted."),
            ("Exec yield time (ms)", barrier.get("outer_exec_yield_time_ms"), "The exact pragma prevents code-mode progress output throughout the authenticated envelope."),
            ("Yield envelope (ms)", barrier.get("outer_exec_yield_envelope_ms"), "This is 1,800 seconds of measured time plus the 369-second validation/teardown reserve."),
            ("Yield margin (ms)", barrier.get("outer_exec_yield_margin_ms"), "The 231-second positive margin is independently rederived."),
            ("Timer after prompt release", barrier.get("outer_exec_timer_starts_at_or_after_prompt_release"), "The retained monotonic timestamps prove the exec timer cannot begin before RELEASED."),
            ("Provider gate vs. tree drain", ultra_canary_summary.get("drain_complete"), "False is required here: the provider gate is CLOSED and quiescent after publication, while the blocked inner call keeps the app-server tree active until immediate teardown."),
            ("Provider-gate protocol", canary_projection.get("provider_gate_protocol"), "The sealed gate independently binds the catalog response bound, production TLS transport, provider ledger, reconciled app-server deliveries, and accepted close."),
            ("Accounting projection schema", canary_projection.get("accounting_projection_schema_version"), "Projection v4 binds the sealed provider-gate endpoint, reconciles app-server deliveries, and records every hook decision, allowed child, and cumulative total."),
            ("Policy-blocked fork calls", len(canary_projection.get("policy_blocked_spawn_call_ids", [])), "The root and allowed child each proved that fork_turns=3 was denied without creating a child."),
            *_hook_trust_report_rows(canary_projection),
            ("Raw call/activity identity", canary_projection.get("raw_call_activity_id_match"), "The raw spawn function-call ID exactly matched the subagent-activity ID."),
            ("Completed root response before spawn", canary_projection.get("completed_root_response_before_spawn"), "The fork-all child inherited a provider cumulative baseline that was independently known to be nonzero."),
            ("Children with nonzero inherited baseline", len(canary_projection.get("nonzero_inherited_baseline_child_thread_ids", [])), "At least one child projection included completed parent history rather than starting from zero."),
            ("Complete graph and cumulative accounting", canary_projection.get("accounting_complete"), "Spawn linkage, descendant resolution, and every cumulative projection all rederived successfully."),
            ("Retained boundary chain", barrier.get("retained_read_only"), "Challenge, call, request, acknowledgement, and candidate snapshot were sealed read-only."),
            ("Authenticated prompt release", canary_prompt_release.get("authenticated"), "READY/GO/RELEASED evidence binds the exact synthetic turn/start write."),
            ("Success timing endpoint", canary_prompt_release.get("request_publication_timing_verified"), "The retained request publication, not the earlier candidate capture, is the first-valid endpoint."),
            ("Authenticated artifacts", len(ultra_canary_summary.get("artifacts", {})), "The full synthetic input, logs, runner record, validation, and barrier chain were fingerprinted."),
        )
        lines.extend(
            [
                r"\subsection{Authenticated Ultra delegation and submission canary}",
                "A separate synthetic, unscored canary first proved authenticated fork-turns=3 denial without child activity at both the root and descendant levels, then completed one fork-all child delegation and submitted a trivial candidate through the production boundary. It used no benchmark task. Replay matched the allowed raw spawn call to the subagent activity, rederived the child's nonzero inherited baseline, proved complete cumulative accounting, descendant quiescence, an active blocked root, an immutable accepted candidate, and no possible later model response.",
            ]
        )
        lines.extend(
            _longtable(
                "Observed Ultra submission-boundary canary",
                r"P{0.28\linewidth}P{0.18\linewidth}P{0.46\linewidth}",
                ("Canary field", "Observed value", "Meaning"),
                (
                    (latex_escape(field), latex_escape(value), latex_escape(meaning))
                    for field, value, meaning in ultra_canary_rows
                ),
                size="footnotesize",
            )
        )
        if not isinstance(ultra_accounting_summary, Mapping):
            raise ReportError("validated Ultra matrix accounting summary is missing at render time")
        matrix_projection_rows = (
            ("Selected Ultra outcomes", ultra_accounting_summary.get("selected_ultra_run_count"), "Every selected pass or failure supplied projection-v6 gate, hook, graph, and token evidence."),
            ("Complete projections", ultra_accounting_summary.get("complete_projection_count"), "The result checker and this renderer independently rederived every thread graph and cumulative total."),
            ("Accepted-boundary projections", ultra_accounting_summary.get("accepted_boundary_projection_count"), "Only the root outer-exec response containing the blocked inner submit may use the narrow cumulative exception."),
            ("Natural-drain projections", ultra_accounting_summary.get("natural_drain_projection_count"), "Every thread in each naturally stopped failure required its full cumulative projection."),
            ("Token-gate crossing projections", ultra_accounting_summary.get("token_gate_crossing_projection_count"), "These exact provider-token endpoints may retain an active tree and incomplete cumulative projection after the sole sanitized crossing."),
        )
        lines.extend(
            _longtable(
                "Independently rederived matrix accounting",
                r"P{0.30\linewidth}P{0.16\linewidth}P{0.46\linewidth}",
                ("Projection field", "Count", "Meaning"),
                (
                    (latex_escape(field), latex_escape(value), latex_escape(meaning))
                    for field, value, meaning in matrix_projection_rows
                ),
                size="footnotesize",
            )
        )
    lines.extend(
        [
            r"\subsection{Construction evidence}",
            "Compile means ask Lean to read and check a whole source file. Import means ask Lean to load another named source unit. A dependency check follows the named facts used by a proof to make sure no hidden shortcut was used.",
            "Each N construction check first copied the complete controlled task, then scanned that staged task and tried a real NumStability import. Only after this absence check passed was the private answer copied in. This order makes the scan cover the files an evaluated run actually receives.",
        ]
    )
    construction_results = list(inputs.construction_check["results"])
    proof_results = [
        result for result in construction_results if result.get("tier") != "T4"
    ]
    t4_skeleton_results = [
        result for result in construction_results if result.get("tier") == "T4"
    ]
    n_results = [result for result in construction_results if result.get("condition") == "N"]
    n_staged_file_count = sum(
        result["n_preflight"]["controlled_files_verified_after_staging"]["verified"]
        for result in n_results
    )
    l_results = [
        result for result in proof_results if result.get("condition") == "L"
    ]
    l_compile_count = sum(
        1
        for result in l_results
        if isinstance(result.get("validation"), Mapping)
        and result["validation"].get("compile_exit_code") == 0
        and result["validation"].get("compile_timed_out") is False
    )
    l_audit_count = sum(
        1
        for result in l_results
        if isinstance(result.get("validation"), Mapping)
        and isinstance(result["validation"].get("dependency_audit"), Mapping)
        and result["validation"]["dependency_audit"].get("complete") is True
        and result["validation"]["dependency_audit"].get("exit_code") == 0
    )
    l_use_count = sum(
        1
        for result in l_results
        if isinstance(result.get("validation"), Mapping)
        and isinstance(result["validation"].get("dependency_audit"), Mapping)
        and result["validation"]["dependency_audit"].get("library_use") is True
    )
    l_declaration_count = sum(
        len(result["validation"]["dependency_audit"].get("library_declarations", []))
        for result in l_results
    )
    t4_compile_count = sum(
        1
        for result in t4_skeleton_results
        if isinstance(result.get("validation"), Mapping)
        and result["validation"].get("compile_exit_code") == 0
        and result["validation"].get("controlled_sorries_checked")
        == result["validation"].get("controlled_sorry_count")
    )
    evidence_rows = [
        (
            "N staged-task scans",
            "pass" if len(n_results) == task_count else "fail",
            f"{len(n_results)} of {task_count} complete staged tasks had no forbidden library file; {n_staged_file_count} controlled file copies were verified",
        ),
        (
            "N real import tests",
            "pass" if len(n_results) == task_count else "fail",
            f"{len(n_results)} of {task_count} checks had Lean report that NumStability was absent",
        ),
        (
            "L hidden proof compiles",
            "pass" if l_compile_count == measured_task_count else "fail",
            f"{l_compile_count} of {measured_task_count} private library-side proofs compiled",
        ),
        (
            "L dependency checks",
            "pass" if l_audit_count == measured_task_count else "fail",
            f"{l_audit_count} of {measured_task_count} proof dependency records were complete",
        ),
        (
            "L NumStability use",
            "pass" if l_use_count == measured_task_count else "fail",
            f"{l_use_count} of {measured_task_count} proofs used NumStability; {l_declaration_count} declaration records were found",
        ),
        (
            "T4 designated-hole skeletons",
            "pass" if t4_compile_count == len(t4_skeleton_results) else "fail",
            f"{t4_compile_count} of {len(t4_skeleton_results)} N/L skeleton builds compiled with exactly their controlled holes; {T4_SKELETON_PRIVATE_PROOF_NOTE}",
        ),
    ]
    lines.extend(
        _longtable(
            "Construction evidence used by this report",
            "P{0.24\\linewidth}P{0.10\\linewidth}P{0.58\\linewidth}",
            ("Check", "Result", "Plain meaning"),
            ((latex_escape(a), latex_escape(b), latex_escape(c)) for a, b, c in evidence_rows),
        )
    )
    condition_order = {"N": 0, "L": 1}
    construction_rows: list[Sequence[str]] = []
    for result in sorted(
        construction_results,
        key=lambda item: (
            str(item.get("task_id")),
            condition_order.get(str(item.get("condition")), 9),
        ),
    ):
        validation = result["validation"]
        audit = (
            validation.get("dependency_audit", {})
            if result.get("tier") != "T4"
            else {}
        )
        compile_ok = (
            validation.get("compile_exit_code") == 0
            and validation.get("compile_timed_out") is False
        )
        construction_rows.append(
            (
                latex_escape(result.get("task_id")),
                latex_escape(result.get("condition")),
                latex_escape(_fmt_number(compile_ok)),
                latex_escape(_fmt_number(result.get("pass"))),
                latex_escape(
                    "designated holes"
                    if result.get("tier") == "T4"
                    else _fmt_number(validation.get("statement_unchanged"))
                ),
                latex_escape(
                    "not applicable"
                    if result.get("tier") == "T4"
                    else _fmt_number(audit.get("complete"))
                ),
                latex_escape(
                    "not applicable"
                    if result.get("tier") == "T4"
                    else _fmt_number(audit.get("library_use"))
                ),
            )
        )
    lines.append(
        T4_PRIVATE_CONSTRUCTION_PROSE
        + latex_escape(len(construction_results))
        + " schema-aware N/L construction results were rebuilt in fresh workspaces. The report authenticated the complete record before using these rows."
    )
    lines.extend(
        _longtable(
            "All " + str(len(construction_results)) + " schema-aware construction results",
            "P{0.16\\linewidth}P{0.08\\linewidth}P{0.10\\linewidth}P{0.08\\linewidth}P{0.16\\linewidth}P{0.13\\linewidth}P{0.13\\linewidth}",
            (
                "Task",
                "Cond.",
                "Compile",
                "Pass",
                "Statement fixed",
                "Audit done",
                "Library use",
            ),
            construction_rows,
            size="footnotesize",
        )
    )

    lines.extend(
        [
            r"\section{How submissions were checked}",
            "A validator is a program that decides whether a submitted proof obeys the fixed rules and compiles. It performs these checks in order:",
            r"\begin{enumerate}",
            r"\item Recheck every controlled file fingerprint before and after validation.",
            r"\item Reject a changed theorem statement, a symbolic link that redirects to another file, and a compiled helper with no matching source file.",
            r"\item Scan every submitted Lean source file for \texttt{sorry}, \texttt{admit}, a new global \texttt{axiom}, \texttt{unsafe}, forbidden imports, or other rule violations. These forms can bypass the requested complete proof.",
            r"\item Compile a hidden copy of the submitted theorem. Hidden means the final checker file is not available for the agent to edit.",
            r"\item Recursively follow the named facts and definitions used by the theorem. Recursively means following each dependency and then its dependencies. Reject any reachable \texttt{sorryAx}, which is Lean's marker for a missing proof, and reject any axiom owned by \texttt{Submission} or another task-local helper module, meaning a Lean source unit supplied with the answer.",
            r"\item This audit does not ban every axiom from Lean, mathlib, or NumStability. Those outside the submitted task modules belong to the fixed libraries and compiler. The audit records them while separately rejecting missing proofs and task-local assumed facts.",
            r"\item In condition L, use the same recursive dependency record to confirm real NumStability use. Merely importing the library is not counted as use.",
            r"\end{enumerate}",
            "A system error means the measurement machinery failed rather than the proof. One such incident may be kept and rerun once. Every other failure receives the full fixed comparison time even though its real stop time is also recorded.",
            r"\subsection{Independent review records}",
            "Independent here means that the fresh Codex reviews used separate contexts and review bases. A formal interface is the exact set of Lean names, inputs, and output claims. They are not human reviews, and a retained rejection is not rewritten as a pass.",
        ]
    )
    review_rows: list[Sequence[str]] = []
    review_task_rows: list[Sequence[str]] = []
    for review_index, review in enumerate(inputs.reviews):
        review_id = _review_identifier(review, review_index)
        reviewer = review.get("reviewer", {})
        task_reviews = _review_task_records(review)
        decisions = [str(_task_review_decision(item) or "") for item in task_reviews]
        source_values = [item.get("source_faithful") for item in task_reviews]
        source_count: Any = (
            sum(value is True for value in source_values)
            if any(value is not None for value in source_values)
            else "--"
        )
        pass_count = sum(value.lower().startswith("pass") for value in decisions)
        rejection_count = len(decisions) - pass_count
        focus = (
            reviewer.get("focus")
            or reviewer.get("identity")
            or review.get("kind")
        ) if isinstance(reviewer, Mapping) else review.get("kind")
        review_rows.append(
            (
                latex_escape(review_id),
                latex_escape(focus),
                latex_escape(_review_decision(review)),
                latex_escape(len(task_reviews)),
                latex_escape(source_count),
                latex_escape(pass_count),
                latex_escape(rejection_count),
            )
        )
        for task_review in task_reviews:
            review_task_rows.append(
                (
                    latex_escape(review_id),
                    latex_escape(task_review.get("task_id")),
                    latex_escape(_task_review_decision(task_review)),
                )
            )
    review_override = inputs.config.get("private_measurement_review_override")
    if isinstance(review_override, Mapping) and review_override.get("enabled") is True:
        ignored_ids = sorted(str(value) for value in review_override["ignored_rejection_task_ids"])
        lines.extend(
            [
                r"\textbf{Private measurement exception.} The project owner directed that the unchanged matrix be measured while retaining, but temporarily not blocking on, exact-target novelty rejections. Source fidelity remains mandatory. The exception covers only: "
                + ", ".join(_inline_code(task_id) for task_id in ignored_ids)
                + ".",
                "These task decisions remain visible below. This exception authorizes private measurement only; it does not approve a public release or make the novelty checks pass.",
            ]
        )
    lines.extend(
        _longtable(
            "Fresh review records",
            "P{0.20\\linewidth}P{0.25\\linewidth}P{0.18\\linewidth}rrrr",
            ("Review", "Focus", "Overall", "Tasks", "Source", "Pass", "Reject"),
            review_rows,
            size="scriptsize",
        )
    )
    lines.extend(
        _longtable(
            "Review outcome for each task",
            "P{0.34\\linewidth}P{0.18\\linewidth}P{0.40\\linewidth}",
            ("Review", "Task", "Outcome"),
            review_task_rows,
            size="footnotesize",
        )
    )

    if t4_coverage:
        lines.extend(
            [
                "T4 uses claim-scoped review units stored in its schema-0.4 task record. Each accepted row binds immutable source and Lean packets plus fresh direct, blind-translation, and round-trip roles; these are separate from the two legacy task-level T1--T3 reviews above."
            ]
        )
        lines.extend(
            _longtable(
                "Accepted T4 claim-review coverage",
                "P{0.18\\linewidth}rrrrr",
                (
                    "Task",
                    "Included claims",
                    "Declarations",
                    "Review units",
                    "Accepted",
                    "Coverage",
                ),
                (
                    (
                        latex_escape(row["task_id"]),
                        latex_escape(row["included_source_count"]),
                        latex_escape(row["declaration_count"]),
                        latex_escape(row["review_unit_count"]),
                        latex_escape(row["accepted_review_count"]),
                        _fmt_rate(row["accepted_review_unit_coverage_rate"]),
                    )
                    for row in t4_coverage
                ),
                size="footnotesize",
            )
        )

    lines.extend(
        [
            r"\section{Measurement limits and result meaning}",
            "Each task-condition pair was repeated three times. A repetition is another fresh attempt at the same fixed task. The labels rep-01, rep-02, and rep-03 are not random seeds.",
            "A model token is a small piece of text counted by the model service. The fixed limit was "
            + latex_escape(limits.get("total_model_tokens"))
            + " total model tokens and "
            + latex_escape(limits.get("wall_clock_seconds"))
            + " measured seconds per attempt. Prompt startup had a separate "
            + latex_escape(limits.get("prompt_startup_timeout_seconds"))
            + "-second timeout and did not consume the measured allowance.",
            (
                "For Ultra attempts, an authenticated loopback provider gate fully buffered each counted turn or compaction response before releasing it to Codex app-server. Its frozen model catalog fixes a 272,000-token per-response bound. Requests begin under conservative concurrent reservations; when another bound would reach the cap, the gate drains existing requests and admits one exclusive request. Unknown or missing request metadata is denied before upstream. Direct app-server delivery rows are bound to their gate calls. A provider response hidden by a collaboration wait is accepted only when the retained evidence proves its exact later direct delivery. Provider totals determine the scored token count; app-server rows remain structural delivery evidence. For a pass, schema v5 authenticates the exact frozen 104-byte rejection-forwarding outer exec and blocked inner submit_proof boundary; the accepted gate close occurs after request publication, with every provider start and commit no later than publication. The provider endpoint is then CLOSED and quiescent even though the rooted app-server tree is still active, and immediate child teardown prevents a later model response. A TOKEN_LIMIT endpoint instead closes on the unique sole-inflight crossing: an ordinary turn releases a minimal empty-output completion, while a compaction crossing releases exactly one opaque compaction item followed by a minimal completion. Both are buffered and action-free, with no messages, tool frames, or interrupt. This exact provider-token endpoint may intentionally retain an active tree and incomplete drain/cumulative accounting. Other scored failures require a natural provider-and-tree drain. Thus one crossing response can overshoot, but no concurrent in-flight tail can."
                if ultra_submission_accounting
                else (
                    "The provider ledger counts every completed provider response. Direct app-server delivery rows and narrowly proved collaboration-wait suppressions reconcile those responses without changing the scored provider total. The sealed gate makes an accepted close or sole sanitized token crossing exact at the provider endpoint; provider quiescence is distinct from app-server-tree terminality."
                    if ultra_token_accounting
                    else "Codex app-server emitted an ordered sequence of live cumulative thread-usage updates. The adapter wrote them atomically to a trusted result-log path that the model could neither see nor modify. Cached input was already included in the input total and was counted once. At the first update at or above the ceiling, the trusted adapter froze that update and stopped the app-server so it could not be overwritten by a later response. Before it inspected or validated a changed proof, the outer runner polled the same path and stopped the remaining agent process group when needed. A limit failure can therefore precede any submission, while every passing record requires a newer post-submission usage update below the ceiling."
                )
            ),
            (
                "The authenticated loopback provider gate and its buffering, reservation, drain, and exclusive-admission endpoint are a disclosed execution-protocol amendment applied identically to N and L. This report therefore does not claim the strict unmodified reference-PDF protocol. The frozen Codex binary and model configuration are unchanged; the trusted adapter and gate enforce this amended endpoint."
                if ultra_token_accounting
                else ""
            ),
        ]
    )
    if prompt_protocol is not None:
        if not isinstance(prompt_release_summary, Mapping):
            raise ReportError("validated prompt-release summary is missing at render time")
        prompt_release_rows = (
            ("Selected final attempts", prompt_release_summary.get("selected_final_run_count"), "Every selected matrix record carried one authenticated release."),
            ("Authenticated releases", prompt_release_summary.get("authenticated_release_count"), "The runner, result checker, and renderer reauthenticated the prompt and turn/start binding."),
            ("Retained handshake files", prompt_release_summary.get("retained_artifact_file_count"), "Each attempt retained canonical, mode-0444 READY, GO, and RELEASED records."),
            ("Startup timeout", str(prompt_release_summary.get("startup_timeout_seconds")) + " seconds", "This independent startup allowance is not the 1,800-second scored wall limit."),
            ("Measured-time origin", prompt_release_summary.get("timing_origin"), "The deadline begins at the RELEASED pre-write monotonic timestamp."),
            ("Ultra pass endpoint", prompt_release_summary.get("ultra_success_endpoint"), "First-valid time ends when the authenticated nested boundary is published after completion of the outer exec response, never at earlier candidate capture."),
        )
        lines.extend(
            [
                r"\subsection{Authenticated prompt release and timing origin}",
                "Before useful model work, the isolated adapter sealed READY and waited for a runner-issued GO. GO was issued only with at least five seconds left in the separate startup window. The adapter then recorded RELEASED immediately before writing the exact turn/start request and recorded a post-flush timestamp. All three records, their self and file hashes, the nonce, identities, prompt bytes, exact request wire, and command paths were independently checked. The measured wall-clock deadline derives only from RELEASED. A pre-GO timeout starts no useful work; missing or invalid post-GO evidence is an unscored SYSTEM_ERROR incident rather than a retryable no-start.",
            ]
        )
        lines.extend(
            _longtable(
                "Prompt-release authentication for selected runs",
                r"P{0.28\linewidth}P{0.20\linewidth}P{0.44\linewidth}",
                ("Timing field", "Verified value", "Meaning"),
                (
                    (latex_escape(field), latex_escape(value), latex_escape(meaning))
                    for field, value, meaning in prompt_release_rows
                ),
                size="footnotesize",
            )
        )
    if ultra_submission_accounting:
        if not isinstance(ultra_boundary_summary, Mapping):
            raise ReportError("validated Ultra result boundary summary is missing")
        boundary_rows = (
            ("Passing runs", ultra_boundary_summary.get("passing_ultra_run_count"), "Each has one runner-verified authenticated first-valid-proof boundary."),
            ("Naturally drained failures", ultra_boundary_summary.get("naturally_drained_failure_count"), "Each unsuccessful run has exact usage and no accepted proof boundary."),
            ("Inexact outcomes", ultra_boundary_summary.get("invalid_or_inexact_outcome_count"), "This must be zero in the accepted matrix."),
            ("Retained boundary artifacts", ultra_boundary_summary.get("retained_artifact_file_count"), "Five sealed artifacts per pass were re-read and hash-checked."),
            ("Pass drain_complete", ultra_boundary_summary.get("pass_drain_complete"), "False is the required blocked-tool state for a pass."),
            ("Later response possible", ultra_boundary_summary.get("later_model_response_possible_after_pass_boundary"), "False: acceptance sends no tool response and terminates the app-server out of band."),
        )
        lines.extend(
            _longtable(
                "Authenticated first-valid-proof accounting",
                r"P{0.28\linewidth}P{0.18\linewidth}P{0.46\linewidth}",
                ("Boundary field", "Measured value", "Meaning"),
                (
                    (latex_escape(field), latex_escape(value), latex_escape(meaning))
                    for field, value, meaning in boundary_rows
                ),
                size="footnotesize",
            )
        )
    lines.append(
        r"\textbf{These are the actual private measurements from the complete selected matrix.} No result or artifact in this report is authorized for public release."
    )

    per_run_rows: list[Sequence[str]] = []
    for run in analysis["per_run_results"]:
        status = "final" if run.get("run_id") in selected_ids else "system incident"
        per_run_rows.append(
            (
                latex_escape(run.get("run_id")),
                latex_escape(status),
                latex_escape(run.get("task_id")),
                latex_escape(run.get("repetition_id")),
                latex_escape(run.get("condition")),
                latex_escape(_fmt_number(run.get("pass"))),
                latex_escape(_fmt_number(run.get("scored_elapsed_seconds"))),
                latex_escape(_fmt_number(run.get("model_tokens"), 0)),
                latex_escape(run.get("failure_code")),
            )
        )
    lines.extend(
        _longtable(
            "Every run record",
            "P{0.20\\linewidth}P{0.09\\linewidth}P{0.09\\linewidth}P{0.07\\linewidth}P{0.05\\linewidth}rrrrP{0.10\\linewidth}",
            ("Run", "Kind", "Task", "Rep.", "Cond.", "Pass", "Seconds", "Tokens", "Failure"),
            per_run_rows,
            size="scriptsize",
        )
    )

    condition_result_rows: list[Sequence[str]] = []
    for row in conditions:
        run_count, passes_count, pass_rate, seconds, tokens, l_use = _condition_values(row, observational)
        condition_result_rows.append(
            (
                latex_escape(row.get("agent_id")),
                latex_escape(row.get("scope")),
                latex_escape(row.get("condition")),
                latex_escape(run_count),
                latex_escape(passes_count),
                _fmt_rate(pass_rate),
                latex_escape(_fmt_number(seconds)),
                latex_escape(_fmt_number(tokens, 1)),
                latex_escape(l_use),
            )
        )
    lines.extend(
        _longtable(
            "Per-condition results",
            "P{0.13\\linewidth}P{0.10\\linewidth}P{0.06\\linewidth}rrrrrr",
            ("Agent", "Scope", "Cond.", "Runs", "Pass", "Rate", "Med. s", "Med. tok.", "L-use"),
            condition_result_rows,
            size="scriptsize",
        )
    )
    lines.append(
        "Median means the middle measured value after sorting. L-use is the number of passing L runs whose final proof truly depended on at least one NumStability declaration. A declaration is a named Lean fact or definition."
    )

    task_result_rows: list[Sequence[str]] = []
    for row in tasks:
        run_count, passes_count, pass_rate, seconds, tokens, l_use = _condition_values(row, observational)
        task_result_rows.append(
            (
                latex_escape(row.get("task_id")),
                latex_escape(row.get("tier")),
                latex_escape(row.get("condition")),
                latex_escape(run_count),
                latex_escape(passes_count),
                _fmt_rate(pass_rate),
                latex_escape(_fmt_number(seconds)),
                latex_escape(_fmt_number(tokens, 1)),
                latex_escape(l_use),
            )
        )
    lines.extend(
        _longtable(
            "Per-task results",
            "P{0.16\\linewidth}P{0.06\\linewidth}P{0.06\\linewidth}rrrrrr",
            ("Task", "Tier", "Cond.", "Runs", "Pass", "Rate", "Med. s", "Med. tok.", "L-use"),
            task_result_rows,
            size="scriptsize",
        )
    )

    lines.extend(
        [
            r"\subsection{Failures}",
            "A failure code is a short, fixed reason for an unsuccessful run. TIME means the time limit; TOKEN means the token limit; NONE means no proof file; RULE means a forbidden shortcut; SYNTAX means Lean could not understand the file; PROOF means Lean found an unfinished or incorrect proof; SYSTEM means the measurement machinery failed.",
        ]
    )
    failure_rows: list[Sequence[str]] = []
    for row in conditions:
        counts = row.get("failure_counts")
        if not isinstance(counts, Mapping):
            raise ReportError("condition result row has no failure counts")
        for code in FAILURE_CODES:
            failure_rows.append(
                (
                    latex_escape(row.get("scope")),
                    latex_escape(row.get("condition")),
                    latex_escape(code),
                    latex_escape(counts.get(code, 0)),
                )
            )
    lines.extend(
        _longtable(
            "Failure counts by scope and condition",
            "P{0.18\\linewidth}P{0.16\\linewidth}P{0.38\\linewidth}P{0.14\\linewidth}",
            ("Scope", "Condition", "Failure code", "Count"),
            failure_rows,
        )
    )

    lines.extend(
        [
            r"\subsection{Matched N/L changes}",
            "A pair contains the N and L attempt for the same task and repetition. Every change below is L minus N. A positive pass change favors L. A negative time or token change means L used less. The reported center for time and tokens is the median of the within-pair changes, not the difference between two unrelated medians. The abbreviation pp means percentage points, the direct difference between two percentages.",
            "A 95 percent range is meant to show uncertainty. Here it is made by a bootstrap, which means repeatedly drawing whole papers from the paper set and recalculating the result.",
        ]
    )
    pair_result_rows: list[Sequence[str]] = []
    for row in pairs:
        pass_change, time_change, token_change = _pair_values(row, observational)
        pair_result_rows.append(
            (
                latex_escape(row.get("scope")),
                latex_escape(row.get("pairs")),
                _fmt_delta(pass_change, scale=100.0) + " pp",
                _range(row, "pass_rate_change", scale=100.0) + " pp",
                _fmt_delta(time_change),
                _range(row, "median_paired_time_change"),
                _fmt_delta(token_change),
                _range(row, "median_paired_token_change"),
            )
        )
    lines.extend(
        _longtable(
            "Paired changes by tier",
            "P{0.10\\linewidth}rP{0.09\\linewidth}P{0.15\\linewidth}P{0.08\\linewidth}P{0.15\\linewidth}P{0.08\\linewidth}P{0.15\\linewidth}",
            ("Scope", "Pairs", "Pass", "95\\% range", "Seconds", "95\\% range", "Tokens", "95\\% range"),
            pair_result_rows,
            size="scriptsize",
        )
    )
    task_pair_result_rows: list[Sequence[str]] = []
    for row in task_pairs:
        pass_change, time_change, token_change = _pair_values(row, observational)
        task_pair_result_rows.append(
            (
                latex_escape(row.get("task_id")),
                latex_escape(row.get("tier")),
                latex_escape(row.get("pairs")),
                _fmt_delta(pass_change, scale=100.0) + " pp",
                _fmt_delta(time_change),
                _fmt_delta(token_change),
            )
        )
    lines.extend(
        _longtable(
            "Per-task paired changes",
            "P{0.22\\linewidth}P{0.08\\linewidth}rP{0.15\\linewidth}P{0.15\\linewidth}P{0.15\\linewidth}",
            ("Task", "Tier", "Pairs", "Pass change", "Second change", "Token change"),
            task_pair_result_rows,
            size="footnotesize",
        )
    )
    if measured_paper_count == 1:
        lines.extend(
            [
                r"\begin{center}",
                r"\fcolorbox{red!70!black}{yellow!12}{\parbox{0.92\linewidth}{\textbf{One-paper warning.} A bootstrap is repeated resampling used to make an uncertainty range. This report resamples whole papers, but there is only one paper. It therefore chooses the same paper again and again. The resulting 95\% range is degenerate, meaning it has no useful information about how results vary across papers. It is shown only as an arithmetic check and must not be read as broad certainty.}}",
                r"\end{center}",
            ]
        )

    lines.extend(
        [
            r"\subsection{Actual library use in condition L}",
            "A passing L proof counts as library use only when the dependency audit finds at least one NumStability declaration in the final proof path. Merely importing or searching the library does not count.",
        ]
    )
    library_rows: list[Sequence[str]] = []
    declarations_by_task: dict[str, set[str]] = {}
    for run in selected_runs:
        if run.get("condition") != "L":
            continue
        declarations = run.get("library_declarations")
        names = [str(name) for name in declarations] if isinstance(declarations, list) else []
        task_id = str(run.get("task_id"))
        declarations_by_task.setdefault(task_id, set()).update(names)
        library_rows.append(
            (
                latex_escape(run.get("run_id")),
                latex_escape(task_id),
                latex_escape(run.get("repetition_id")),
                latex_escape(_fmt_number(run.get("pass"))),
                latex_escape(_fmt_number(run.get("library_use"))),
                latex_escape(len(names)),
            )
        )
    lines.extend(
        _longtable(
            "Library-use result for every selected L run",
            "P{0.28\\linewidth}P{0.14\\linewidth}P{0.10\\linewidth}P{0.10\\linewidth}P{0.12\\linewidth}P{0.10\\linewidth}",
            ("Run", "Task", "Rep.", "Pass", "Used library", "Decl. count"),
            library_rows,
            size="footnotesize",
        )
    )
    for task_id in sorted(declarations_by_task):
        names = sorted(declarations_by_task[task_id])
        if names:
            lines.append(
                "Recorded NumStability declarations for "
                + latex_escape(task_id)
                + ": "
                + ", ".join(_inline_code(name) for name in names)
                + "."
            )
        else:
            lines.append("No NumStability declaration was recorded for " + latex_escape(task_id) + ".")

    lines.extend(
        [
            r"\section{Recorded protocol scope and limitations}",
            "This run set is complete. The following concrete properties of its execution environment remain part of the measurement record:",
            r"\begin{enumerate}",
        ]
    )
    for deviation in environment.get("known_reference_protocol_deviations", []):
        lines.append(r"\item " + latex_escape(deviation))
    lines.extend(
        [
            r"\end{enumerate}",
            "OCI is a standard format for a frozen container image, which is a saved software filesystem. This measurement has no OCI image fingerprint. It instead records a bubblewrap environment bundle fingerprint.",
            "The host folders /usr, /bin, /lib*, and /etc are mounted read-only, which means an attempt can read them but cannot change them. They are not one fully fingerprinted OCI filesystem.",
            "A backend seed is a number that asks the model service to repeat its random choices. No accepted and enforced seed input was available, so the three repetition labels must not be described as seeds.",
            (
                "The provider gate reserves the authenticated 272,000-token response bound before upstream: concurrent reservations are allowed only while the strict inequality remains below the cap, after which the gate drains and admits one exclusive request. A passing proof stops only after both the exact nested submit_proof call and its containing outer raw-response completion have been observed. Schema v5 records whichever observation arrived first with an enum, exclusive Boolean flags, and consistent monotonic timestamps before publication, then records the accepted provider close after publication. Its exact 2,400,000-ms yield pragma exceeds the measured limit plus the frozen validation/teardown reserve, with the timer beginning no earlier than authenticated prompt release. A token crossing is exact at the CLOSED provider endpoint even when the app-server tree and cumulative projection remain active; ordinary and compaction crossings use their distinct action-free sanitized releases. Naturally stopped failures still require full tree and accounting closure. Production transport provenance is authenticated through explicit TLS and the frozen trust store; resolver address variability is availability-only and never changes scoring semantics. First-valid wall time runs from authenticated RELEASED to retained boundary publication, not earlier candidate capture."
                if ultra_submission_accounting
                else (
                r"A rawResponse/completed token endpoint is exact only when its sealed gate, provider ledger, authenticated crossbindings, reconciled app-server deliveries, and teardown agree. One sole-inflight response may cross the cap, while concurrent in-flight overshoot is forbidden; provider closure does not by itself claim tree terminality. The nested \texttt{rollout\_budget} remains advisory."
                    if ultra_token_accounting
                    else "The token-timing caveat is notification granularity. The service reports live cumulative totals between model responses, so the outer runner may first observe a limit after one response has crossed it. Such a TOKEN_LIMIT record may contain one-response overshoot. For a passing proof, the runner requires a newer usage update after it notices the submission; the recorded total may therefore include tokens reported just after the proof first became valid. First-valid wall time is still taken when the validator accepts the proof."
                )
            ),
            r"\section{Implementation file map}",
            "The table below says where each part lives. A JSON file is a structured text record that programs can read. A JSONL file is one JSON record per line.",
        ]
    )
    file_rows = [
        ("shared/HighamBench/Core.lean", "Definitions genuinely shared by several papers."),
        ("shared/HighamBench/P*Definitions.lean", "The extra definitions exposed only to one paper."),
        ("tasks/P*/T*/", "Every manifest task's target, paper context, and task record."),
        ("metadata/manifest.json", "Paper, source anchors, task bindings, and hashes."),
        ("metadata/config.json", "Versions, conditions, repetitions, limits, and the live token-control contract."),
        ("metadata/environment.json", "Machine, tools, isolation, token-control implementation, and known deviations."),
        ("metadata/run_order.json", f"The fixed N/L order for all {pair_count} pairs."),
        ("metadata/release_files.json", "The fingerprints of the complete evaluation package."),
        ("metadata/library_source.json", "The exact NumStability source-file list."),
        ("metadata/library_olean.json", "The exact pruned NumStability compiled-file list."),
        ("metadata/packages_olean.json", "Fingerprints for compiled Lean and package trees."),
        ("metadata/packages_runtime.json", "The exact pruned package files exposed inside a run."),
        ("metadata/evidence/token_control_live_canary.json", "The frozen real-provider low-cap token-control canary and its observed outcome."),
        ("metadata/evidence/ultra_orchestration_live_canary.json", "The frozen synthetic delegation and authenticated submission-boundary canary."),
        ("metadata/evidence/", "Real N-absence and L-library-use construction checks."),
        ("metadata/reviews/", "The independent review records for every task."),
        (
            "tools/codex_isolated.py",
            "Starts one fresh restricted Codex app-server attempt and publishes either an exact authenticated pass boundary or an exact naturally drained failure ledger outside the model workspace."
            if ultra_submission_accounting
            else (
                "Starts one fresh restricted Codex app-server attempt and publishes an exact naturally drained completed-response ledger outside the model workspace."
                if ultra_token_accounting
                else "Starts one fresh restricted Codex app-server attempt and publishes live cumulative usage outside the model workspace."
            ),
        ),
        ("tools/offline_shell.c", "Installs the no-socket kernel rule for model shell commands."),
        ("tools/lean_isolated.py", "Runs Lean with exactly the files allowed by N or L."),
        ("tools/preflight.py", "Scans each complete staged N task and tests the forbidden import."),
        ("tools/refresh_snapshot.py", "Regenerates metadata uniformly for every manifest paper."),
        ("tools/run_token_control_canary.py", "Runs and validates the authenticated low-cap live token-control diagnostic."),
        ("tools/run_matrix.py", f"Runs the {run_count} assignments in their fixed order."),
        ("tools/runner.py", "Polls trusted live usage before submission validation and records one attempt, its time, tokens, and validation result."),
        ("tools/validator.py", "Checks statement identity, forbidden shortcuts, compilation, and dependencies."),
        ("tools/result_set.py", "Rejects a missing, repeated, mismatched, or out-of-order final matrix."),
        ("tools/analyze.py", "Makes all run, condition, task, failure, pair, and library-use summaries."),
        ("tools/render_report.py", "Makes this detailed LaTeX report and can compile its PDF."),
        ("result folder/freeze_check.json", "Records the checked release, tools, and compiled setup used by every run."),
    ]
    lines.extend(
        _longtable(
            "Implementation files",
            "P{0.36\\linewidth}P{0.56\\linewidth}",
            ("Path or result artifact", "Purpose"),
            ((latex_escape(path), latex_escape(purpose)) for path, purpose in file_rows),
            size="footnotesize",
        )
    )

    benchmark_id = inputs.config.get("benchmark_id")
    lines.extend(
        [
            r"\section{How to reproduce the artifacts}",
            "Run all commands from the repository root. Replace words in angle brackets with local paths. The authentication file is secret; do not copy it into a result folder or report.",
            r"\subsection{1. Run the tool tests}",
            r"\begin{lstlisting}",
            "python3 -m unittest discover -s paper_bencmark/highambench/tools/tests -v",
            r"\end{lstlisting}",
            r"\subsection{2. Run the fixed matrix}",
            (
                r"The verification flags below are used because prompt release and the sealed provider-token gate were both checked. The gate authenticates its production TLS transport, frozen model catalog, 272,000-token response bound, reservation--drain--exclusive state machine, and delivery of every provider response. A collaboration-wait response may be absent from the app-server event list only when a unique child result and a later direct response prove that delivery. Provider totals are used for scoring; app-server totals describe only its visible event list. Accepted runs close the gate after schema-v5 request publication while the app-server tree is still active, then perform immediate child teardown. TOKEN\_LIMIT closes on one sole-inflight sanitized response. One-response overshoot is possible; concurrent in-flight overshoot is false. Other failures require natural provider-and-tree closure. The synthetic Ultra and token canaries exercise these endpoint shapes; nested \texttt{rollout\_budget} remains advisory."
                if ultra_submission_accounting
                else (
                    r"The token-control verification flag below authenticates the sealed provider gate and reconciles every provider response with the app-server event list. Provider totals are used for scoring. One sole-inflight response may cross the cap; concurrent in-flight overshoot is false."
                    if ultra_token_accounting
                    else r"The two verification flags below are used because both controls were checked. Token enforcement comes from live cumulative \texttt{thread/tokenUsage/updated} notifications: the app-server adapter atomically publishes their ordered totals to a trusted result-log path outside the model workspace, freezes the first threshold-crossing update, and stops the app-server. The outer runner polls that path before submission validation and stops the remaining agent process group when needed. Input totals include cached input, which is counted once. Before matrix startup, the frozen low-cap canary independently demonstrated this path while the nested \texttt{rollout\_budget} remained at the full benchmark limit. That feature stays enabled with unit weights only as an advisory provider-side guard; it is not the benchmark's enforcing control. The program reads the environment identity, agent version, model, reasoning level, and limits from the authenticated metadata; they are not free command-line choices."
                )
            ),
            r"\begin{lstlisting}",
            "python3 paper_bencmark/highambench/tools/run_matrix.py \\",
            "  --benchmark-root paper_bencmark/highambench \\",
            "  --project-root . \\",
            "  --results-root paper_bencmark/scratch_pad/highambench_results \\",
            "  --codex <CODEX_BINARY> --auth-file <CODEX_AUTH_FILE> \\",
            "  --offline-shell <OFFLINE_SHELL_BINARY> \\",
            "  --toolchain-root <LEAN_TOOLCHAIN_ROOT> \\",
            "  --packages-root .lake/packages \\",
            "  --packages-runtime-root " + PACKAGES_RUNTIME_ROOT + " \\",
            "  --shared-olean-root paper_bencmark/scratch_pad/highambench_environment/shared_olean \\",
            "  --library-source NumStability --library-root-file NumStability.lean \\",
            "  --library-olean " + PRUNED_LIBRARY_OLEAN_ROOT + " \\",
            "  --release-manifest paper_bencmark/highambench/metadata/release_files.json \\",
            "  --agent-network-verified --token-control-verified",
            r"\end{lstlisting}",
            r"\subsection{3. Check completeness and make summary data}",
            r"\begin{lstlisting}",
            "python3 paper_bencmark/highambench/tools/analyze.py \\",
            "  paper_bencmark/scratch_pad/highambench_results/runs.jsonl \\",
            "  --output-dir paper_bencmark/scratch_pad/highambench_results/analysis \\",
            "  --run-order paper_bencmark/highambench/metadata/run_order.json \\",
            "  --config paper_bencmark/highambench/metadata/config.json \\",
            "  --manifest paper_bencmark/highambench/metadata/manifest.json \\",
            "  --repository-root . --observational-pilot",
            r"\end{lstlisting}",
            r"\subsection{4. Make this report and PDF}",
            r"\begin{lstlisting}",
            "python3 paper_bencmark/highambench/tools/render_report.py \\",
            "  --analysis paper_bencmark/scratch_pad/highambench_results/analysis/summary.json \\",
            "  --output-tex paper_bencmark/scratch_pad/HighamBench_Report.tex \\",
            "  --compile-pdf",
            r"\end{lstlisting}",
            "The report builder rereads the final metadata, evidence, reviews, and analysis. It also requires the nearby frozen-run check, checks its fingerprint against the accepted result set, verifies the release files, and compares the construction tools, Python executable, pruned package view, and pruned NumStability library with those fixed identities. It refuses missing runs, stale records, damaged network evidence, failed token-control evidence, failed construction checks, or missing task summaries. This prevents an incomplete measurement from becoming a polished report by accident.",
            r"\section{Final scope statement}",
            "This private snapshot contains " + latex_escape(measured_paper_count) + " paper(s) and " + latex_escape(measured_task_count) + " measured T1--T3 task(s), plus " + latex_escape(len(t4_coverage)) + " separate T4 whole-paper formalization record(s). The N/L score measures only the T1--T3 proof tasks; it does not measure unrestricted prose translation, and T4 is not folded into the overall difficulty score. It is not approved for public release.",
            "Recorded benchmark ID: " + _inline_code(benchmark_id) + ".",
            r"\end{document}",
            "",
        ]
    )
    return "\n".join(lines)


def write_report(output_tex: Path, document: str, *, compile_pdf: bool) -> Path | None:
    output = output_tex.resolve()
    if output.suffix.lower() != ".tex":
        raise ReportError("--output-tex must end in .tex")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name("." + output.name + ".tmp")
    temporary.write_text(document, encoding="utf-8")
    temporary.replace(output)
    if not compile_pdf:
        return None
    latexmk = shutil.which("latexmk")
    if latexmk is None:
        raise ReportError("--compile-pdf was requested, but latexmk is not installed")
    command = [
        latexmk,
        "-norc",
        "-pdf",
        "-interaction=nonstopmode",
        "-halt-on-error",
        f"-outdir={output.parent}",
        str(output),
    ]
    completed = subprocess.run(
        command,
        cwd=output.parent,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        tail = "\n".join(completed.stdout.splitlines()[-40:])
        raise ReportError(f"latexmk failed with exit code {completed.returncode}:\n{tail}")
    pdf = output.with_suffix(".pdf")
    if not pdf.is_file():
        raise ReportError("latexmk returned success but did not create the expected PDF")
    return pdf


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="HighamBench directory; defaults to the parent of tools/",
    )
    parser.add_argument("--analysis", type=Path, required=True, help="analyze.py summary.json")
    parser.add_argument("--output-tex", type=Path, required=True)
    parser.add_argument("--compile-pdf", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        inputs = load_report_inputs(args.benchmark_root, args.analysis)
        document = render_report(inputs)
        pdf = write_report(args.output_tex, document, compile_pdf=args.compile_pdf)
        result = {
            "benchmark_id": inputs.config.get("benchmark_id"),
            "latex": str(args.output_tex.resolve()),
            "pdf": str(pdf) if pdf is not None else None,
            "official_scores_valid": inputs.analysis.get("official_scores_valid") is True,
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (OSError, ReportError) as error:
        print(f"report error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
