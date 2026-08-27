#!/usr/bin/env python3
"""Validate a complete HighamBench result matrix before final analysis.

The runner deliberately handles one run at a time.  This module performs the
cross-run checks that a one-run validator cannot perform: the planned matrix is
complete, N/L order is respected, paired metadata agrees, system-error reruns
are resolved, and every final record matches the frozen benchmark metadata.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path, PurePosixPath
import platform
import stat
import sys
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, FAILURE_CODES, SCHEMA_VERSION, read_json, sha256_file, write_json
    from . import run_matrix
    from . import run_token_control_canary as token_canary
    from . import run_ultra_orchestration_canary as ultra_canary
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        FAILURE_CODES,
        SCHEMA_VERSION,
        read_json,
        sha256_file,
        write_json,
    )
    import run_matrix  # type: ignore
    import run_token_control_canary as token_canary  # type: ignore
    import run_ultra_orchestration_canary as ultra_canary  # type: ignore


AgentKey = tuple[str, str, str]
AssignmentKey = tuple[str, str, str]

PROTOCOL_CLAIMS = (
    "fresh_conversation",
    "filesystem_isolated",
    "network_disabled",
    "backend_seed_supplied",
    "seed_enforced_by_agent",
    "token_limit_enforced_by_agent",
    "condition_l_library_available",
)
PROTOCOL_VERIFICATIONS = (
    "fresh_workspace_copy",
    "condition_n_preflight",
    "condition_n_import_probe_complete",
    "network_violation_marker_integrity",
)
# These controls depend on features supplied by the chosen model backend or
# adapter.  A complete pilot may be reported as observational when they are not
# available.  Isolation and condition-separation failures are never relaxed.
OBSERVATIONAL_CONTROL_CLAIMS = {
    "backend_seed_supplied",
    "seed_enforced_by_agent",
    "token_limit_enforced_by_agent",
}
ENVIRONMENT_BUNDLE_DEFINITION = (
    "SHA-256 of UTF-8 canonical JSON with sorted keys and compact separators over an "
    "object containing the complete config and environment records, after removing "
    "environment_id and environment_bundle_sha256 from their top-level/frozen locations."
)
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)
TOKEN_USAGE_MEASUREMENT_SOURCE = "codex_app_server_rawResponse/completed"
TOKEN_MEASUREMENT_SOURCE = (
    "Codex app-server rawResponse/completed exact rooted-thread-tree ledger"
)
TOKEN_LIMIT_ENFORCEMENT_MODE = (
    "first_authenticated_provider_gate_crossing_commit_at_or_above_limit"
)
TOKEN_LIMIT_NOTIFICATION = "rawResponse/completed"
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
LEGACY_TOKEN_USAGE_MEASUREMENT_SOURCE = (
    "codex_app_server_thread/tokenUsage/updated"
)
LEGACY_TOKEN_MEASUREMENT_SOURCE = (
    "Codex app-server thread/tokenUsage/updated live cumulative notification"
)
LEGACY_TOKEN_LIMIT_ENFORCEMENT_MODE = (
    "first_live_cumulative_update_at_or_above_limit"
)
LEGACY_TOKEN_LIMIT_NOTIFICATION = "thread/tokenUsage/updated"
LEGACY_TOKEN_USAGE_SCOPE = "thread"
TOKEN_TIMESTAMP_TOLERANCE_NS = 5_000_000_000
POST_SUBMISSION_FRESHNESS_BASES = {
    "trusted_notification_observed_at_or_after_submission_detection",
    "newer_notification_sequence",
    "clean_adapter_exit_with_final_usage",
    "ultra_tree_quiescence_with_final_ledger",
    "authenticated_outer_exec_raw_response_with_blocked_inner_submit_boundary",
}
ULTRA_PASS_FRESHNESS_BASIS = (
    "authenticated_outer_exec_raw_response_with_blocked_inner_submit_boundary"
)
ULTRA_PASS_TIME_MEASUREMENT = (
    "authenticated CLOCK_MONOTONIC turn/start write to authenticated nested "
    "submission-boundary publication after outer exec raw-response completion "
    "with inner submit_proof blocked; hidden validation certifies the immutable "
    "requested bytes"
)
SUBMISSION_BARRIER_SCHEMA_VERSION = (
    ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
)
NESTED_SUBMISSION_WIRE_FORMAT = ultra_canary.codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT
NESTED_SUBMISSION_EXEC_SOURCE_BYTES = (
    ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
)
NESTED_SUBMISSION_EXEC_SOURCE_SHA256 = (
    ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
)
NESTED_SUBMISSION_EXEC_YIELD_RECORD = (
    ultra_canary.codex_isolated.nested_submission_exec_yield_record()
)
SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE = (
    ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
)
SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER = (
    ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
)
SUBMISSION_BARRIER_ARTIFACTS = ("challenge", "call", "request", "ack", "snapshot")
SUBMISSION_BARRIER_RECORD_FIELDS = {
    "challenge": ("challenge_sha256", "highambench_submission_challenge"),
    "call": ("call_sha256", "highambench_submission_call"),
    "request": ("request_sha256", "highambench_submission_request"),
    "ack": ("ack_sha256", "highambench_submission_ack"),
}
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
VALIDATION_AUTHENTICATION_FIELDS = {
    "schema_version",
    "run_id",
    "task_id",
    "candidate_sha256",
    "target_theorem",
    "controlled_manifest_sha256",
    "validator_contract_sha256",
    "submission_request_sha256",
    "submission_sequence",
}
PLURAL_VALIDATION_AUTHENTICATION_FIELDS = {
    "schema_version",
    "run_id",
    "task_id",
    "candidate_sha256",
    "required_declarations",
    "controlled_sorries",
    "controlled_manifest_sha256",
    "validator_contract_sha256",
    "submission_request_sha256",
    "submission_sequence",
}
CONTROLLED_SORRY_FIELDS = {
    "placeholder_order",
    "placeholder_id",
    "declaration_id",
    "lean_name",
    "marker",
    "line",
    "column",
}


def _valid_nested_submission_wire(value: Any) -> bool:
    """Independently require the frozen outer-exec/inner-dynamic wire identity."""

    if not isinstance(value, Mapping):
        return False
    inner_call_id = value.get("call_id")
    outer_call_id = value.get("outer_exec_call_id")
    outer_raw_item_id = value.get("outer_raw_item_id")
    outer_observed_ns = value.get("outer_raw_item_observed_at_monotonic_ns")
    inner_started_ns = value.get("inner_dynamic_item_started_at_monotonic_ns")
    return (
        value.get("schema_version") == SUBMISSION_BARRIER_SCHEMA_VERSION
        and value.get("candidate_path") == "Candidate.lean"
        and value.get("submission_transport") == NESTED_SUBMISSION_WIRE_FORMAT
        and isinstance(outer_raw_item_id, str)
        and bool(outer_raw_item_id)
        and value.get("outer_raw_item_type") == "custom_tool_call"
        and value.get("outer_exec_name") == "exec"
        and isinstance(outer_call_id, str)
        and bool(outer_call_id)
        and isinstance(inner_call_id, str)
        and bool(inner_call_id)
        and len({outer_raw_item_id, outer_call_id, inner_call_id}) == 3
        and value.get("inner_dynamic_call_id") == inner_call_id
        and value.get("inner_dynamic_tool_name") == "submit_proof"
        and value.get("inner_dynamic_arguments")
        == {"candidate_path": "Candidate.lean"}
        and ultra_canary.codex_isolated.is_canonical_nested_submit_exec_input(
            value.get("outer_exec_program"), candidate_path="Candidate.lean"
        )
        and value.get("outer_exec_program_bytes")
        == NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        and value.get("outer_exec_program_sha256")
        == NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        and all(
            value.get(field) == expected
            for field, expected in NESTED_SUBMISSION_EXEC_YIELD_RECORD.items()
        )
        and type(outer_observed_ns) is int
        and type(inner_started_ns) is int
        and 0 < outer_observed_ns <= inner_started_ns
        and value.get("outer_raw_item_observed_before_inner_dynamic_call") is True
    )


def _valid_submission_event_order(
    value: Any, *, derive_from_timestamps: bool
) -> bool:
    """Require one schema-v5 event order and, for requests, derive it again."""

    if not isinstance(value, Mapping):
        return False
    dynamic_before = value.get(
        "dynamic_call_observed_before_raw_response_completed"
    )
    response_before = value.get(
        "raw_response_completed_before_dynamic_call_observed"
    )
    order = value.get("submission_event_order")
    if (dynamic_before, response_before) == (True, False):
        if order != SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE:
            return False
    elif (dynamic_before, response_before) == (False, True):
        if order != SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER:
            return False
    else:
        return False
    if value.get("raw_response_completed_before_boundary_publication") is not True:
        return False
    if not derive_from_timestamps:
        return True
    captured_ns = value.get("captured_at_monotonic_ns")
    response_ns = value.get("raw_response_observed_at_monotonic_ns")
    published_ns = value.get("request_published_at_monotonic_ns")
    if any(type(item) is not int or item <= 0 for item in (
        captured_ns,
        response_ns,
        published_ns,
    )):
        return False
    assert isinstance(captured_ns, int)
    assert isinstance(response_ns, int)
    assert isinstance(published_ns, int)
    return (
        captured_ns != response_ns
        and dynamic_before is (captured_ns < response_ns)
        and response_ns <= published_ns
        and captured_ns <= published_ns
    )
FROZEN_TOKEN_CANARY_PATH = token_canary.FROZEN_EVIDENCE_PATH
TOKEN_CANARY_ARTIFACT_LABELS = token_canary.ARTIFACT_LABELS
FROZEN_ULTRA_CANARY_PATH = ultra_canary.FROZEN_EVIDENCE_PATH
SIGNPOSTED_PROMPT_PROTOCOL_VERSION = "signposted-library-v1"
SIGNPOSTED_PROMPT_COMPOSITION_ORDER = [
    "common_prompt",
    "condition_L_supplement_if_condition_L",
    "task_context",
    "fixed_target",
]
EFFECTIVE_PROMPT_COMPOSITION = (
    "utf8_rstrip_each_section_join_two_newlines_final_newline_v1"
)
PROMPT_RELEASE_PROTOCOL_VERSION = "highambench-prompt-release-v1"
PROMPT_RELEASE_SCHEMA_VERSION = 1
PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS = 120.0
PROMPT_RELEASE_GO_MINIMUM_WINDOW_SECONDS = 5.0
PROMPT_RELEASE_ARTIFACTS = {
    "ready": ("ready_sha256", "highambench_prompt_ready", ".prompt-ready.json"),
    "go": ("go_sha256", "highambench_prompt_go", ".prompt-go.json"),
    "released": (
        "release_sha256",
        "highambench_prompt_released",
        ".prompt-release.json",
    ),
}
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
        value.get("schema_version") != PROMPT_RELEASE_SCHEMA_VERSION
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
        != len(TOKEN_CANARY_ARTIFACT_LABELS)
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
        and value.get("measurement_source") == TOKEN_USAGE_MEASUREMENT_SOURCE
        and value.get("notification") == TOKEN_LIMIT_NOTIFICATION
        and value.get("usage_scope") == TOKEN_USAGE_SCOPE
    )


def _valid_token_control(value: Any, token_limit: Any) -> bool:
    """Recognize either frozen token contract without permitting a mixed schema.

    Ultra is accounted from response-ID-deduplicated ``rawResponse/completed``
    events over the complete rooted coordinator/subagent tree.  The legacy
    branch remains readable so already-recorded raw-access xhigh result bundles
    can still be authenticated with their own frozen metadata.
    """

    if (
        not isinstance(value, Mapping)
        or not isinstance(token_limit, int)
        or isinstance(token_limit, bool)
        or token_limit <= 0
    ):
        return False
    common_fields = {
        "comparison": ">=",
        "limit_tokens": token_limit,
    }
    if any(value.get(field) != wanted for field, wanted in common_fields.items()):
        return False
    if (
        not isinstance(value.get("limit_tokens"), int)
        or isinstance(value.get("limit_tokens"), bool)
    ):
        return False
    if any(
        value.get(field) is not True
        for field in (
            "cached_input_counted_once",
            "checked_before_submission_validation",
            "input_includes_cached",
            "live_update_sequence",
            "live_cumulative",
            "outer_runner_polling",
            "trusted_usage_path_outside_workspace",
        )
    ) or value.get("over_limit_pass_allowed") is not False:
        return False

    ultra_contract = {
        "control": "loopback_provider_response_admission_gate",
        "measurement_source": TOKEN_USAGE_MEASUREMENT_SOURCE,
        "notification": TOKEN_LIMIT_NOTIFICATION,
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
        "provider_gate_protocol": ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "provider_response_bound_tokens": 272_000,
        "strict_admission_inequality": (
            "completed_tokens + (open_request_count + 1) * "
            "response_bound < token_limit"
        ),
        "crossing_response_release": (
            ultra_canary.runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY
        ),
        "crossing_response_actions_released": False,
        "provider_requests_quiescent_at_scored_endpoint": True,
        "tree_quiescence_distinct_from_provider_quiescence": True,
    }
    legacy_contract = {
        "control": "app_server_live_cumulative_usage",
        "measurement_source": LEGACY_TOKEN_USAGE_MEASUREMENT_SOURCE,
        "notification": LEGACY_TOKEN_LIMIT_NOTIFICATION,
        "usage_scope": LEGACY_TOKEN_USAGE_SCOPE,
        "one_response_overshoot_possible": True,
        "trusted_adapter_freezes_first_threshold": True,
    }
    matches_ultra = all(
        value.get(field) == wanted for field, wanted in ultra_contract.items()
    )
    ultra_only_fields = set(ultra_contract) - set(legacy_contract)
    matches_legacy = all(
        value.get(field) == wanted for field, wanted in legacy_contract.items()
    ) and all(field not in value for field in ultra_only_fields)
    if not (matches_ultra or matches_legacy):
        return False

    advisory = value.get("advisory_rollout_budget")
    if not isinstance(advisory, Mapping) or (
        advisory.get("enabled") is not True
        or advisory.get("feature") != "rollout_budget"
        or not isinstance(advisory.get("feature_row"), str)
        or not advisory.get("feature_row", "").startswith("rollout_budget ")
        or advisory.get("strict_config") is not True
        or advisory.get("limit_tokens") != token_limit
        or not isinstance(advisory.get("limit_tokens"), int)
        or isinstance(advisory.get("limit_tokens"), bool)
        or advisory.get("role") != "advisory_only"
    ):
        return False
    return all(
        isinstance(advisory.get(field), int)
        and not isinstance(advisory.get(field), bool)
        and advisory.get(field) == 1
        for field in ("prefill_token_weight", "sampling_token_weight")
    )


def _valid_token_canary_descriptor(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and value.get("path") == FROZEN_TOKEN_CANARY_PATH
        and value.get("status") == "passed"
        and _hex_digest(value.get("sha256"))
    )


def _valid_token_canary_summary(
    value: Any,
    descriptor: Any,
    token_limit: Any,
) -> bool:
    if (
        not isinstance(value, Mapping)
        or not _valid_token_canary_descriptor(descriptor)
        or value.get("path") != descriptor.get("path")
        or value.get("sha256") != descriptor.get("sha256")
        or value.get("status") != "passed"
        or not isinstance(token_limit, int)
        or isinstance(token_limit, bool)
        or token_limit <= 0
    ):
        return False
    canary_limit = value.get("canary_limit_tokens")
    crossing = value.get("first_crossing_tokens")
    final_tokens = value.get("final_endpoint_tokens")
    if (
        not isinstance(canary_limit, int)
        or isinstance(canary_limit, bool)
        or canary_limit != token_canary.DEFAULT_CANARY_TOKEN_LIMIT
        or not 0 < canary_limit < token_limit
        or not isinstance(crossing, int)
        or isinstance(crossing, bool)
        or crossing < canary_limit
        or not isinstance(final_tokens, int)
        or isinstance(final_tokens, bool)
        or final_tokens != crossing
        or value.get("thread_count") != 1
        or value.get("observed_child_thread_count") != 0
        or value.get("response_count") != 2
        or value.get("drain_complete") is not False
        or value.get("provider_gate_quiescent") is not True
        or value.get("measurement_exact") is not True
        or value.get("synthetic_input") is not True
        or value.get("matrix_assignment") is not False
        or value.get("benchmark_task_bytes_used") is not False
        or value.get("prompt_protocol") != token_canary.PROMPT_PROTOCOL
        or not _hex_digest(value.get("source_separation_audit_sha256"))
        or not _valid_token_canary_prompt_release(value.get("prompt_release"))
    ):
        return False
    projection = value.get("accounting_projection")
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
        not isinstance(projection, Mapping)
        or set(projection) != expected_projection_fields
        or projection.get("accounting_projection_schema_version")
        != token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or projection.get("provider_gate_protocol")
        != ultra_canary.runner.PROVIDER_GATE_PROTOCOL
        or not _hex_digest(projection.get("provider_gate_record_sha256"))
        or projection.get("provider_gate_close_reason") != "token_limit"
        or not isinstance(projection.get("provider_gate_response_ids"), list)
        or len(projection.get("provider_gate_response_ids")) != 2
        or projection.get("provider_gate_deliveries_reconciled") is not True
        or projection.get("provider_gate_setup_requests_empty") is not True
        or projection.get("provider_requests_quiescent") is not True
        or projection.get("adapter_teardown_complete") is not True
        or projection.get("spawn_binding_source")
        != ACCOUNTING_SPAWN_BINDING_SOURCE
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
        or _canonical_record_sha256(projection, "projection_payload_sha256")
        != projection.get("projection_payload_sha256")
    ):
        return False
    try:
        reconciliation = run_matrix.verify_provider_usage_reconciliation(
            projection.get("provider_usage_reconciliation"),
            expected_provider_response_ids=projection.get(
                "provider_gate_response_ids"
            ),
            expected_appserver_response_ledger=projection.get(
                "appserver_response_ledger"
            ),
            required_suppressed_wait_count=0,
            required_superseded_collaboration_message_count=0,
            required_discarded_after_explicit_child_interrupt_count=0,
        )
    except BenchmarkToolError:
        return False
    if reconciliation.get("provider_response_count") != 2:
        return False
    artifacts = value.get("artifacts")
    if not isinstance(artifacts, Mapping) or set(artifacts) != set(
        TOKEN_CANARY_ARTIFACT_LABELS
    ):
        return False
    for label in TOKEN_CANARY_ARTIFACT_LABELS:
        artifact = artifacts.get(label)
        if not isinstance(artifact, Mapping):
            return False
        relative = artifact.get("path")
        size = artifact.get("bytes")
        if (
            not isinstance(relative, str)
            or not relative
            or PurePosixPath(relative).is_absolute()
            or ".." in PurePosixPath(relative).parts
            or not _hex_digest(artifact.get("sha256"))
            or not isinstance(size, int)
            or isinstance(size, bool)
            or size <= 0
        ):
            return False
    return True


def _valid_ultra_canary_descriptor(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and value.get("path") == FROZEN_ULTRA_CANARY_PATH
        and value.get("status") == "passed"
        and _hex_digest(value.get("sha256"))
    )


def _valid_ultra_canary_summary(value: Any, descriptor: Any) -> bool:
    if (
        not isinstance(value, Mapping)
        or not _valid_ultra_canary_descriptor(descriptor)
        or value.get("path") != descriptor.get("path")
        or value.get("sha256") != descriptor.get("sha256")
        or value.get("status") != "passed"
        or value.get("drain_complete") is not False
        or value.get("measurement_exact") is not True
        or value.get("submission_boundary_exact") is not True
    ):
        return False
    projection = value.get("accounting_projection")
    if (
        not isinstance(projection, Mapping)
        or projection.get("accounting_projection_schema_version")
        != ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or projection.get("provider_gate_protocol")
        != ultra_canary.runner.PROVIDER_GATE_PROTOCOL
        or not _hex_digest(projection.get("provider_gate_record_sha256"))
        or projection.get("provider_gate_close_reason") != "accepted_submission"
        or not isinstance(projection.get("provider_gate_response_ids"), list)
        or not projection.get("provider_gate_response_ids")
        or projection.get("provider_gate_deliveries_reconciled") is not True
        or projection.get("provider_gate_setup_requests_empty") is not True
        or projection.get("provider_requests_quiescent") is not True
        or projection.get("adapter_teardown_complete") is not True
        or projection.get("spawn_binding_source") != ACCOUNTING_SPAWN_BINDING_SOURCE
        or projection.get("raw_call_activity_id_match") is not True
        or projection.get("completed_root_response_before_spawn") is not True
        or not isinstance(projection.get("fork_turns_all_child_thread_count"), int)
        or isinstance(projection.get("fork_turns_all_child_thread_count"), bool)
        or projection.get("fork_turns_all_child_thread_count") < 1
        or not isinstance(
            projection.get("nonzero_inherited_baseline_child_thread_ids"), list
        )
        or not projection.get("nonzero_inherited_baseline_child_thread_ids")
        or any(
            projection.get(field) is not True
            for field in (
                "spawn_linkage_complete",
                "descendant_accounting_complete",
                "cumulative_projection_complete",
                "fork_policy_complete",
                "accounting_complete",
            )
        )
        or not _hex_digest(projection.get("projection_payload_sha256"))
        or _canonical_record_sha256(
            projection, "projection_payload_sha256"
        ) != projection.get("projection_payload_sha256")
        or not isinstance(projection.get("thread_accounting"), list)
        or len(projection.get("thread_accounting")) != value.get("thread_count")
    ):
        return False
    try:
        reconciliation = run_matrix.verify_provider_usage_reconciliation(
            projection.get("provider_usage_reconciliation"),
            expected_provider_response_ids=projection.get(
                "provider_gate_response_ids"
            ),
            expected_appserver_response_ledger=projection.get(
                "appserver_response_ledger"
            ),
            required_suppressed_wait_count=None,
            expected_thread_accounting=projection.get("thread_accounting"),
        )
    except BenchmarkToolError:
        return False
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
        "nonzero_inherited_baseline_child_thread_ids",
    ):
        identifiers = projection.get(field)
        if (
            not isinstance(identifiers, list)
            or identifiers != sorted(set(identifiers))
            or any(not isinstance(item, str) or not item for item in identifiers)
        ):
            return False
    try:
        raw_ids = _accounting_identifier_set(
            projection.get("raw_spawn_call_ids"), "canary raw spawn IDs"
        )
        activity_ids = _accounting_identifier_set(
            projection.get("activity_spawn_call_ids"), "canary activity IDs"
        )
        collab_ids = _accounting_identifier_set(
            projection.get("collab_spawn_call_ids"), "canary collab IDs"
        )
        resolved_ids = _accounting_identifier_set(
            projection.get("resolved_spawn_call_ids"), "canary resolved IDs"
        )
        failed_ids = _accounting_identifier_set(
            projection.get("failed_spawn_call_ids"), "canary failed IDs"
        )
        blocked_ids = _accounting_identifier_set(
            projection.get("policy_blocked_spawn_call_ids"),
            "canary policy-blocked IDs",
        )
        unsupported_ids = _accounting_identifier_set(
            projection.get("unsupported_spawn_call_ids"), "canary unsupported IDs"
        )
        unresolved_ids = _accounting_identifier_set(
            projection.get("unresolved_spawn_call_ids"), "canary unresolved IDs"
        )
        child_ids = _accounting_identifier_set(
            projection.get("inference_child_thread_ids"), "canary child IDs"
        )
        accounting = projection.get("thread_accounting")
        known_threads = {
            str(thread.get("thread_id"))
            for thread in accounting
            if isinstance(thread, Mapping)
            and isinstance(thread.get("thread_id"), str)
            and thread.get("thread_id")
        }
        calls = _validate_ultra_fork_policy(
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
    except _AccountingProjectionError:
        return False
    if (
        value.get("thread_count") != 2
        or value.get("observed_descendant_thread_count") != 1
        or value.get("positive_usage_descendant_thread_count") != 1
        or len(resolved_ids) != 1
        or len(blocked_ids) != 2
        or failed_ids != blocked_ids
        or raw_ids != resolved_ids | blocked_ids
        or unresolved_ids
        or len(child_ids) != 1
        or projection.get("nonzero_inherited_baseline_child_thread_ids")
        != sorted(child_ids)
    ):
        return False
    allowed_call = calls[next(iter(resolved_ids))]
    root_id = allowed_call.get("parent_thread_id")
    blocked_calls = [calls[call_id] for call_id in sorted(blocked_ids)]
    if (
        allowed_call.get("fork_turns") != "all"
        or not isinstance(root_id, str)
        or {call.get("parent_thread_id") for call in blocked_calls}
        != {root_id, next(iter(child_ids))}
        or any(call.get("fork_turns") != "3" for call in blocked_calls)
    ):
        return False
    validation_auth = value.get("validation_authentication")
    if (
        not isinstance(validation_auth, Mapping)
        or validation_auth.get("schema_version") != 1
        or validation_auth.get("authenticated") is not True
        or any(
            not _hex_digest(validation_auth.get(field))
            for field in (
                "record_sha256",
                "validation_log_sha256",
                "candidate_sha256",
                "validator_contract_sha256",
                "submission_request_sha256",
            )
        )
        or not isinstance(validation_auth.get("submission_sequence"), int)
        or isinstance(validation_auth.get("submission_sequence"), bool)
        or validation_auth.get("submission_sequence") <= 0
    ):
        return False
    dependency_audit = value.get("dependency_audit")
    if (
        not isinstance(dependency_audit, Mapping)
        or dependency_audit.get("complete") is not True
        or not _hex_digest(dependency_audit.get("helper_sha256"))
        or not _hex_digest(dependency_audit.get("command_sha256"))
        or dependency_audit.get("library_use") is not False
        or dependency_audit.get("library_declarations") != []
        or dependency_audit.get("target_seen") is not True
        or dependency_audit.get("semantic_type_equal") is not True
    ):
        return False
    prompt_release = value.get("prompt_release")
    if (
        not isinstance(prompt_release, Mapping)
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
        or not isinstance(
            prompt_release.get("released_at_monotonic_ns"), int
        )
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
        return False
    for field, minimum in (
        ("thread_count", 2),
        ("observed_descendant_thread_count", 1),
        ("positive_usage_descendant_thread_count", 1),
        ("response_count", 1),
        ("total_model_tokens", 1),
    ):
        raw = value.get(field)
        if not isinstance(raw, int) or isinstance(raw, bool) or raw < minimum:
            return False
    barrier = value.get("barrier")
    if (
        not isinstance(barrier, Mapping)
        or not _valid_nested_submission_wire(barrier)
        or not _valid_submission_event_order(
            barrier, derive_from_timestamps=True
        )
        or not isinstance(barrier.get("sequence"), int)
        or isinstance(barrier.get("sequence"), bool)
        or barrier.get("sequence") <= 0
        or barrier.get("retained_read_only") is not True
        or not all(
            _hex_digest(barrier.get(field))
            for field in (
                "challenge_sha256",
                "call_sha256",
                "request_sha256",
                "ack_sha256",
                "candidate_sha256",
                "validator_contract_sha256",
            )
        )
        or not isinstance(barrier.get("candidate_size_bytes"), int)
        or isinstance(barrier.get("candidate_size_bytes"), bool)
        or barrier.get("candidate_size_bytes") <= 0
        or barrier.get("outer_raw_item_and_call_ids_pairwise_distinct") is not True
        or barrier.get("outer_raw_item_observed_before_inner_dynamic_call") is not True
        or barrier.get("inner_dynamic_item_started") is not True
        or barrier.get("inner_submit_invocation_exact") is not True
        or barrier.get("inner_submit_only_nested_tool_call") is not True
    ):
        return False
    artifacts = value.get("artifacts")
    if not isinstance(artifacts, Mapping) or set(artifacts) != set(
        ultra_canary.ARTIFACT_LABELS
    ):
        return False
    return all(
        isinstance(artifact, Mapping)
        and isinstance(artifact.get("path"), str)
        and bool(artifact.get("path"))
        and _hex_digest(artifact.get("sha256"))
        and isinstance(artifact.get("bytes"), int)
        and not isinstance(artifact.get("bytes"), bool)
        and artifact.get("bytes") > 0
        for artifact in artifacts.values()
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


def _agent_key(run: Mapping[str, Any]) -> AgentKey:
    agent = run.get("agent")
    if not isinstance(agent, Mapping):
        return ("unknown", "unknown", "unknown")
    return (
        str(agent.get("id", "unknown")),
        str(agent.get("version", "unknown")),
        str(agent.get("model", "unknown")),
    )


def _assignment_key(run: Mapping[str, Any]) -> AssignmentKey | None:
    task = run.get("task_id")
    repetition = run.get("repetition_id")
    condition = run.get("condition")
    if not isinstance(task, str) or not isinstance(repetition, str) or condition not in ("N", "L"):
        return None
    return task, repetition, condition


def _hex_digest(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(
        character in "0123456789abcdef" for character in value
    )


def _iso_time(value: Any) -> dt.datetime | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=dt.timezone.utc)
    return parsed


def _document_digest(value: Mapping[str, Any]) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _authenticate_token_canary_production_freeze(
    repository_root: Path,
    evidence: Mapping[str, Any],
    *,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
    errors: list[str],
) -> bool:
    """Reopen and bind the token canary's authenticated production freeze."""

    project = repository_root.resolve()
    artifact_root_raw = evidence.get("artifact_root")
    if not isinstance(artifact_root_raw, str) or not artifact_root_raw:
        errors.append("token-control canary artifact root is missing")
        return False
    artifact_root_relative = PurePosixPath(artifact_root_raw)
    if artifact_root_relative.is_absolute() or ".." in artifact_root_relative.parts:
        errors.append("token-control canary artifact root has an unsafe path")
        return False
    unresolved_artifact_root = project / artifact_root_relative
    if unresolved_artifact_root.is_symlink():
        errors.append("token-control canary artifact root must not be a symlink")
        return False
    artifact_root = unresolved_artifact_root.resolve()
    try:
        artifact_root.relative_to(project)
    except ValueError:
        errors.append("token-control canary artifact root escapes repository root")
        return False
    if not artifact_root.is_dir():
        errors.append("token-control canary artifact root is missing")
        return False

    artifacts = evidence.get("artifacts")
    descriptor = artifacts.get("freeze_check") if isinstance(artifacts, Mapping) else None
    if not isinstance(descriptor, Mapping) or set(descriptor) != {"path", "sha256"}:
        errors.append(
            "token-control canary production freeze artifact descriptor is invalid"
        )
        return False
    relative_raw = descriptor.get("path")
    if not isinstance(relative_raw, str) or not relative_raw:
        errors.append("token-control canary production freeze artifact path is missing")
        return False
    relative = PurePosixPath(relative_raw)
    if relative.is_absolute() or ".." in relative.parts:
        errors.append("token-control canary production freeze artifact path is unsafe")
        return False
    unresolved_artifact = artifact_root / relative
    if unresolved_artifact.is_symlink():
        errors.append(
            "token-control canary production freeze artifact must not be a symlink"
        )
        return False
    artifact_path = unresolved_artifact.resolve()
    try:
        artifact_path.relative_to(artifact_root)
    except ValueError:
        errors.append(
            "token-control canary production freeze artifact escapes its artifact root"
        )
        return False
    expected_sha256 = descriptor.get("sha256")
    if not artifact_path.is_file() or not _hex_digest(expected_sha256):
        errors.append("token-control canary production freeze artifact is missing")
        return False
    try:
        actual_sha256 = sha256_file(artifact_path)
    except OSError as error:
        errors.append(
            f"token-control canary production freeze artifact cannot be read: {error}"
        )
        return False
    if actual_sha256 != expected_sha256:
        errors.append(
            "token-control canary production freeze artifact has the wrong SHA-256"
        )
        return False
    try:
        production_freeze = read_json(artifact_path)
    except BenchmarkToolError as error:
        errors.append(str(error))
        return False
    if not isinstance(production_freeze, Mapping):
        errors.append("token-control canary production freeze artifact is not an object")
        return False
    if production_freeze.get("prompt_protocol") != dict(prompt_protocol):
        errors.append("token-control canary production prompt protocol is stale")
        return False
    if production_freeze.get("execution_components") != dict(execution_components):
        errors.append("token-control canary production execution components are stale")
        return False
    return True


def _authenticated_token_canary_summary(
    repository_root: Path,
    descriptor: Mapping[str, Any],
    *,
    config: Mapping[str, Any],
    frozen: Mapping[str, Any],
    token_limit: int,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
    errors: list[str],
) -> dict[str, Any] | None:
    """Authenticate the private synthetic canary with its canonical verifier."""

    evidence_path = (repository_root.resolve() / FROZEN_TOKEN_CANARY_PATH).resolve()
    try:
        evidence_path.relative_to(repository_root.resolve())
    except ValueError:
        errors.append("token-control canary evidence path escapes repository root")
        return None
    if not evidence_path.is_file():
        errors.append("token-control canary evidence file is missing")
        return None
    if sha256_file(evidence_path) != descriptor.get("sha256"):
        errors.append("token-control canary evidence has the wrong SHA-256")
        return None
    expected_agent = {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "binary_sha256": frozen.get("agent_binary_sha256"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
        "ultra_orchestration": frozen.get("ultra_orchestration"),
    }
    try:
        evidence = read_json(evidence_path)
        if not isinstance(evidence, Mapping):
            raise BenchmarkToolError(
                "synthetic token-canary evidence must be a JSON object"
            )
        summary = token_canary.validate_attestation_document(
            evidence,
            project_root=repository_root,
            expected_benchmark_id=str(config.get("benchmark_id")),
            expected_agent=expected_agent,
            expected_frozen_token_limit=token_limit,
        )
    except (OSError, RuntimeError, BenchmarkToolError) as error:
        errors.append(str(error))
        return None
    if not _authenticate_token_canary_production_freeze(
        repository_root,
        evidence,
        prompt_protocol=prompt_protocol,
        execution_components=execution_components,
        errors=errors,
    ):
        return None
    return {
        "path": FROZEN_TOKEN_CANARY_PATH,
        "sha256": descriptor.get("sha256"),
        **summary,
    }


def _authenticated_ultra_canary_summary(
    repository_root: Path,
    descriptor: Mapping[str, Any],
    *,
    config: Mapping[str, Any],
    frozen: Mapping[str, Any],
    token_limit: int,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
    errors: list[str],
) -> dict[str, Any] | None:
    """Authenticate and replay the separate synthetic delegation witness."""

    expected_agent = {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "binary_sha256": frozen.get("agent_binary_sha256"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
        "ultra_orchestration": frozen.get("ultra_orchestration"),
    }
    try:
        return ultra_canary.verify_frozen_attestation(
            repository_root,
            descriptor,
            expected_benchmark_id=str(config.get("benchmark_id")),
            expected_agent=expected_agent,
            expected_token_limit=token_limit,
            expected_prompt_protocol=prompt_protocol,
            expected_execution_components=execution_components,
        )
    except (OSError, RuntimeError, BenchmarkToolError) as error:
        errors.append(str(error))
        return None


def _environment_bundle_digest(
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
    return _document_digest({"config": config_copy, "environment": environment_copy})


def _expected_environment_id(
    manifest: Mapping[str, Any], bundle_digest: str
) -> str | None:
    """Derive the environment ID from the ordered benchmark corpus and bundle."""

    papers = manifest.get("papers")
    if not isinstance(papers, list) or not papers:
        return None
    paper_ids: list[str] = []
    for paper in papers:
        if not isinstance(paper, Mapping):
            return None
        paper_id = paper.get("paper_id")
        if not isinstance(paper_id, str) or not paper_id:
            return None
        paper_ids.append(paper_id.lower())
    corpus_id = "-".join(paper_ids)
    return f"highambench-{corpus_id}-{bundle_digest[:16]}"


def _contains_text(value: Any, needle: str) -> bool:
    if isinstance(value, str):
        return needle.lower() in value.lower()
    if isinstance(value, Mapping):
        return any(
            _contains_text(key, needle) or _contains_text(item, needle)
            for key, item in value.items()
        )
    if isinstance(value, list):
        return any(_contains_text(item, needle) for item in value)
    return False


def _metadata_tasks(manifest: Mapping[str, Any], errors: list[str]) -> dict[str, dict[str, Any]]:
    tasks: dict[str, dict[str, Any]] = {}
    papers = manifest.get("papers")
    if not isinstance(papers, list) or not papers:
        errors.append("manifest has no papers")
        return tasks
    for paper in papers:
        if not isinstance(paper, Mapping):
            errors.append("manifest contains a non-object paper entry")
            continue
        paper_id = paper.get("paper_id")
        source = paper.get("source")
        paper_digest = source.get("sha256") if isinstance(source, Mapping) else None
        if not isinstance(paper_id, str) or not _hex_digest(paper_digest):
            errors.append(f"manifest paper has invalid id or source hash: {paper_id!r}")
            continue
        targets = paper.get("targets")
        if not isinstance(targets, list) or not targets:
            errors.append(f"manifest paper {paper_id} has no targets")
            continue
        for target in targets:
            if not isinstance(target, Mapping):
                errors.append(f"manifest paper {paper_id} contains a non-object target")
                continue
            task_id = target.get("task_id")
            tier = target.get("tier")
            if not isinstance(task_id, str) or tier not in ("T1", "T2", "T3", "T4"):
                errors.append(f"manifest contains invalid task id or tier: {task_id!r}/{tier!r}")
                continue
            if task_id in tasks:
                errors.append(f"manifest repeats task {task_id}")
                continue
            lean_target = target.get("lean_target")
            declared_target = (
                lean_target.get("file") if isinstance(lean_target, Mapping) else None
            )
            target_relative: str | None = None
            context_relative: str | None = None
            if isinstance(declared_target, str) and declared_target:
                declared_path = PurePosixPath(declared_target)
                benchmark_prefix = PurePosixPath("paper_bencmark/highambench")
                try:
                    declared_path = declared_path.relative_to(benchmark_prefix)
                except ValueError:
                    pass
                if declared_path.is_absolute() or ".." in declared_path.parts:
                    errors.append(f"manifest task {task_id} has an unsafe target path")
                else:
                    target_relative = declared_path.as_posix()
                    context_relative = (
                        declared_path.parent / "context.md"
                    ).as_posix()
            required_declarations: list[str] | None = None
            target_theorem: str | None = None
            if isinstance(lean_target, Mapping):
                if tier == "T4":
                    raw_required = lean_target.get("required_declarations")
                    if (
                        not isinstance(raw_required, list)
                        or not raw_required
                        or any(
                            not isinstance(value, str) or not value
                            for value in raw_required
                        )
                        or "declaration" in lean_target
                    ):
                        errors.append(
                            f"manifest task {task_id} has invalid plural Lean identity"
                        )
                    else:
                        required_declarations = list(raw_required)
                elif isinstance(lean_target.get("declaration"), str):
                    target_theorem = lean_target.get("declaration")
            task_identity = {
                "paper_id": paper_id,
                "paper_sha256": paper_digest,
                "tier": tier,
                "target_file": target_relative,
                "context_file": context_relative,
                "target_theorem": target_theorem,
            }
            if tier == "T4":
                task_identity["required_declarations"] = required_declarations
            tasks[task_id] = task_identity
    return tasks


def _prompt_protocol(
    config: Mapping[str, Any], errors: list[str]
) -> Mapping[str, Any] | None:
    frozen = config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        return None
    raw = frozen.get("prompt_protocol")
    if raw is None:
        return None
    if not isinstance(raw, Mapping):
        errors.append("frozen prompt_protocol is not an object")
        return None
    if (
        raw.get("version") != SIGNPOSTED_PROMPT_PROTOCOL_VERSION
        or raw.get("composition_order") != SIGNPOSTED_PROMPT_COMPOSITION_ORDER
        or raw.get("N_receives_condition_supplement") is not False
        or raw.get("relevant_theorem_or_module_hints_supplied") is not False
    ):
        errors.append("frozen signposted prompt protocol has an invalid policy")
    common = raw.get("common_prompt")
    supplements = raw.get("condition_supplements")
    if (
        not isinstance(common, Mapping)
        or common.get("path") != "agent_prompt.md"
        or not _hex_digest(common.get("sha256"))
        or type(common.get("bytes")) is not int
        or common.get("bytes") <= 0
    ):
        errors.append("frozen signposted prompt protocol has an invalid common prompt")
    if not isinstance(supplements, Mapping) or set(supplements) != {"L"}:
        errors.append("frozen signposted prompt protocol must contain exactly one L supplement")
    else:
        supplement = supplements.get("L")
        if (
            not isinstance(supplement, Mapping)
            or supplement.get("path") != "condition_prompts/L.md"
            or not _hex_digest(supplement.get("sha256"))
            or type(supplement.get("bytes")) is not int
            or supplement.get("bytes") <= 0
        ):
            errors.append("frozen signposted prompt protocol has an invalid L supplement")
    return raw


def _source_descriptor(
    benchmark_root: Path,
    relative: str,
    expected: Mapping[str, Any],
    errors: list[str],
    *,
    label: str,
) -> tuple[dict[str, Any] | None, str | None]:
    relative_path = PurePosixPath(relative)
    if relative_path.is_absolute() or ".." in relative_path.parts:
        errors.append(f"{label} has an unsafe path")
        return None, None
    path = benchmark_root / relative_path
    if path.is_symlink() or not path.is_file():
        errors.append(f"{label} is missing or is a symlink: {path}")
        return None, None
    descriptor = {
        "path": relative,
        "sha256": sha256_file(path),
        "bytes": path.stat().st_size,
    }
    if descriptor != dict(expected):
        errors.append(f"{label} does not match its authenticated descriptor")
        return None, None
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        errors.append(f"cannot read {label} as UTF-8: {error}")
        return None, None
    return descriptor, text


def _expected_prompt_provenance(
    config: Mapping[str, Any],
    tasks: Mapping[str, Mapping[str, Any]],
    *,
    repository_root: Path | None,
    errors: list[str],
) -> tuple[
    Mapping[str, Any] | None,
    dict[tuple[str, str], dict[str, Any]],
    dict[tuple[str, str], str],
    Path | None,
]:
    protocol = _prompt_protocol(config, errors)
    if protocol is None:
        return None, {}, {}, None
    if repository_root is None:
        errors.append(
            "signposted prompt provenance requires repository_root for byte authentication"
        )
        return protocol, {}, {}, None
    benchmark_root = (
        repository_root.resolve() / "paper_bencmark" / "highambench"
    )
    common = protocol.get("common_prompt")
    supplements = protocol.get("condition_supplements")
    if not isinstance(common, Mapping) or not isinstance(supplements, Mapping):
        return protocol, {}, {}, benchmark_root
    supplement = supplements.get("L")
    if not isinstance(supplement, Mapping):
        return protocol, {}, {}, benchmark_root
    common_descriptor, common_text = _source_descriptor(
        benchmark_root,
        str(common.get("path", "")),
        common,
        errors,
        label="common prompt",
    )
    supplement_descriptor, supplement_text = _source_descriptor(
        benchmark_root,
        str(supplement.get("path", "")),
        supplement,
        errors,
        label="condition-L prompt supplement",
    )
    if (
        common_descriptor is None
        or common_text is None
        or supplement_descriptor is None
        or supplement_text is None
    ):
        return protocol, {}, {}, benchmark_root

    expected: dict[tuple[str, str], dict[str, Any]] = {}
    effective_prompt_texts: dict[tuple[str, str], str] = {}
    for task_id, task in tasks.items():
        target_relative = task.get("target_file")
        context_relative = task.get("context_file")
        if not isinstance(target_relative, str) or not isinstance(context_relative, str):
            errors.append(f"task {task_id} has no paths for prompt authentication")
            continue
        manifest_path = benchmark_root / "metadata" / "controlled" / f"{task_id}.json"
        try:
            controlled = read_json(manifest_path)
        except BenchmarkToolError as error:
            errors.append(str(error))
            continue
        files = controlled.get("files") if isinstance(controlled, Mapping) else None
        if not isinstance(files, list):
            errors.append(f"controlled manifest for {task_id} has no files")
            continue
        entries = {
            str(item.get("path")): item
            for item in files
            if isinstance(item, Mapping) and isinstance(item.get("path"), str)
        }
        task_sources: dict[str, tuple[dict[str, Any], str]] = {}
        for role, relative in (
            ("task_context", context_relative),
            ("fixed_target", target_relative),
        ):
            entry = entries.get(relative)
            if not isinstance(entry, Mapping):
                errors.append(
                    f"controlled manifest for {task_id} omits prompt source {relative}"
                )
                break
            descriptor, text = _source_descriptor(
                benchmark_root,
                relative,
                entry,
                errors,
                label=f"{task_id} {role}",
            )
            if descriptor is None or text is None:
                break
            task_sources[role] = (descriptor, text)
        if set(task_sources) != {"task_context", "fixed_target"}:
            continue
        context_descriptor, context_text = task_sources["task_context"]
        target_descriptor, target_text = task_sources["fixed_target"]
        for condition in ("N", "L"):
            sections = [common_text.rstrip()]
            selected_supplement: dict[str, Any] | None = None
            if condition == "L":
                sections.append(supplement_text.rstrip())
                selected_supplement = supplement_descriptor
            sections.extend(
                (
                    "## Task context\n\n" + context_text.rstrip(),
                    "## Fixed Lean target\n\n```lean\n"
                    + target_text.rstrip()
                    + "\n```",
                )
            )
            payload = ("\n\n".join(sections) + "\n").encode("utf-8")
            effective_prompt_texts[(task_id, condition)] = payload.decode("utf-8")
            expected[(task_id, condition)] = {
                "protocol_version": SIGNPOSTED_PROMPT_PROTOCOL_VERSION,
                "condition": condition,
                "composition_order": list(SIGNPOSTED_PROMPT_COMPOSITION_ORDER),
                "common_prompt": common_descriptor,
                "condition_supplement": selected_supplement,
                "task_context": context_descriptor,
                "fixed_target": target_descriptor,
                "effective_prompt": {
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "bytes": len(payload),
                    "encoding": "utf-8",
                    "composition": EFFECTIVE_PROMPT_COMPOSITION,
                },
                "authentication": {
                    "computed_before_prompt_release": True,
                    "frozen_protocol_match": True,
                    "controlled_task_sources_match": True,
                    "agent_command_match": True,
                },
            }
    return protocol, expected, effective_prompt_texts, benchmark_root


def _argv_option(command: Sequence[Any], option: str) -> tuple[int, str | None]:
    positions = [index for index, item in enumerate(command) if item == option]
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        return len(positions), None
    value = command[positions[0] + 1]
    return 1, value if isinstance(value, str) else None


def _check_prompt_provenance(
    run: Mapping[str, Any],
    expected: Mapping[str, Any] | None,
    *,
    protocol: Mapping[str, Any] | None,
    benchmark_root: Path | None,
    errors: list[str],
) -> bool:
    label = str(run.get("run_id"))
    if protocol is None:
        return True
    provenance = run.get("prompt_provenance")
    if not isinstance(provenance, Mapping):
        errors.append(f"final run {label} lacks signposted prompt provenance")
        return False
    if expected is None or dict(provenance) != dict(expected):
        errors.append(f"final run {label} has wrong effective-prompt provenance")
        return False
    command = run.get("agent_command")
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        errors.append(f"final run {label} has no auditable agent command for its prompt")
        return False
    count, condition = _argv_option(command, "--condition")
    if count != 1 or condition != run.get("condition"):
        errors.append(f"final run {label} agent command has the wrong prompt condition")
        return False
    file_count, condition_file = _argv_option(command, "--condition-prompt-file")
    digest_count, condition_digest = _argv_option(
        command, "--condition-prompt-sha256"
    )
    if run.get("condition") == "N":
        if file_count != 0 or digest_count != 0:
            errors.append(f"condition-N run {label} received L-only prompt arguments")
            return False
    else:
        raw_supplements = protocol.get("condition_supplements")
        supplement = (
            raw_supplements.get("L")
            if isinstance(raw_supplements, Mapping)
            else None
        )
        expected_path = (
            benchmark_root / str(supplement.get("path"))
            if benchmark_root is not None and isinstance(supplement, Mapping)
            else None
        )
        if (
            file_count != 1
            or digest_count != 1
            or expected_path is None
            or condition_file is None
            or Path(condition_file).resolve() != expected_path.resolve()
            or condition_digest != supplement.get("sha256")
        ):
            errors.append(f"condition-L run {label} agent command used the wrong supplement")
            return False
    return True


def _repetitions(config: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    repetitions = config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        errors.append("config has no repetitions")
        return result
    for repetition in repetitions:
        if not isinstance(repetition, Mapping) or not isinstance(repetition.get("id"), str):
            errors.append("config contains an invalid repetition entry")
            continue
        repetition_id = repetition["id"]
        if repetition_id in result:
            errors.append(f"config repeats repetition {repetition_id}")
            continue
        result[repetition_id] = repetition.get("backend_seed")
    return result


def _expected_assignments(
    run_order: Mapping[str, Any],
    tasks: Mapping[str, Mapping[str, Any]],
    repetitions: Mapping[str, Any],
    errors: list[str],
) -> tuple[dict[AssignmentKey, dict[str, Any]], dict[str, dict[str, Any]]]:
    expected: dict[AssignmentKey, dict[str, Any]] = {}
    pairs_by_id: dict[str, dict[str, Any]] = {}
    planned_run_ids: set[str] = set()
    pairs = run_order.get("pairs")
    if not isinstance(pairs, list):
        errors.append("run-order document has no pairs list")
        return expected, pairs_by_id
    method = run_order.get("method")
    salt = method.get("salt") if isinstance(method, Mapping) else None
    method_name = method.get("name") if isinstance(method, Mapping) else None
    if method_name != "sha256_first_byte_parity" or not isinstance(salt, str) or not salt:
        errors.append(
            "run-order method must be sha256_first_byte_parity with a nonempty salt"
        )
    for pair in pairs:
        if not isinstance(pair, Mapping):
            errors.append("run-order contains a non-object pair")
            continue
        pair_id = pair.get("pair_id")
        task_id = pair.get("task_id")
        repetition_id = pair.get("repetition_id")
        order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if not all(isinstance(value, str) for value in (pair_id, task_id, repetition_id)):
            errors.append(f"run-order contains an invalid pair identity: {pair!r}")
            continue
        if pair_id in pairs_by_id:
            errors.append(f"run-order repeats pair {pair_id}")
            continue
        identity_is_known = True
        if task_id not in tasks:
            errors.append(f"run-order pair {pair_id} names unknown task {task_id}")
            identity_is_known = False
        if repetition_id not in repetitions:
            errors.append(f"run-order pair {pair_id} names unknown repetition {repetition_id}")
            identity_is_known = False
        if order not in (["N", "L"], ["L", "N"]):
            errors.append(f"run-order pair {pair_id} does not contain one N and one L in order")
            continue
        if not isinstance(run_ids, list) or len(run_ids) != 2 or not all(
            isinstance(run_id, str) and run_id for run_id in run_ids
        ):
            errors.append(f"run-order pair {pair_id} has invalid run_ids")
            continue
        if len(set(run_ids)) != 2:
            errors.append(f"run-order pair {pair_id} repeats a run id")
        for run_id in run_ids:
            if run_id in planned_run_ids:
                errors.append(f"run-order repeats planned run id {run_id}")
            planned_run_ids.add(run_id)
        digest = pair.get("sha256")
        if method_name == "sha256_first_byte_parity" and isinstance(salt, str):
            key = f"{salt}|{task_id}|{repetition_id}"
            actual_digest = hashlib.sha256(key.encode("utf-8")).hexdigest()
            actual_order = ["N", "L"] if int(actual_digest[:2], 16) % 2 == 0 else ["L", "N"]
            if digest != actual_digest:
                errors.append(f"run-order pair {pair_id} has the wrong SHA-256")
            if order != actual_order:
                errors.append(f"run-order pair {pair_id} does not follow its SHA-256 order rule")
        pair_order = "N-first" if order[0] == "N" else "L-first"
        pair_record = {
            "pair_id": pair_id,
            "task_id": task_id,
            "repetition_id": repetition_id,
            "condition_order": list(order),
            "run_ids": list(run_ids),
            "pair_order": pair_order,
        }
        pairs_by_id[pair_id] = pair_record
        if not identity_is_known:
            continue
        for index, condition in enumerate(order):
            assignment = (task_id, repetition_id, condition)
            if assignment in expected:
                errors.append(
                    f"run-order repeats assignment {task_id}/{repetition_id}/{condition}"
                )
                continue
            expected[assignment] = {
                **pair_record,
                "condition": condition,
                "run_id": run_ids[index],
                "order_index": index + 1,
                "backend_seed": repetitions.get(repetition_id),
            }
    matrix = {
        (task_id, repetition_id, condition)
        for task_id in tasks
        for repetition_id in repetitions
        for condition in ("N", "L")
    }
    missing = sorted(matrix - set(expected))
    extra = sorted(set(expected) - matrix)
    for assignment in missing:
        errors.append("run-order misses assignment " + "/".join(assignment))
    for assignment in extra:
        errors.append("run-order has extra assignment " + "/".join(assignment))
    return expected, pairs_by_id


def _metadata_readiness(
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
    *,
    repository_root: Path | None,
    allow_observational_unscored: bool,
) -> tuple[list[str], list[str], list[dict[str, Any]], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    verified_hashes: list[dict[str, Any]] = []
    nonreference_reasons: list[str] = []
    if repository_root is None:
        nonreference_reasons.append(
            "the repository root was not supplied, so both live canaries and their "
            "production prompt/execution freeze bindings were not reauthenticated"
        )
    frozen = config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        errors.append("config has no frozen_environment object")
        frozen = {}
    for field in (
        "lean_toolchain",
        "lean_commit",
        "lean_binary_sha256",
        "mathlib_commit",
        "numstability_commit",
        "agent_id",
        "agent_version",
        "agent_binary_sha256",
        "model_version",
        "model_reasoning_effort",
        "prompt_sha256",
        "allowed_tools",
        "hardware_class",
        "operating_system",
        "environment_id",
        "environment_bundle_sha256",
        "bubblewrap_binary_sha256",
        "bubblewrap_version",
        "numstability_source_manifest",
        "numstability_source_manifest_sha256",
        "numstability_compiled_manifest",
        "numstability_compiled_manifest_sha256",
        "compiled_environment_summary",
        "compiled_environment_summary_sha256",
        "packages_runtime_manifest",
        "packages_runtime_manifest_sha256",
        "python_version",
        "python_binary_sha256",
        "release_manifest",
        "release_manifest_sha256",
        "token_control_canary",
        "ultra_orchestration_canary",
    ):
        value = frozen.get(field)
        if value is None or value == "" or value == []:
            errors.append(f"frozen environment field {field} is not fixed")
    container_digest = frozen.get("container_image_digest")
    bubblewrap_recorded = _contains_text(config.get("isolation"), "bubblewrap")
    if container_digest is None or container_digest == "":
        if bubblewrap_recorded:
            reason = (
                "no frozen OCI/container image digest; runs use recorded bubblewrap namespace "
                "isolation (the model shell is offline while the Codex control process keeps "
                "its provider connection)"
            )
            nonreference_reasons.append(reason)
            if not allow_observational_unscored:
                errors.append(reason)
        else:
            errors.append(
                "frozen environment has neither a container image digest nor an explicit "
                "bubblewrap isolation record"
            )
    for field in (
        "prompt_sha256",
        "agent_binary_sha256",
        "environment_bundle_sha256",
        "lean_binary_sha256",
        "bubblewrap_binary_sha256",
        "numstability_source_manifest_sha256",
        "numstability_compiled_manifest_sha256",
        "compiled_environment_summary_sha256",
        "packages_runtime_manifest_sha256",
        "python_binary_sha256",
        "release_manifest_sha256",
    ):
        digest = frozen.get(field)
        if digest is not None and not _hex_digest(digest):
            errors.append(f"frozen {field} is not a lowercase SHA-256")
    environment_id = frozen.get("environment_id")
    bundle_digest = frozen.get("environment_bundle_sha256")
    expected_environment_id = (
        _expected_environment_id(manifest, bundle_digest)
        if _hex_digest(bundle_digest)
        else None
    )
    if (
        isinstance(environment_id, str)
        and expected_environment_id is not None
        and environment_id != expected_environment_id
    ):
        errors.append(
            "frozen environment_id is not derived from the ordered manifest paper IDs "
            "and environment_bundle_sha256; "
            f"expected {expected_environment_id!r}"
        )
    for field in ("mathlib_commit", "numstability_commit"):
        commit = frozen.get(field)
        if commit is not None and (
            not isinstance(commit, str)
            or len(commit) != 40
            or any(character not in "0123456789abcdef" for character in commit)
        ):
            errors.append(f"frozen {field} is not a full lowercase Git commit hash")

    current_python_version = platform.python_version()
    frozen_python_version = frozen.get("python_version")
    if frozen_python_version != current_python_version:
        errors.append(
            f"current Python version {current_python_version!r} does not match "
            f"frozen {frozen_python_version!r}"
        )
    python_path = Path(sys.executable).resolve()
    python_record: dict[str, Any] = {
        "label": "current Python executable",
        "path": "<current sys.executable>",
        "expected_sha256": frozen.get("python_binary_sha256"),
    }
    if not python_path.is_file():
        errors.append("current sys.executable is not a readable regular file")
        python_record["match"] = False
    else:
        actual_python_digest = sha256_file(python_path)
        python_record["actual_sha256"] = actual_python_digest
        python_record["match"] = actual_python_digest == frozen.get(
            "python_binary_sha256"
        )
        if python_record["match"] is not True:
            errors.append("current Python executable does not match its frozen SHA-256")
    verified_hashes.append(python_record)

    hash_records: list[tuple[str, Any, Any]] = []
    hash_records.extend(
        [
            (
                "NumStability source manifest",
                frozen.get("numstability_source_manifest"),
                frozen.get("numstability_source_manifest_sha256"),
            ),
            (
                "NumStability compiled manifest",
                frozen.get("numstability_compiled_manifest"),
                frozen.get("numstability_compiled_manifest_sha256"),
            ),
            (
                "compiled environment summary",
                frozen.get("compiled_environment_summary"),
                frozen.get("compiled_environment_summary_sha256"),
            ),
            (
                "packages runtime manifest",
                frozen.get("packages_runtime_manifest"),
                frozen.get("packages_runtime_manifest_sha256"),
            ),
            (
                "evaluation release manifest",
                frozen.get("release_manifest"),
                frozen.get("release_manifest_sha256"),
            ),
        ]
    )
    canary_descriptor = frozen.get("token_control_canary")
    if not _valid_token_canary_descriptor(canary_descriptor):
        errors.append("frozen token-control canary descriptor is invalid")
    elif isinstance(canary_descriptor, Mapping):
        hash_records.append(
            (
                "token-control canary evidence",
                canary_descriptor.get("path"),
                canary_descriptor.get("sha256"),
            )
        )
    ultra_canary_descriptor = frozen.get("ultra_orchestration_canary")
    if not _valid_ultra_canary_descriptor(ultra_canary_descriptor):
        errors.append("frozen Ultra orchestration canary descriptor is invalid")
    elif isinstance(ultra_canary_descriptor, Mapping):
        hash_records.append(
            (
                "Ultra orchestration canary evidence",
                ultra_canary_descriptor.get("path"),
                ultra_canary_descriptor.get("sha256"),
            )
        )
    specification = manifest.get("specification")
    if isinstance(specification, Mapping):
        hash_records.append(
            ("specification", specification.get("local_path"), specification.get("sha256"))
        )
    else:
        errors.append("manifest has no specification object")
    target_count = 0
    for paper in manifest.get("papers", []) if isinstance(manifest.get("papers"), list) else []:
        if not isinstance(paper, Mapping):
            continue
        source = paper.get("source")
        if isinstance(source, Mapping):
            hash_records.append(
                (f"paper {paper.get('paper_id')}", source.get("local_path"), source.get("sha256"))
            )
        for target in paper.get("targets", []) if isinstance(paper.get("targets"), list) else []:
            if not isinstance(target, Mapping):
                continue
            target_count += 1
            lean_target = target.get("lean_target")
            if isinstance(lean_target, Mapping):
                hash_records.append(
                    (
                        f"target {target.get('task_id')}",
                        lean_target.get("file"),
                        lean_target.get("controlled_file_sha256"),
                    )
                )
            else:
                errors.append(f"target {target.get('task_id')} has no lean_target object")
    shared = manifest.get("controlled_shared_files")
    if isinstance(shared, list) and shared:
        for entry in shared:
            if isinstance(entry, Mapping):
                hash_records.append(
                    (f"shared file {entry.get('path')}", entry.get("path"), entry.get("sha256"))
                )
            else:
                errors.append("manifest contains a non-object controlled shared file")
    else:
        errors.append("manifest has no controlled_shared_files entries")
    if target_count == 0:
        errors.append("manifest has no controlled target files")
    for label, raw_path, digest in hash_records:
        if not isinstance(raw_path, str) or not raw_path:
            errors.append(f"{label} has no fixed file path")
        if not _hex_digest(digest):
            errors.append(f"{label} has no fixed lowercase SHA-256")
            continue
        record = {"label": label, "path": raw_path, "expected_sha256": digest}
        if repository_root is not None and isinstance(raw_path, str):
            path = (repository_root / raw_path).resolve()
            try:
                path.relative_to(repository_root.resolve())
            except ValueError:
                errors.append(f"{label} path escapes repository root: {raw_path}")
                continue
            if not path.is_file():
                errors.append(f"{label} file is missing: {raw_path}")
                continue
            actual = sha256_file(path)
            record["actual_sha256"] = actual
            record["match"] = actual == digest
            if actual != digest:
                errors.append(f"{label} does not match its recorded SHA-256")
        else:
            record["match"] = None
            if repository_root is None:
                warnings.append(f"{label} hash syntax checked but file content was not re-read")
        verified_hashes.append(record)
    return errors, warnings, verified_hashes, nonreference_reasons


def _check_planned_metadata(
    run: Mapping[str, Any],
    expected: Mapping[str, Any],
    task: Mapping[str, Any],
    errors: list[str],
    *,
    require_planned_run_id: bool,
) -> None:
    label = str(run.get("run_id") or expected["run_id"])
    exact = {
        "pair_id": expected["pair_id"],
        "task_id": expected["task_id"],
        "paper_id": task["paper_id"],
        "paper_sha256": task["paper_sha256"],
        "tier": task["tier"],
        "condition": expected["condition"],
        "repetition_id": expected["repetition_id"],
        "backend_seed": expected["backend_seed"],
        "pair_order": expected["pair_order"],
        "order_index": expected["order_index"],
    }
    if require_planned_run_id:
        exact["run_id"] = expected["run_id"]
    for field, wanted in exact.items():
        if run.get(field) != wanted:
            errors.append(
                f"run {label} has {field}={run.get(field)!r}; expected {wanted!r}"
            )


def _check_frozen_run_evidence(
    runs: Sequence[Mapping[str, Any]],
    *,
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
    run_order: Mapping[str, Any],
    repository_root: Path | None,
    errors: list[str],
    warnings: list[str],
) -> tuple[str | None, bool]:
    frozen = config.get("frozen_environment")
    frozen = frozen if isinstance(frozen, Mapping) else {}
    limits_record = config.get("limits")
    expected_token_limit = (
        limits_record.get("total_model_tokens")
        if isinstance(limits_record, Mapping)
        else None
    )
    configured_token_control = config.get("token_control")
    if not _valid_token_control(configured_token_control, expected_token_limit):
        errors.append("config has invalid live token-control metadata")
    canary_descriptor = frozen.get("token_control_canary")
    if not _valid_token_canary_descriptor(canary_descriptor):
        errors.append("config has invalid token-control canary descriptor")
    ultra_canary_descriptor = frozen.get("ultra_orchestration_canary")
    if not _valid_ultra_canary_descriptor(ultra_canary_descriptor):
        errors.append("config has invalid Ultra orchestration canary descriptor")
    expected_metadata = {
        "config": _document_digest(config),
        "manifest": _document_digest(manifest),
        "run_order": _document_digest(run_order),
    }
    configured_prompt_protocol = frozen.get("prompt_protocol")
    hardware_matching_policy = frozen.get("hardware_matching_policy")
    environment: Mapping[str, Any] | None = None
    expected_release_file_count: int | None = None
    expected_source_file_count: int | None = None
    expected_compiled_file_count: int | None = None
    expected_runtime_file_count: int | None = None
    expected_runtime_counts: dict[str, int] | None = None
    expected_compiled_counts: dict[str, int] | None = None
    expected_canary_summary: dict[str, Any] | None = None
    expected_ultra_canary_summary: dict[str, Any] | None = None
    production_prompt_protocol: dict[str, Any] | None = None
    production_execution_components: dict[str, str] | None = None
    if repository_root is not None:
        environment_path = (
            repository_root.resolve()
            / "paper_bencmark"
            / "highambench"
            / "metadata"
            / "environment.json"
        )
        if not environment_path.is_file():
            errors.append(f"frozen environment record is missing: {environment_path}")
        else:
            try:
                raw_environment = read_json(environment_path)
            except BenchmarkToolError as error:
                errors.append(str(error))
                raw_environment = None
            if not isinstance(raw_environment, Mapping):
                errors.append("frozen environment record is not a JSON object")
            else:
                environment = raw_environment
                expected_metadata["environment"] = _document_digest(environment)
                if hardware_matching_policy is not None and (
                    hardware_matching_policy
                    != getattr(run_matrix, "HARDWARE_MATCHING_POLICY", None)
                    or environment.get("hardware_matching_policy")
                    != hardware_matching_policy
                ):
                    errors.append(
                        "paired-hardware policy disagrees across frozen metadata"
                    )
                if environment.get("environment_bundle_definition") != ENVIRONMENT_BUNDLE_DEFINITION:
                    errors.append("environment record names the wrong canonical bundle algorithm")
                bundle = _environment_bundle_digest(config, environment)
                if bundle != frozen.get("environment_bundle_sha256"):
                    errors.append("current config/environment canonical bundle digest is stale")
                if environment.get("environment_bundle_sha256") != bundle:
                    errors.append("environment record stores the wrong canonical bundle digest")
                if environment.get("environment_id") != frozen.get("environment_id"):
                    errors.append("environment_id disagrees between config and environment record")
                if environment.get("release_manifest_sha256") != frozen.get(
                    "release_manifest_sha256"
                ):
                    errors.append("release manifest SHA-256 disagrees across frozen metadata")
                if environment.get("token_control") != configured_token_control:
                    errors.append(
                        "token-control metadata disagrees between config and environment record"
                    )
                if environment.get("token_control_canary") != canary_descriptor:
                    errors.append(
                        "token-control canary descriptor disagrees between config and "
                        "environment record"
                    )
                if (
                    environment.get("ultra_orchestration_canary")
                    != ultra_canary_descriptor
                ):
                    errors.append(
                        "Ultra orchestration canary descriptor disagrees between "
                        "config and environment record"
                    )
                environment_agent = environment.get("agent")
                if configured_prompt_protocol is not None and (
                    not isinstance(environment_agent, Mapping)
                    or environment_agent.get("prompt_protocol")
                    != configured_prompt_protocol
                ):
                    errors.append(
                        "prompt protocol disagrees between config and environment record"
                    )
                runtime_record = environment.get("runtime")
                python_record = (
                    runtime_record.get("python")
                    if isinstance(runtime_record, Mapping)
                    else None
                )
                if not isinstance(python_record, Mapping) or (
                    python_record.get("version") != frozen.get("python_version")
                    or python_record.get("binary_sha256")
                    != frozen.get("python_binary_sha256")
                ):
                    errors.append("Python identity disagrees across frozen metadata")
                if not isinstance(runtime_record, Mapping) or (
                    runtime_record.get("packages_runtime_manifest")
                    != frozen.get("packages_runtime_manifest")
                    or runtime_record.get("packages_runtime_manifest_sha256")
                    != frozen.get("packages_runtime_manifest_sha256")
                ):
                    errors.append(
                        "packages runtime manifest disagrees across frozen metadata"
                    )
                try:
                    (
                        production_prompt_protocol,
                        production_execution_components,
                    ) = run_matrix.production_freeze_bindings(config, environment)
                except BenchmarkToolError as error:
                    errors.append(
                        "production prompt/execution freeze bindings are invalid: "
                        f"{error}"
                    )
        if (
            isinstance(canary_descriptor, Mapping)
            and _valid_token_canary_descriptor(canary_descriptor)
            and isinstance(expected_token_limit, int)
            and not isinstance(expected_token_limit, bool)
            and expected_token_limit > 0
            and production_prompt_protocol is not None
            and production_execution_components is not None
        ):
            expected_canary_summary = _authenticated_token_canary_summary(
                repository_root,
                canary_descriptor,
                config=config,
                frozen=frozen,
                token_limit=expected_token_limit,
                prompt_protocol=production_prompt_protocol,
                execution_components=production_execution_components,
                errors=errors,
            )
        if (
            isinstance(ultra_canary_descriptor, Mapping)
            and _valid_ultra_canary_descriptor(ultra_canary_descriptor)
            and isinstance(expected_token_limit, int)
            and not isinstance(expected_token_limit, bool)
            and expected_token_limit > 0
            and production_prompt_protocol is not None
            and production_execution_components is not None
        ):
            expected_ultra_canary_summary = _authenticated_ultra_canary_summary(
                repository_root,
                ultra_canary_descriptor,
                config=config,
                frozen=frozen,
                token_limit=expected_token_limit,
                prompt_protocol=production_prompt_protocol,
                execution_components=production_execution_components,
                errors=errors,
            )
        for field, count_name in (
            ("release_manifest", "release"),
            ("numstability_source_manifest", "source"),
            ("numstability_compiled_manifest", "compiled"),
            ("packages_runtime_manifest", "runtime"),
        ):
            raw_path = frozen.get(field)
            if not isinstance(raw_path, str):
                continue
            path = (repository_root.resolve() / raw_path).resolve()
            try:
                path.relative_to(repository_root.resolve())
            except ValueError:
                continue
            if not path.is_file():
                continue
            try:
                value = read_json(path)
            except BenchmarkToolError as error:
                errors.append(str(error))
                continue
            files = value.get("files") if isinstance(value, Mapping) else None
            if not isinstance(files, list):
                continue
            if count_name == "release":
                expected_release_file_count = len(files)
            elif count_name == "source":
                expected_source_file_count = len(files)
            elif count_name == "compiled":
                expected_compiled_file_count = len(files)
            else:
                expected_runtime_file_count = len(files)
                counts = {"source": 0, "olean": 0, "compiled_support": 0}
                invalid_paths: list[str] = []
                for entry in files:
                    relative = entry.get("path") if isinstance(entry, Mapping) else None
                    kind = (
                        _package_runtime_file_kind(relative)
                        if isinstance(relative, str)
                        else None
                    )
                    if kind is None:
                        invalid_paths.append(str(relative))
                    else:
                        counts[kind] += 1
                if invalid_paths:
                    errors.append(
                        "packages runtime manifest contains files outside its exact "
                        "source/compiled projection: " + ", ".join(invalid_paths[:8])
                    )
                else:
                    expected_runtime_counts = counts
        compiled_path_raw = frozen.get("compiled_environment_summary")
        if isinstance(compiled_path_raw, str):
            compiled_path = (repository_root.resolve() / compiled_path_raw).resolve()
            if compiled_path.is_file():
                try:
                    compiled_value = read_json(compiled_path)
                except BenchmarkToolError as error:
                    errors.append(str(error))
                    compiled_value = None
                toolchain = (
                    compiled_value.get("toolchain")
                    if isinstance(compiled_value, Mapping)
                    else None
                )
                packages = (
                    compiled_value.get("packages")
                    if isinstance(compiled_value, Mapping)
                    else None
                )
                if (
                    isinstance(toolchain, Mapping)
                    and isinstance(toolchain.get("file_count"), int)
                    and isinstance(packages, list)
                    and all(
                        isinstance(item, Mapping)
                        and isinstance(item.get("file_count"), int)
                        for item in packages
                    )
                ):
                    expected_compiled_counts = {
                        "toolchain_file_count": toolchain.get("file_count"),
                        "package_count": len(packages),
                        "package_file_count": sum(
                            item.get("file_count", 0) for item in packages
                        ),
                    }
    else:
        warnings.append(
            "freeze evidence syntax was checked, but environment.json was not re-read "
            "because no repository root was supplied"
        )

    evidence_digests: set[str] = set()
    reference_policy_freeze: Mapping[str, Any] | None = None
    for index, run in enumerate(runs):
        label = str(run.get("run_id") or f"input record {index}")
        wrapper = run.get("frozen_run_verification")
        if not isinstance(wrapper, Mapping):
            errors.append(f"run {label} lacks mandatory frozen-run verification evidence")
            continue
        check = wrapper.get("freeze_check")
        recorded_digest = wrapper.get("freeze_check_sha256")
        if not isinstance(check, Mapping):
            errors.append(f"run {label} has no embedded freeze_check object")
            continue
        actual_digest = _document_digest(check)
        if recorded_digest != actual_digest:
            errors.append(f"run {label} has a stale or altered freeze_check digest")
        else:
            evidence_digests.add(actual_digest)
        if (
            check.get("schema_version") != SCHEMA_VERSION
            or check.get("kind") != "highambench-frozen-run-verification"
            or check.get("ok") is not True
        ):
            errors.append(f"run {label} does not cite a successful supported freeze check")
        elif hardware_matching_policy is not None:
            if environment is not None:
                metadata_reference = json.loads(json.dumps(check))
                metadata_reference["host_class"] = json.loads(
                    json.dumps(environment.get("host_class"))
                )
                metadata_reference["provider_token_gate"] = json.loads(
                    json.dumps(environment.get("provider_token_gate"))
                )
                try:
                    run_matrix.verify_pair_policy_compatible_freeze_checks(
                        metadata_reference, check
                    )
                except BenchmarkToolError as error:
                    errors.append(
                        f"run {label} freeze check violates current paired-hardware "
                        f"metadata: {error}"
                    )
            if reference_policy_freeze is None:
                reference_policy_freeze = check
            else:
                try:
                    run_matrix.verify_pair_policy_compatible_freeze_checks(
                        reference_policy_freeze, check
                    )
                except BenchmarkToolError as error:
                    errors.append(
                        f"run {label} freeze check differs outside the paired-hardware "
                        f"allowlist: {error}"
                    )
        for field, wanted in (
            ("benchmark_id", config.get("benchmark_id")),
            ("environment_id", frozen.get("environment_id")),
            ("environment_bundle_sha256", frozen.get("environment_bundle_sha256")),
        ):
            if check.get(field) != wanted:
                errors.append(f"run {label} freeze check has the wrong {field}")
        release = check.get("release_manifest")
        if not isinstance(release, Mapping) or release.get("sha256") != frozen.get(
            "release_manifest_sha256"
        ):
            errors.append(f"run {label} freeze check has the wrong release manifest identity")
        elif (
            not isinstance(release.get("file_count"), int)
            or release.get("file_count") <= 0
            or not isinstance(release.get("verification"), Mapping)
            or release["verification"].get("ok") is not True
            or release["verification"].get("verified")
            != release["verification"].get("expected")
            or release["verification"].get("missing") != []
            or release["verification"].get("changed") != []
        ):
            errors.append(f"run {label} freeze check lacks a complete release verification")
        elif (
            expected_release_file_count is not None
            and (
                release.get("file_count") != expected_release_file_count
                or release["verification"].get("expected") != expected_release_file_count
            )
        ):
            errors.append(f"run {label} freeze check has the wrong release file count")

        agent = check.get("agent")
        expected_agent = {
            "id": frozen.get("agent_id"),
            "version": frozen.get("agent_version"),
            "binary_sha256": frozen.get("agent_binary_sha256"),
            "model": frozen.get("model_version"),
            "reasoning_effort": frozen.get("model_reasoning_effort"),
            "ultra_orchestration": frozen.get("ultra_orchestration"),
        }
        if not isinstance(agent, Mapping) or any(
            agent.get(field) != wanted for field, wanted in expected_agent.items()
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong agent identity")

        python_check = check.get("python")
        if not isinstance(python_check, Mapping) or (
            python_check.get("version") != frozen.get("python_version")
            or python_check.get("binary_sha256")
            != frozen.get("python_binary_sha256")
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong Python identity")

        token_control = check.get("token_control")
        if (
            token_control != configured_token_control
            or not _valid_token_control(token_control, expected_token_limit)
        ):
            errors.append(f"run {label} freeze check has invalid token-control evidence")
        if production_prompt_protocol is not None:
            if check.get("prompt_protocol") != production_prompt_protocol:
                errors.append(f"run {label} freeze check has the wrong prompt protocol")
            if check.get("execution_components") != production_execution_components:
                errors.append(
                    f"run {label} freeze check has the wrong execution components"
                )
        elif configured_prompt_protocol is None:
            if check.get("prompt_protocol") is not None:
                errors.append(
                    f"legacy run {label} freeze check unexpectedly cites a prompt protocol"
                )
        elif check.get("prompt_protocol") != configured_prompt_protocol:
            errors.append(f"run {label} freeze check has the wrong prompt protocol")
        canary_summary = check.get("token_control_canary")
        if not _valid_token_canary_summary(
            canary_summary, canary_descriptor, expected_token_limit
        ):
            errors.append(
                f"run {label} freeze check has invalid token-control canary summary"
            )
        elif (
            expected_canary_summary is not None
            and canary_summary != expected_canary_summary
        ):
            errors.append(
                f"run {label} freeze check has stale token-control canary summary"
            )
        ultra_canary_summary = check.get("ultra_orchestration_canary")
        if not _valid_ultra_canary_summary(
            ultra_canary_summary, ultra_canary_descriptor
        ):
            errors.append(
                f"run {label} freeze check has invalid Ultra orchestration canary summary"
            )
        elif (
            expected_ultra_canary_summary is not None
            and ultra_canary_summary != expected_ultra_canary_summary
        ):
            errors.append(
                f"run {label} freeze check has stale Ultra orchestration canary summary"
            )

        lean_check = check.get("lean")
        expected_lean_version = (
            str(frozen.get("lean_toolchain")).rsplit(":v", 1)[-1]
            if isinstance(frozen.get("lean_toolchain"), str)
            else None
        )
        expected_lean = {
            "version": expected_lean_version,
            "commit": frozen.get("lean_commit"),
            "binary_sha256": frozen.get("lean_binary_sha256"),
            "mathlib_commit": frozen.get("mathlib_commit"),
            "numstability_commit": frozen.get("numstability_commit"),
        }
        if not isinstance(lean_check, Mapping) or any(
            lean_check.get(field) != wanted for field, wanted in expected_lean.items()
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong Lean identity")
        elif any(
            not isinstance(lean_check.get(field), int)
            or isinstance(lean_check.get(field), bool)
            or lean_check.get(field) <= 0
            for field in ("compiled_files_verified", "source_files_verified")
        ):
            errors.append(f"run {label} freeze check has invalid library file counts")
        elif (
            expected_source_file_count is not None
            and lean_check.get("source_files_verified") != expected_source_file_count
        ) or (
            expected_compiled_file_count is not None
            and lean_check.get("compiled_files_verified") != expected_compiled_file_count
        ):
            errors.append(f"run {label} freeze check has stale library file counts")

        limits = config.get("limits")
        expected_limits = {
            "wall_clock_seconds": (
                limits.get("wall_clock_seconds") if isinstance(limits, Mapping) else None
            ),
            "total_model_tokens": (
                limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
            ),
        }
        if not isinstance(check.get("limits"), Mapping) or any(
            check["limits"].get(field) != wanted
            for field, wanted in expected_limits.items()
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong limits")

        bubblewrap = check.get("bubblewrap")
        if not isinstance(bubblewrap, Mapping) or (
            bubblewrap.get("version") != frozen.get("bubblewrap_version")
            or bubblewrap.get("binary_sha256") != frozen.get("bubblewrap_binary_sha256")
        ):
            errors.append(f"run {label} freeze check has incomplete or wrong bubblewrap identity")

        compiled = check.get("compiled_environment_summary")
        if not isinstance(compiled, Mapping) or (
            compiled.get("sha256") != frozen.get("compiled_environment_summary_sha256")
            or any(
                not isinstance(compiled.get(field), int)
                or isinstance(compiled.get(field), bool)
                or compiled.get(field) <= 0
                for field in (
                    "toolchain_file_count",
                    "package_count",
                    "package_file_count",
                )
            )
        ):
            errors.append(f"run {label} freeze check has invalid compiled-tree evidence")
        elif expected_compiled_counts is not None and any(
            compiled.get(field) != wanted
            for field, wanted in expected_compiled_counts.items()
        ):
            errors.append(f"run {label} freeze check has stale compiled-tree counts")

        packages_runtime = check.get("packages_runtime")
        if not isinstance(packages_runtime, Mapping) or (
            packages_runtime.get("path") != frozen.get("packages_runtime_manifest")
            or packages_runtime.get("sha256")
            != frozen.get("packages_runtime_manifest_sha256")
            or not isinstance(packages_runtime.get("file_count"), int)
            or isinstance(packages_runtime.get("file_count"), bool)
            or packages_runtime.get("file_count") <= 0
            or not isinstance(packages_runtime.get("source_file_count"), int)
            or isinstance(packages_runtime.get("source_file_count"), bool)
            or packages_runtime.get("source_file_count") <= 0
            or not isinstance(packages_runtime.get("olean_file_count"), int)
            or isinstance(packages_runtime.get("olean_file_count"), bool)
            or packages_runtime.get("olean_file_count") <= 0
            or not isinstance(
                packages_runtime.get("compiled_support_file_count"), int
            )
            or isinstance(
                packages_runtime.get("compiled_support_file_count"), bool
            )
            or packages_runtime.get("compiled_support_file_count") <= 0
            or packages_runtime.get("source_file_count")
            + packages_runtime.get("olean_file_count")
            + packages_runtime.get("compiled_support_file_count")
            != packages_runtime.get("file_count")
            or not isinstance(packages_runtime.get("verification"), Mapping)
            or packages_runtime["verification"].get("ok") is not True
            or packages_runtime["verification"].get("verified")
            != packages_runtime["verification"].get("expected")
            or packages_runtime["verification"].get("missing") != []
            or packages_runtime["verification"].get("changed") != []
        ):
            errors.append(f"run {label} freeze check has invalid packages-runtime evidence")
        elif expected_runtime_file_count is not None and (
            packages_runtime.get("file_count") != expected_runtime_file_count
            or packages_runtime["verification"].get("expected")
            != expected_runtime_file_count
            or (
                expected_runtime_counts is not None
                and (
                    packages_runtime.get("source_file_count")
                    != expected_runtime_counts["source"]
                    or packages_runtime.get("olean_file_count")
                    != expected_runtime_counts["olean"]
                    or packages_runtime.get("compiled_support_file_count")
                    != expected_runtime_counts["compiled_support"]
                )
            )
        ):
            errors.append(f"run {label} freeze check has stale packages-runtime counts")

        host = check.get("host_class")
        required_host_fields = (
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
        )
        if (
            not isinstance(host, Mapping)
            or set(host) != set(required_host_fields)
            or any(host.get(field) in (None, "") for field in required_host_fields)
        ):
            errors.append(f"run {label} freeze check has incomplete host evidence")
        elif hardware_matching_policy is not None and check.get(
            "hardware_matching_policy"
        ) != hardware_matching_policy:
            errors.append(f"run {label} freeze check has a stale paired-hardware policy")
        elif environment is not None:
            recorded_host = environment.get("host_class")
            if not isinstance(recorded_host, Mapping):
                errors.append(f"run {label} freeze check host disagrees with environment.json")
            elif hardware_matching_policy is None:
                if any(
                    host.get(field) != recorded_host.get(field)
                    for field in required_host_fields
                ):
                    errors.append(
                        f"run {label} freeze check host disagrees with environment.json"
                    )
            else:
                policy_host = hardware_matching_policy.get("frozen_host_class")
                exact_fields = (
                    policy_host.get("exact_fields")
                    if isinstance(policy_host, Mapping)
                    else None
                )
                if (
                    check.get("hardware_matching_policy")
                    != hardware_matching_policy
                    or not isinstance(exact_fields, list)
                    or any(
                        host.get(field) != recorded_host.get(field)
                        for field in exact_fields
                    )
                ):
                    errors.append(
                        f"run {label} freeze check violates paired-hardware invariants"
                    )
        metadata_digests = check.get("metadata_document_sha256")
        if not isinstance(metadata_digests, Mapping):
            errors.append(f"run {label} freeze check has no metadata document digests")
        else:
            for name, wanted in expected_metadata.items():
                if metadata_digests.get(name) != wanted:
                    errors.append(f"run {label} freeze check is stale for {name}")
    if len(evidence_digests) > 1 and hardware_matching_policy is None:
        errors.append("runs cite more than one frozen-run verification artifact")
    freeze_digest = (
        next(iter(evidence_digests))
        if len(evidence_digests) == 1
        else _document_digest({"freeze_check_sha256s": sorted(evidence_digests)})
        if evidence_digests and hardware_matching_policy is not None
        else None
    )
    both_canaries_bound = bool(
        repository_root is not None
        and production_prompt_protocol is not None
        and production_execution_components is not None
        and expected_canary_summary is not None
        and expected_ultra_canary_summary is not None
    )
    return freeze_digest, both_canaries_bound


def _check_limits(
    run: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
    *,
    final_record: bool,
) -> None:
    label = str(run.get("run_id"))
    limits = config.get("limits")
    run_limits = run.get("limits")
    if not isinstance(limits, Mapping) or not isinstance(run_limits, Mapping):
        errors.append(f"run {label} or config lacks limits")
        return
    wall_limit = limits.get("wall_clock_seconds")
    token_limit = limits.get("total_model_tokens")
    if run_limits.get("time_seconds") != wall_limit:
        errors.append(f"run {label} has the wrong wall-clock limit")
    if run_limits.get("model_tokens") != token_limit:
        errors.append(f"run {label} has the wrong model-token limit")
    elapsed = run.get("scored_elapsed_seconds")
    if not isinstance(elapsed, (int, float)) or isinstance(elapsed, bool) or elapsed < 0:
        errors.append(f"run {label} has invalid scored elapsed time")
    elif isinstance(wall_limit, (int, float)) and elapsed > wall_limit:
        errors.append(f"run {label} has scored elapsed time above the fixed limit")
    if final_record and not bool(run.get("pass")) and elapsed != limits.get(
        "failure_scored_time_seconds"
    ):
        errors.append(f"failed run {label} was not charged the full fixed time")


def _check_protocol(
    run: Mapping[str, Any],
    errors: list[str],
    *,
    allow_observational_unscored: bool,
) -> bool:
    """Validate protocol evidence and return whether this is an official run."""

    label = str(run.get("run_id"))
    protocol = run.get("protocol")
    if not isinstance(protocol, Mapping):
        errors.append(f"final run {label} lacks a protocol record")
        return False
    claims = protocol.get("claims")
    verified = protocol.get("verified")
    if not isinstance(claims, Mapping):
        errors.append(f"final run {label} lacks protocol claims")
        claims = {}
    if not isinstance(verified, Mapping):
        errors.append(f"final run {label} lacks protocol verification evidence")
        verified = {}
    for name in PROTOCOL_CLAIMS:
        if not isinstance(claims.get(name), bool):
            errors.append(f"final run {label} has no Boolean protocol claim {name}")
    for name in PROTOCOL_VERIFICATIONS:
        if not isinstance(verified.get(name), bool):
            errors.append(f"final run {label} has no Boolean protocol verification {name}")
    seed_was_supplied = run.get("backend_seed") is not None
    if claims.get("backend_seed_supplied") is not seed_was_supplied:
        errors.append(
            f"final run {label} protocol disagrees with whether a backend seed was supplied"
        )
    if claims.get("seed_enforced_by_agent") is True and not seed_was_supplied:
        errors.append(f"final run {label} claims to enforce a missing backend seed")

    complete = protocol.get("complete") is True
    officially_scored = run.get("scored") is True and complete
    if officially_scored:
        for name in (
            claim
            for claim in PROTOCOL_CLAIMS
            if claim not in ("backend_seed_supplied", "seed_enforced_by_agent")
        ):
            if claims.get(name) is not True:
                errors.append(
                    f"official run {label} marks protocol complete while claim {name} is unmet"
                )
        if claims.get("backend_seed_supplied") != claims.get(
            "seed_enforced_by_agent"
        ):
            errors.append(
                f"official run {label} has an incomplete frozen seed mode"
            )
        for name in PROTOCOL_VERIFICATIONS:
            if verified.get(name) is not True:
                errors.append(
                    f"official run {label} marks protocol complete while verification {name} failed"
                )
        return True

    if not allow_observational_unscored:
        if not complete:
            errors.append(f"final run {label} does not have a complete protocol record")
        if run.get("scored") is not True:
            errors.append(f"final run {label} is not marked scored")
        return False

    if run.get("scored") is not False:
        errors.append(f"observational run {label} must be explicitly marked scored=false")
    if complete:
        errors.append(
            f"observational run {label} is unscored even though its protocol is marked complete"
        )
    unmet_claims = {
        name for name in PROTOCOL_CLAIMS if claims.get(name) is not True
    }
    unsafe_unmet = unmet_claims - OBSERVATIONAL_CONTROL_CLAIMS
    if unsafe_unmet:
        errors.append(
            f"observational run {label} failed non-relaxable controls: "
            + ", ".join(sorted(unsafe_unmet))
        )
    if not unmet_claims:
        errors.append(
            f"observational run {label} gives no unavailable backend/reference control reason"
        )
    failed_verifications = {
        name for name in PROTOCOL_VERIFICATIONS if verified.get(name) is not True
    }
    if failed_verifications:
        errors.append(
            f"observational run {label} failed required verification: "
            + ", ".join(sorted(failed_verifications))
        )
    notes = protocol.get("notes")
    if not isinstance(notes, list) or not notes or not all(
        isinstance(note, str) and note for note in notes
    ):
        errors.append(
            f"observational run {label} must explain its unavailable controls in protocol notes"
        )
    return False


def _check_network_evidence(run: Mapping[str, Any], errors: list[str]) -> None:
    label = str(run.get("run_id"))
    evidence = run.get("network_violation")
    if not isinstance(evidence, Mapping):
        errors.append(f"final run {label} lacks structured network-violation evidence")
        return
    for field in ("detected", "saturated", "integrity_ok"):
        if not isinstance(evidence.get(field), bool):
            errors.append(f"final run {label} has non-Boolean network field {field}")
    for field in ("event_count", "kernel_event_count"):
        value = evidence.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            errors.append(f"final run {label} has invalid network field {field}")
    note = evidence.get("note")
    if not isinstance(note, str) or not note:
        errors.append(f"final run {label} has no network evidence note")
    marker = evidence.get("saved_marker_log")
    marker_digest = evidence.get("marker_sha256")
    if marker is not None and (not isinstance(marker, str) or not marker):
        errors.append(f"final run {label} has an invalid saved network marker path")
    if marker_digest is not None and not _hex_digest(marker_digest):
        errors.append(f"final run {label} has an invalid saved network marker SHA-256")
    if (marker is None) != (marker_digest is None):
        errors.append(f"final run {label} has incomplete saved network marker evidence")

    detected = evidence.get("detected")
    integrity_ok = evidence.get("integrity_ok")
    event_count = evidence.get("event_count")
    if detected is False:
        if event_count != 0 or evidence.get("saturated") is not False:
            errors.append(f"final run {label} says no network event but records event data")
        if integrity_ok is not True:
            errors.append(f"final run {label} says no network event with failed marker integrity")
    if integrity_ok is False and detected is not True:
        errors.append(f"final run {label} has failed network integrity without a violation")
    if run.get("pass") is True and (detected is not False or integrity_ok is not True):
        errors.append(f"passing run {label} has unsafe network evidence")
    if detected is True and run.get("failure_code") not in {
        "TIME_LIMIT",
        "TOKEN_LIMIT",
        "NO_SUBMISSION",
        "RULE_VIOLATION",
    }:
        errors.append(
            f"run {label} detected a network attempt but has incoherent failure code "
            f"{run.get('failure_code')!r}"
        )
    protocol = run.get("protocol")
    verified = protocol.get("verified") if isinstance(protocol, Mapping) else None
    if isinstance(verified, Mapping) and verified.get(
        "network_violation_marker_integrity"
    ) is not integrity_ok:
        errors.append(f"final run {label} protocol disagrees with network marker integrity")


def _check_n_preflight_evidence(
    run: Mapping[str, Any],
    errors: list[str],
    *,
    controlled_manifest_sha256: str | None,
) -> None:
    if run.get("condition") != "N":
        return
    label = str(run.get("run_id"))
    preflight = run.get("n_preflight")
    if not isinstance(preflight, Mapping):
        errors.append(f"condition-N run {label} lacks structured preflight evidence")
        return
    if preflight.get("ok") is not True or preflight.get("complete") is not True:
        errors.append(f"condition-N run {label} did not complete its isolation preflight")
    staging = preflight.get("controlled_task_staging")
    if not isinstance(staging, Mapping):
        errors.append(f"condition-N run {label} has no controlled-task staging evidence")
    else:
        verified = staging.get("verified_files")
        expected = staging.get("expected_files")
        if (
            staging.get("complete") is not True
            or not isinstance(verified, int)
            or isinstance(verified, bool)
            or verified <= 0
            or verified != expected
            or not _hex_digest(staging.get("manifest_sha256"))
        ):
            errors.append(f"condition-N run {label} has incomplete controlled-task staging")
        if (
            controlled_manifest_sha256 is not None
            and staging.get("manifest_sha256") != controlled_manifest_sha256
        ):
            errors.append(f"condition-N run {label} staged the wrong controlled manifest")
    scan = preflight.get("filesystem_scan")
    if not isinstance(scan, Mapping):
        errors.append(f"condition-N run {label} has no complete filesystem-scan evidence")
    else:
        markers = scan.get("markers")
        file_count = scan.get("regular_file_count")
        expected = staging.get("expected_files") if isinstance(staging, Mapping) else None
        if (
            scan.get("root") != "."
            or not isinstance(markers, list)
            or "NumStability" not in markers
            or not isinstance(file_count, int)
            or isinstance(file_count, bool)
            or not isinstance(expected, int)
            or file_count < expected
            or scan.get("symlink_count") != 0
        ):
            errors.append(f"condition-N run {label} filesystem scan did not cover the staged task")
    probe = preflight.get("import_probe")
    if not isinstance(probe, Mapping) or (
        probe.get("reliable") is not True or probe.get("importable") is not False
    ):
        errors.append(f"condition-N run {label} did not prove the library import absent")


def _canonical_record_sha256(value: Mapping[str, Any], hash_field: str) -> str:
    unsigned = {key: item for key, item in value.items() if key != hash_field}
    payload = json.dumps(
        unsigned, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


class _AccountingProjectionError(ValueError):
    """One independently rederived Ultra accounting invariant failed."""


def _accounting_nonnegative_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise _AccountingProjectionError(f"{label} is not a nonnegative integer")
    return value


def _accounting_breakdown(value: Any, label: str) -> dict[str, int]:
    if not isinstance(value, Mapping):
        raise _AccountingProjectionError(f"{label} is not a token breakdown")
    result = {
        field: _accounting_nonnegative_int(value.get(field), f"{label}.{field}")
        for field in ACCOUNTING_TOKEN_FIELDS
    }
    if (
        result["cached_input_tokens"] > result["input_tokens"]
        or result["cache_write_input_tokens"] > result["input_tokens"]
        or result["reasoning_output_tokens"] > result["output_tokens"]
        or result["total_tokens"]
        != result["input_tokens"] + result["output_tokens"]
    ):
        raise _AccountingProjectionError(f"{label} is internally inconsistent")
    return result


def _accounting_optional_breakdown(
    value: Any, label: str
) -> dict[str, int] | None:
    return None if value is None else _accounting_breakdown(value, label)


def _accounting_identifier_set(value: Any, label: str) -> set[str]:
    if (
        not isinstance(value, list)
        or any(not isinstance(item, str) or not item for item in value)
        or value != sorted(set(value))
    ):
        raise _AccountingProjectionError(f"{label} is not a sorted identifier set")
    return set(value)


def _validate_ultra_fork_policy(
    usage: Mapping[str, Any],
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
    """Fail closed unless every raw spawn has one authenticated hook decision."""

    policy_blocked_ids = _accounting_identifier_set(
        usage.get("policy_blocked_spawn_call_ids"), "policy-blocked spawn IDs"
    )
    hook_observed_ids = _accounting_identifier_set(
        usage.get("hook_observed_spawn_call_ids"), "hook-observed spawn IDs"
    )
    hook_allowed_ids = _accounting_identifier_set(
        usage.get("hook_allowed_spawn_call_ids"), "hook-allowed spawn IDs"
    )
    hook_blocked_ids = _accounting_identifier_set(
        usage.get("hook_blocked_spawn_call_ids"), "hook-blocked spawn IDs"
    )
    hook_invalid_ids = _accounting_identifier_set(
        usage.get("hook_invalid_spawn_call_ids"), "hook-invalid spawn IDs"
    )
    policy = usage.get("fork_policy")
    expected_static = ultra_canary.codex_isolated.ultra_fork_policy_static_record()
    if (
        not isinstance(policy, Mapping)
        or set(policy) != set(expected_static) | {"call_evidence", "complete"}
    ):
        raise _AccountingProjectionError("fork-policy fields are not exact")
    static = dict(policy)
    raw_evidence = static.pop("call_evidence")
    complete = static.pop("complete")
    if static != expected_static or complete not in (True, False):
        raise _AccountingProjectionError("fork-policy freeze is inconsistent")
    if not isinstance(raw_evidence, list):
        raise _AccountingProjectionError("fork-policy call evidence is missing")

    if usage.get("fork_policy_complete") is False:
        if not allow_incomplete or complete is not False:
            raise _AccountingProjectionError("fork-policy projection is incomplete")
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
            raise _AccountingProjectionError(
                "incomplete fork-policy identifier projections are inconsistent"
            )
        by_id: dict[str, Mapping[str, Any]] = {}
        for index, raw_call in enumerate(raw_evidence):
            if not isinstance(raw_call, Mapping):
                raise _AccountingProjectionError(
                    f"fork-policy call {index} is not an object"
                )
            call_id = raw_call.get("call_id")
            if (
                set(raw_call) != ULTRA_FORK_POLICY_CALL_FIELDS
                or not isinstance(call_id, str)
                or not call_id
                or call_id in by_id
            ):
                raise _AccountingProjectionError(
                    "fork-policy call evidence is malformed"
                )
            by_id[call_id] = raw_call
        if list(by_id) != sorted(by_id) or set(by_id) != raw_ids:
            raise _AccountingProjectionError(
                "incomplete fork-policy call evidence is not canonical"
            )
        return by_id

    allowed_failed_ids = failed_ids - policy_blocked_ids
    allowed_terminal_ids = resolved_ids | allowed_failed_ids
    if (
        usage.get("fork_policy_complete") is not True
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
        raise _AccountingProjectionError(
            "fork-policy identifier projections are inconsistent"
        )

    if static != expected_static or complete is not True:
        raise _AccountingProjectionError("fork-policy freeze is inconsistent")

    by_id: dict[str, Mapping[str, Any]] = {}
    for index, raw_call in enumerate(raw_evidence):
        if not isinstance(raw_call, Mapping):
            raise _AccountingProjectionError(
                f"fork-policy call {index} is not an object"
            )
        call_id = raw_call.get("call_id")
        if (
            set(raw_call) != ULTRA_FORK_POLICY_CALL_FIELDS
            or not isinstance(call_id, str)
            or not call_id
            or call_id in by_id
        ):
            raise _AccountingProjectionError("fork-policy call evidence is malformed")
        by_id[call_id] = raw_call
    if list(by_id) != sorted(by_id) or set(by_id) != raw_ids:
        raise _AccountingProjectionError("fork-policy call evidence is not canonical")

    codex = ultra_canary.codex_isolated
    for call_id, call in by_id.items():
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
            raise _AccountingProjectionError(
                f"fork-policy call {call_id} has an inexact hook binding"
            )
        child_observed = call.get("child_activity_observed")
        if child_observed is not (call_id in resolved_ids):
            raise _AccountingProjectionError(
                f"fork-policy call {call_id} has inconsistent child activity"
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
                raise _AccountingProjectionError(
                    f"fork-policy blocked call {call_id} is inconsistent"
                )
            continue
        expected_semantics = {
            "all": "full_history_parent_pre_response",
            "none": "no_history_zero",
        }.get(fork_turns)
        expected_resolution = (
            "resolved_child" if call_id in resolved_ids else "failed_without_child"
        )
        if (
            expected_semantics is None
            or call.get("fork_semantics") != expected_semantics
            or call.get("hook_status") != codex.ULTRA_FORK_POLICY_ALLOW_STATUS
            or call.get("decision") != codex.ULTRA_FORK_POLICY_ALLOW_DECISION
            or call.get("feedback") is not None
            or call.get("resolution_status") != expected_resolution
        ):
            raise _AccountingProjectionError(
                f"fork-policy allowed call {call_id} is inconsistent"
            )
    return by_id


def _ultra_accounting_evidence(usage: Mapping[str, Any]) -> dict[str, Any]:
    """Return the complete normalized evidence needed for a second replay.

    This deliberately copies values from the run instead of trusting a producer
    digest or a producer-computed ``accounting_complete`` flag.  The report
    renderer performs the same arithmetic and graph checks over this evidence.
    """

    fields = (
        "accounting_projection_schema_version",
        "spawn_binding_source",
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
        "spawn_linkage_complete",
        "descendant_accounting_complete",
        "cumulative_projection_complete",
        "accounting_complete",
        "root_thread_id",
        "thread_count",
        "response_count",
        "call_count",
        "response_ids",
        "provider_response_count",
        "provider_response_ids",
        "provider_usage",
        "appserver_response_count",
        "appserver_response_ids",
        "appserver_usage",
        "suppressed_collaboration_wait_response_count",
        "suppressed_collaboration_wait_response_ids",
        "suppressed_collaboration_wait_usage",
        "suppressed_collaboration_wait_evidence",
        "superseded_by_collaboration_message_response_count",
        "superseded_by_collaboration_message_response_ids",
        "superseded_by_collaboration_message_usage",
        "superseded_by_collaboration_message_evidence",
        "discarded_after_explicit_child_interrupt_response_count",
        "discarded_after_explicit_child_interrupt_response_ids",
        "discarded_after_explicit_child_interrupt_usage",
        "discarded_after_explicit_child_interrupt_evidence",
        "provider_usage_reconciliation",
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "model_tokens",
        "submission_boundary_exact",
        "submission_boundary",
        "first_crossing",
        "stop_reason",
        "drain_complete",
        "active_thread_ids",
        "unresolved_thread_ids",
        "invalid_reasons",
        "interrupt_requested",
        "pending_interrupt_response_count",
        "appserver_response_ledger",
        "provider_token_gate",
        "adapter_teardown",
        "thread_accounting",
    )
    return {field: copy_value for field in fields if (copy_value := usage.get(field)) is not None} | {
        field: None
        for field in ("submission_boundary", "first_crossing")
        if field in usage and usage.get(field) is None
    }


def _derive_ultra_provider_gate_projection(
    usage: Mapping[str, Any],
    *,
    provider_response_ids: Sequence[str],
    provider_response_count: int,
    provider_totals: Mapping[str, Any],
    appserver_response_ids: Sequence[str],
    appserver_response_count: int,
    appserver_totals: Mapping[str, Any],
    accepted: bool,
) -> dict[str, Any]:
    """Rebind projection-v6 provider totals and structural app-server rows."""

    gate = usage.get("provider_token_gate")
    expected_gate_fields = ultra_canary.runner.ULTRA_PROVIDER_GATE_SUMMARY_KEYS
    if not isinstance(gate, Mapping) or set(gate) != set(expected_gate_fields):
        raise _AccountingProjectionError("provider-gate summary has the wrong schema")
    record_sha256 = gate.get("record_sha256")
    artifact_path = gate.get("artifact_path")
    if (
        gate.get("enabled") is not True
        or gate.get("response_token_bound")
        != ultra_canary.runner.PROVIDER_RESPONSE_TOKEN_BOUND
        or not isinstance(artifact_path, str)
        or not Path(artifact_path).is_absolute()
        or not _hex_digest(record_sha256)
        or gate.get("final_attached") is not True
        or gate.get("exact_for_usage") is not True
        or not isinstance(gate.get("live"), Mapping)
    ):
        raise _AccountingProjectionError("provider-gate summary is not exact and final")

    terminal = gate.get("terminal")
    if (
        not isinstance(terminal, Mapping)
        or set(terminal) != set(ultra_canary.runner.PROVIDER_GATE_STATE_KEYS)
        or terminal.get("phase") != "CLOSED"
        or terminal.get("open_request_ids") != []
        or terminal.get("all_complete") is not True
        or terminal.get("no_post_close_upstream") is not True
        or terminal.get("poisoned") is not False
        or terminal.get("poison_reasons") != []
        or terminal.get("active_handler_count") != 0
        or terminal.get("handlers_quiescent") is not True
        or terminal.get("completed_tokens") != provider_totals.get("total_tokens")
    ):
        raise _AccountingProjectionError("provider-gate terminal state is inexact")

    close_reason = terminal.get("close_reason")
    teardown = usage.get("adapter_teardown")
    if (
        not isinstance(teardown, Mapping)
        or set(teardown) != set(ultra_canary.runner.ULTRA_ADAPTER_TEARDOWN_KEYS)
        or teardown.get("process_group_isolated") is not True
        or teardown.get("immediate") is not (close_reason != "natural_end")
        or teardown.get("stdin_closed") is not True
        or teardown.get("completed") is not True
    ):
        raise _AccountingProjectionError("provider-gate endpoint lacks clean teardown")

    raw_ledger = usage.get("appserver_response_ledger")
    if not isinstance(raw_ledger, list) or len(raw_ledger) != appserver_response_count:
        raise _AccountingProjectionError("provider-gate response ledger has the wrong size")
    seen_responses: set[str] = set()
    seen_calls: set[str] = set()
    ledger_totals = {field: 0 for field in ACCOUNTING_TOKEN_FIELDS}
    ordered_calls: list[Mapping[str, Any]] = []
    for index, raw_response in enumerate(raw_ledger):
        if (
            not isinstance(raw_response, Mapping)
            or set(raw_response) != set(ultra_canary.runner.ULTRA_RESPONSE_LEDGER_KEYS)
        ):
            raise _AccountingProjectionError(
                f"provider-gate response ledger entry {index} has the wrong schema"
            )
        response_id = raw_response.get("response_id")
        thread_id = raw_response.get("thread_id")
        turn_id = raw_response.get("turn_id")
        sequence = raw_response.get("raw_response_notification_sequence")
        if (
            not isinstance(response_id, str)
            or not response_id
            or response_id in seen_responses
            or not isinstance(thread_id, str)
            or not thread_id
            or not isinstance(turn_id, str)
            or not turn_id
            or sequence != index + 1
        ):
            raise _AccountingProjectionError("provider-gate response identity is invalid")
        response_usage = _accounting_breakdown(
            raw_response.get("usage"), f"response ledger {response_id}.usage"
        )
        for field in ACCOUNTING_TOKEN_FIELDS:
            ledger_totals[field] += response_usage[field]
        call = raw_response.get("provider_gate_call")
        if (
            not isinstance(call, Mapping)
            or set(call) != set(ultra_canary.runner.PROVIDER_GATE_CALL_KEYS)
        ):
            raise _AccountingProjectionError("response lacks its exact provider-gate call")
        try:
            run_matrix._validate_provider_gate_call_sse_authentication(
                call,
                label=f"response ledger {response_id or index} provider-gate call",
            )
        except BenchmarkToolError as error:
            raise _AccountingProjectionError(str(error)) from error
        call_id = call.get("call_id")
        metadata = call.get("request_metadata")
        crossbind = call.get("appserver_crossbind")
        delivery = call.get("appserver_delivery")
        if (
            not isinstance(call_id, str)
            or not call_id
            or call_id in seen_calls
            or call.get("response_id") != response_id
            or call.get("response_bound")
            != ultra_canary.runner.PROVIDER_RESPONSE_TOKEN_BOUND
            or call.get("normalized_usage") != response_usage
            or call.get("client_release_complete") is not True
            or call.get("error") is not None
            or not isinstance(metadata, Mapping)
            or set(metadata)
            != set(ultra_canary.runner.PROVIDER_GATE_REQUEST_METADATA_KEYS)
            or any(
                not isinstance(metadata.get(name), str) or not metadata.get(name)
                for name in ultra_canary.runner.PROVIDER_GATE_REQUEST_METADATA_KEYS
            )
            or metadata.get("request_kind") not in {"turn", "compaction"}
            or metadata.get("thread_id") != thread_id
            or metadata.get("turn_id") != turn_id
            or not isinstance(crossbind, Mapping)
            or set(crossbind) != set(ultra_canary.runner.PROVIDER_GATE_CROSSBIND_KEYS)
            or crossbind.get("thread_id") != thread_id
            or crossbind.get("turn_id") != turn_id
            or crossbind.get("event_sequence") != sequence
            or crossbind.get("normalized_usage") != response_usage
            or not isinstance(delivery, Mapping)
            or set(delivery)
            != {
                "kind",
                "successor_call_id",
                "successor_response_id",
                "bind_unix_ns",
                "bind_monotonic_ns",
            }
            or delivery.get("kind") != "direct_raw_response"
            or delivery.get("successor_call_id") is not None
            or delivery.get("successor_response_id") is not None
            or delivery.get("bind_unix_ns") != crossbind.get("bind_unix_ns")
            or delivery.get("bind_monotonic_ns")
            != crossbind.get("bind_monotonic_ns")
        ):
            raise _AccountingProjectionError(
                "provider/app-server direct delivery binding changed"
            )
        seen_responses.add(response_id)
        seen_calls.add(call_id)
        ordered_calls.append(call)
    if (
        seen_responses != set(appserver_response_ids)
        or [response["response_id"] for response in raw_ledger]
        != list(appserver_response_ids)
        or [call.get("response_id") for call in ordered_calls]
        != list(appserver_response_ids)
        or ledger_totals != dict(appserver_totals)
    ):
        raise _AccountingProjectionError("provider response ledger does not reproduce usage")

    crossing = terminal.get("crossing")
    first_crossing = usage.get("first_crossing")
    if accepted:
        endpoint = "accepted_boundary"
        if (
            close_reason != "accepted_submission"
            or crossing is not None
            or first_crossing is not None
            or usage.get("stop_reason") != "first_valid_proof"
            or usage.get("drain_complete") is not False
            or any(call.get("release_kind") != "byte_identity" for call in ordered_calls)
        ):
            raise _AccountingProjectionError("accepted boundary and provider-gate close disagree")
    elif close_reason == "token_limit":
        endpoint = "token_gate_crossing"
        request_kind = crossing.get("request_kind") if isinstance(crossing, Mapping) else None
        expected_release_kind = (
            ultra_canary.runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
            if request_kind == "compaction"
            else ultra_canary.runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE
        )
        final_metadata = (
            ordered_calls[-1].get("request_metadata") if ordered_calls else None
        )
        if (
            not isinstance(crossing, Mapping)
            or set(crossing) != set(ultra_canary.runner.PROVIDER_GATE_CROSSING_KEYS)
            or request_kind not in {"turn", "compaction"}
            or not isinstance(first_crossing, Mapping)
            or first_crossing.get("response_id") != crossing.get("response_id")
            or first_crossing.get("tokens") != crossing.get("completed_tokens")
            or crossing.get("sole_inflight") is not True
            or crossing.get("release_kind") != expected_release_kind
            or usage.get("stop_reason") != "token_limit"
            or usage.get("drain_complete") is not False
            or len([call for call in ordered_calls if call.get("crossed_cap") is True]) != 1
            or ordered_calls[-1].get("response_id") != crossing.get("response_id")
            or ordered_calls[-1].get("release_kind") != expected_release_kind
            or not isinstance(final_metadata, Mapping)
            or final_metadata.get("request_kind") != request_kind
            or any(
                call.get("release_kind") != "byte_identity"
                for call in ordered_calls[:-1]
            )
        ):
            raise _AccountingProjectionError("token crossing and provider-gate close disagree")
    else:
        endpoint = "natural_drain"
        if (
            close_reason != "natural_end"
            or crossing is not None
            or first_crossing is not None
            or usage.get("drain_complete") is not True
            or any(call.get("release_kind") != "byte_identity" for call in ordered_calls)
        ):
            raise _AccountingProjectionError("natural outcome and provider-gate close disagree")
    return {
        "outcome": endpoint,
        "protocol": ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "record_sha256": record_sha256,
        "response_ids": list(provider_response_ids),
        "provider_response_count": provider_response_count,
        "appserver_response_ids": [call.get("response_id") for call in ordered_calls],
        "appserver_response_count": appserver_response_count,
        "close_reason": close_reason,
        "appserver_deliveries_reconciled": True,
        "adapter_teardown_complete": True,
    }


def _derive_ultra_accounting_projection(usage: Any) -> dict[str, Any]:
    """Independently rederive projection-v6 policy, graph, gate, and token completeness.

    Accepted runs have one narrow exception: the root's blocked ``submit_proof``
    response may be absent from the last cumulative provider notification.
    Token-limit runs instead require the exact sealed provider-gate crossing and
    may retain an active tree. Naturally drained outcomes have no exception and
    require a full cumulative projection for every rooted thread.
    """

    if not isinstance(usage, Mapping):
        raise _AccountingProjectionError("usage is not an object")
    if usage.get("accounting_projection_schema_version") != (
        ACCOUNTING_PROJECTION_SCHEMA_VERSION
    ):
        raise _AccountingProjectionError("accounting projection schema is not v6")
    if usage.get("spawn_binding_source") != ACCOUNTING_SPAWN_BINDING_SOURCE:
        raise _AccountingProjectionError("spawn binding source is not the raw call/activity identity")

    root_id = usage.get("root_thread_id")
    if not isinstance(root_id, str) or not root_id:
        raise _AccountingProjectionError("root thread id is missing")
    response_ids_raw = usage.get("response_ids")
    if (
        not isinstance(response_ids_raw, list)
        or any(not isinstance(item, str) or not item for item in response_ids_raw)
        or len(response_ids_raw) != len(set(response_ids_raw))
    ):
        raise _AccountingProjectionError("response-id ledger is malformed")
    provider_response_ids = list(response_ids_raw)
    provider_response_count = _accounting_nonnegative_int(
        usage.get("response_count"), "response_count"
    )
    if (
        len(provider_response_ids) != provider_response_count
        or usage.get("call_count") != provider_response_count
    ):
        raise _AccountingProjectionError("response totals disagree")
    provider_totals = {
        "input_tokens": usage.get("input_tokens"),
        "cached_input_tokens": usage.get("cached_input_tokens"),
        "cache_write_input_tokens": usage.get("cache_write_input_tokens"),
        "output_tokens": usage.get("output_tokens"),
        "reasoning_output_tokens": usage.get("reasoning_output_tokens"),
        "total_tokens": usage.get("model_tokens"),
    }
    try:
        reconciliation = run_matrix.verify_provider_usage_reconciliation(
            usage.get("provider_usage_reconciliation"),
            expected_provider_usage=provider_totals,
            expected_provider_response_ids=provider_response_ids,
            expected_thread_accounting=usage.get("thread_accounting"),
            expected_root_thread_id=usage.get("root_thread_id"),
            expected_appserver_response_ledger=usage.get(
                "appserver_response_ledger"
            ),
        )
    except BenchmarkToolError as error:
        raise _AccountingProjectionError(str(error)) from error
    appserver_response_ids = reconciliation["appserver_response_ids"]
    appserver_response_count = reconciliation["appserver_response_count"]
    appserver_totals = reconciliation["appserver_usage"]
    if (
        usage.get("provider_response_count") != provider_response_count
        or usage.get("provider_response_ids") != provider_response_ids
        or usage.get("provider_usage") != provider_totals
        or usage.get("appserver_response_count") != appserver_response_count
        or usage.get("appserver_response_ids") != appserver_response_ids
        or usage.get("appserver_usage") != appserver_totals
        or usage.get("suppressed_collaboration_wait_response_count")
        != reconciliation["suppressed_collaboration_wait_response_count"]
        or usage.get("suppressed_collaboration_wait_response_ids")
        != reconciliation["suppressed_collaboration_wait_response_ids"]
        or usage.get("suppressed_collaboration_wait_usage")
        != reconciliation["suppressed_collaboration_wait_usage"]
        or usage.get("suppressed_collaboration_wait_evidence")
        != reconciliation["suppressed_collaboration_wait_evidence"]
        or usage.get("superseded_by_collaboration_message_response_count")
        != reconciliation[
            "superseded_by_collaboration_message_response_count"
        ]
        or usage.get("superseded_by_collaboration_message_response_ids")
        != reconciliation["superseded_by_collaboration_message_response_ids"]
        or usage.get("superseded_by_collaboration_message_usage")
        != reconciliation["superseded_by_collaboration_message_usage"]
        or usage.get("superseded_by_collaboration_message_evidence")
        != reconciliation["superseded_by_collaboration_message_evidence"]
        or usage.get(
            "discarded_after_explicit_child_interrupt_response_count"
        )
        != reconciliation[
            "discarded_after_explicit_child_interrupt_response_count"
        ]
        or usage.get("discarded_after_explicit_child_interrupt_response_ids")
        != reconciliation[
            "discarded_after_explicit_child_interrupt_response_ids"
        ]
        or usage.get("discarded_after_explicit_child_interrupt_usage")
        != reconciliation["discarded_after_explicit_child_interrupt_usage"]
        or usage.get("discarded_after_explicit_child_interrupt_evidence")
        != reconciliation[
            "discarded_after_explicit_child_interrupt_evidence"
        ]
    ):
        raise _AccountingProjectionError(
            "normalized provider/app-server reconciliation aliases disagree"
        )

    boundary = usage.get("submission_boundary")
    accepted = bool(
        usage.get("submission_boundary_exact") is True
        and isinstance(boundary, Mapping)
        and boundary.get("status") == "accepted"
        and boundary.get("exact") is True
        and boundary.get("authenticated") is True
    )
    if usage.get("submission_boundary_exact") not in (True, False):
        raise _AccountingProjectionError("submission boundary exactness is not Boolean")
    if accepted:
        boundary_response_id = boundary.get("response_id")
        if (
            not isinstance(boundary_response_id, str)
            or boundary_response_id not in provider_response_ids
            or boundary.get("thread_id") != root_id
        ):
            raise _AccountingProjectionError("accepted boundary is not the rooted response")
    else:
        boundary_response_id = None
        if boundary is not None or usage.get("submission_boundary_exact") is not False:
            raise _AccountingProjectionError("non-accepted outcome carries a submission boundary")
    raw_gate_hint = usage.get("provider_token_gate")
    terminal_hint = (
        raw_gate_hint.get("terminal")
        if isinstance(raw_gate_hint, Mapping)
        else None
    )
    token_endpoint_hint = bool(
        not accepted
        and isinstance(terminal_hint, Mapping)
        and terminal_hint.get("close_reason") == "token_limit"
    )

    raw_threads = usage.get("thread_accounting")
    thread_count = _accounting_nonnegative_int(
        usage.get("thread_count"), "thread_count"
    )
    if not isinstance(raw_threads, list) or len(raw_threads) != thread_count or not raw_threads:
        raise _AccountingProjectionError("thread-accounting ledger has the wrong size")
    zero = {field: 0 for field in ACCOUNTING_TOKEN_FIELDS}
    threads: dict[str, dict[str, Any]] = {}
    summed = dict(zero)
    summed_responses = 0
    for index, raw in enumerate(raw_threads):
        if not isinstance(raw, Mapping):
            raise _AccountingProjectionError(f"thread {index} is not an object")
        thread_id = raw.get("thread_id")
        if not isinstance(thread_id, str) or not thread_id or thread_id in threads:
            raise _AccountingProjectionError("thread identifiers are invalid or repeated")
        parent_id = raw.get("parent_thread_id")
        if parent_id is not None and (not isinstance(parent_id, str) or not parent_id):
            raise _AccountingProjectionError(f"thread {thread_id} has an invalid parent")
        raw_sum = {
            field: _accounting_nonnegative_int(
                raw.get(field), f"thread {thread_id}.{field}"
            )
            for field in ACCOUNTING_TOKEN_FIELDS
        }
        if (
            raw_sum["cached_input_tokens"] > raw_sum["input_tokens"]
            or raw_sum["cache_write_input_tokens"] > raw_sum["input_tokens"]
            or raw_sum["reasoning_output_tokens"] > raw_sum["output_tokens"]
            or raw_sum["total_tokens"]
            != raw_sum["input_tokens"] + raw_sum["output_tokens"]
        ):
            raise _AccountingProjectionError(f"thread {thread_id} raw sum is inconsistent")
        for field in ACCOUNTING_TOKEN_FIELDS:
            summed[field] += raw_sum[field]
        raw_response_count = _accounting_nonnegative_int(
            raw.get("response_count"), f"thread {thread_id}.response_count"
        )
        summed_responses += raw_response_count

        is_root = thread_id == root_id
        baseline = _accounting_optional_breakdown(
            raw.get("expected_cumulative_baseline"),
            f"thread {thread_id}.expected_cumulative_baseline",
        )
        exempt_id = raw.get("cumulative_projection_exempt_response_id")
        exempt_usage = _accounting_optional_breakdown(
            raw.get("cumulative_projection_exempt_response_usage"),
            f"thread {thread_id}.cumulative_projection_exempt_response_usage",
        )
        if accepted and is_root:
            if exempt_id != boundary_response_id or exempt_usage is None:
                raise _AccountingProjectionError("accepted root lacks its exact blocked-response exception")
        elif exempt_id is not None or exempt_usage is not None:
            raise _AccountingProjectionError("only an accepted root may exempt one response")
        last = _accounting_optional_breakdown(
            raw.get("last_cumulative"), f"thread {thread_id}.last_cumulative"
        )
        observations = _accounting_nonnegative_int(
            raw.get("cumulative_observation_count"),
            f"thread {thread_id}.cumulative_observation_count",
        )
        if (observations == 0) != (last is None):
            raise _AccountingProjectionError(f"thread {thread_id} observation count disagrees")
        if baseline is None:
            if is_root or not token_endpoint_hint:
                raise _AccountingProjectionError(
                    f"thread {thread_id} has an unresolved baseline outside a token crossing"
                )
            full = _accounting_optional_breakdown(
                raw.get("full_cumulative_projection"),
                f"thread {thread_id}.full_cumulative_projection",
            )
            expected = _accounting_optional_breakdown(
                raw.get("expected_cumulative_projection"),
                f"thread {thread_id}.expected_cumulative_projection",
            )
            if full is not None or expected is not None:
                raise _AccountingProjectionError(
                    f"thread {thread_id} unresolved baseline has a projection"
                )
            projection_match = False
            observed_baseline = None
            baseline_match = False
            projection_status = "unresolved_expected_baseline"
        else:
            full = {
                field: baseline[field] + raw_sum[field]
                for field in ACCOUNTING_TOKEN_FIELDS
            }
            if _accounting_optional_breakdown(
                raw.get("full_cumulative_projection"),
                f"thread {thread_id}.full_cumulative_projection",
            ) != full:
                raise _AccountingProjectionError(
                    f"thread {thread_id} full projection disagrees"
                )
            projected_raw = dict(raw_sum)
            if exempt_usage is not None:
                projected_raw = {
                    field: raw_sum[field] - exempt_usage[field]
                    for field in ACCOUNTING_TOKEN_FIELDS
                }
                if any(value < 0 for value in projected_raw.values()):
                    raise _AccountingProjectionError(
                        "root exception exceeds its raw response sum"
                    )
            expected = {
                field: baseline[field] + projected_raw[field]
                for field in ACCOUNTING_TOKEN_FIELDS
            }
            if _accounting_optional_breakdown(
                raw.get("expected_cumulative_projection"),
                f"thread {thread_id}.expected_cumulative_projection",
            ) != expected:
                raise _AccountingProjectionError(
                    f"thread {thread_id} expected projection disagrees"
                )
            if last is None:
                projection_match = bool(
                    accepted and is_root and expected == zero and baseline == zero
                )
                observed_baseline = None
                baseline_match = projection_match
                projection_status = (
                    "zero_pre_response_without_cumulative_notification"
                    if projection_match
                    else "missing_cumulative"
                )
            else:
                compare_raw = (
                    raw_sum
                    if exempt_usage is not None and last == full
                    else projected_raw
                )
                differences = {
                    field: last[field] - compare_raw[field]
                    for field in ACCOUNTING_TOKEN_FIELDS
                }
                observed_baseline = (
                    differences
                    if all(value >= 0 for value in differences.values())
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
                    projection_status = "matched_full_including_exempt_response"
                elif exempt_usage is not None and last == expected:
                    projection_status = "matched_pre_exempt_response"
                elif exempt_usage is None and last == expected:
                    projection_status = "matched_full_projection"
                else:
                    projection_status = "cumulative_projection_mismatch"
        if (
            raw.get("observed_cumulative_baseline") != observed_baseline
            or raw.get("cumulative_baseline_matches_expected") != baseline_match
            or raw.get("cumulative_projection_match") != projection_match
            or raw.get("cumulative_projection_status") != projection_status
        ):
            raise _AccountingProjectionError(f"thread {thread_id} projection attestation disagrees")

        binding_status = raw.get("spawn_binding_status")
        spawn_fields = (
            raw.get("spawn_call_id"),
            raw.get("spawn_parent_turn_id"),
            raw.get("spawn_parent_response_id"),
            raw.get("spawn_fork_turns"),
            raw.get("spawn_fork_semantics"),
        )
        if is_root:
            binding_complete = bool(
                parent_id is None
                and binding_status == "root_zero"
                and all(value is None for value in spawn_fields)
                and baseline == zero
            )
        else:
            call_id, parent_turn, parent_response, fork_turns, fork_semantics = spawn_fields
            expected_semantics = {
                "none": "no_history_zero",
                "all": "full_history_parent_pre_response",
            }.get(fork_turns)
            binding_complete = bool(
                binding_status == "resolved"
                and isinstance(call_id, str)
                and call_id
                and isinstance(parent_turn, str)
                and parent_turn
                and isinstance(parent_response, str)
                and parent_response in appserver_response_ids
                and expected_semantics is not None
                and fork_semantics == expected_semantics
                and (fork_turns != "none" or baseline == zero)
            )
        accounting_complete = bool(binding_complete and projection_match)
        if raw.get("accounting_complete") != accounting_complete:
            raise _AccountingProjectionError(f"thread {thread_id} accounting Boolean disagrees")
        threads[thread_id] = {
            "parent_thread_id": parent_id,
            "spawn_call_id": raw.get("spawn_call_id"),
            "accounting_complete": accounting_complete,
            "projection_match": projection_match,
            "baseline": baseline,
        }

    if root_id not in threads or threads[root_id]["parent_thread_id"] is not None:
        raise _AccountingProjectionError("root thread is absent or parented")
    for thread_id, thread in threads.items():
        if thread_id == root_id:
            continue
        parent = thread["parent_thread_id"]
        if parent not in threads or parent == thread_id:
            raise _AccountingProjectionError(f"child {thread_id} has an invalid parent")
        seen: set[str] = set()
        current: str | None = thread_id
        while current is not None:
            if current in seen:
                raise _AccountingProjectionError("thread-parent graph contains a cycle")
            seen.add(current)
            parent_value = threads[current]["parent_thread_id"]
            current = parent_value if isinstance(parent_value, str) else None

    if summed != appserver_totals or summed_responses != appserver_response_count:
        raise _AccountingProjectionError(
            "per-thread sums disagree with structural app-server usage"
        )

    gate_projection = _derive_ultra_provider_gate_projection(
        usage,
        provider_response_ids=provider_response_ids,
        provider_response_count=provider_response_count,
        provider_totals=provider_totals,
        appserver_response_ids=appserver_response_ids,
        appserver_response_count=appserver_response_count,
        appserver_totals=appserver_totals,
        accepted=accepted,
    )

    raw_ids = _accounting_identifier_set(usage.get("raw_spawn_call_ids"), "raw spawn IDs")
    activity_ids = _accounting_identifier_set(
        usage.get("activity_spawn_call_ids"), "activity spawn IDs"
    )
    collab_ids = _accounting_identifier_set(
        usage.get("collab_spawn_call_ids"), "collaboration spawn IDs"
    )
    resolved_ids = _accounting_identifier_set(
        usage.get("resolved_spawn_call_ids"), "resolved spawn IDs"
    )
    failed_ids = _accounting_identifier_set(
        usage.get("failed_spawn_call_ids"), "failed spawn IDs"
    )
    policy_blocked_ids = _accounting_identifier_set(
        usage.get("policy_blocked_spawn_call_ids"), "policy-blocked spawn IDs"
    )
    unresolved_ids = _accounting_identifier_set(
        usage.get("unresolved_spawn_call_ids"), "unresolved spawn IDs"
    )
    unsupported_ids = _accounting_identifier_set(
        usage.get("unsupported_spawn_call_ids"), "unsupported spawn IDs"
    )
    inference_child_ids = _accounting_identifier_set(
        usage.get("inference_child_thread_ids"), "inference child IDs"
    )
    terminal_ids = resolved_ids | failed_ids
    children = set(threads) - {root_id}
    child_spawn_ids = {
        str(threads[thread_id]["spawn_call_id"])
        for thread_id in children
        if threads[thread_id]["spawn_call_id"] is not None
    }
    _validate_ultra_fork_policy(
        usage,
        raw_ids=raw_ids,
        activity_ids=activity_ids,
        collab_ids=collab_ids,
        resolved_ids=resolved_ids,
        failed_ids=failed_ids,
        unsupported_ids=unsupported_ids,
        known_thread_ids=set(threads),
        response_ids=set(appserver_response_ids),
        allow_incomplete=token_endpoint_hint,
    )
    derived_spawn_complete = bool(
        not (resolved_ids & failed_ids)
        and raw_ids == terminal_ids
        and activity_ids == resolved_ids
        and collab_ids <= terminal_ids
        and not unresolved_ids
        and not unsupported_ids
        and inference_child_ids == children
        and child_spawn_ids == resolved_ids
        and len(child_spawn_ids) == len(children)
        and policy_blocked_ids <= failed_ids
        and usage.get("fork_policy_complete") is True
    )
    derived_descendants = all(
        threads[thread_id]["accounting_complete"] for thread_id in children
    )
    derived_cumulative = all(
        thread["projection_match"] for thread in threads.values()
    )
    derived_complete = bool(
        derived_spawn_complete
        and derived_cumulative
        and all(thread["accounting_complete"] for thread in threads.values())
    )
    expected_booleans = {
        "spawn_linkage_complete": derived_spawn_complete,
        "descendant_accounting_complete": derived_descendants,
        "cumulative_projection_complete": derived_cumulative,
        # The provider-gated token endpoint is allowed to stop with an
        # in-progress fork-policy ledger.  The verifier above still replays the
        # reported Boolean against the exact call evidence; accepted and
        # naturally drained endpoints remain complete.
        "fork_policy_complete": usage.get("fork_policy_complete"),
        "accounting_complete": derived_complete,
    }
    if any(usage.get(field) != value for field, value in expected_booleans.items()):
        raise _AccountingProjectionError("top-level accounting Booleans disagree")
    if gate_projection["outcome"] != "token_gate_crossing" and not all(
        expected_booleans.values()
    ):
        raise _AccountingProjectionError("Ultra accounting projection is incomplete")
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
        "accounting_complete": derived_complete,
        "cumulative_projection_complete": derived_cumulative,
        "spawn_linkage_complete": derived_spawn_complete,
        "fork_policy_complete": usage.get("fork_policy_complete"),
        "evidence": _ultra_accounting_evidence(usage),
    }


def _check_ultra_accounting_projection(
    run: Mapping[str, Any], errors: list[str]
) -> dict[str, Any]:
    label = str(run.get("run_id"))
    try:
        audit = _derive_ultra_accounting_projection(run.get("token_usage"))
    except _AccountingProjectionError as error:
        errors.append(f"final Ultra run {label} has invalid accounting projection: {error}")
        return {"run_id": label, "valid": False, "error": str(error)}
    return {"run_id": label, "valid": True, **audit}


def _validation_artifact_path(
    raw_path: Any,
    *,
    repository_root: Path,
    label: str,
    errors: list[str],
) -> Path | None:
    if not isinstance(raw_path, str) or not raw_path:
        errors.append(f"{label} has no retained path")
        return None
    unresolved = Path(raw_path)
    if not unresolved.is_absolute():
        unresolved = repository_root / unresolved
    try:
        metadata = unresolved.lstat()
    except OSError as error:
        errors.append(f"{label} is missing: {error}")
        return None
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        errors.append(f"{label} is not a retained regular non-symlink file")
        return None
    path = unresolved.resolve()
    try:
        path.relative_to(repository_root.resolve())
    except ValueError:
        errors.append(f"{label} escapes the repository/results root")
        return None
    return path


def _check_validation_authentication(
    run: Mapping[str, Any],
    task: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
    *,
    controlled_manifest_sha256: str | None,
    repository_root: Path | None,
) -> None:
    """Authenticate the exact bytes accepted or rejected by hidden validation."""

    label = str(run.get("run_id"))
    log_path = run.get("validation_log")
    byte_digest = run.get("validation_log_sha256")
    record_digest = run.get("validation_record_sha256")
    frozen = config.get("frozen_environment")
    ultra = bool(
        isinstance(frozen, Mapping)
        and frozen.get("model_reasoning_effort") == "ultra"
    )
    validation_expected = bool(
        (ultra and (run.get("pass") is True or run.get("failure_code") == "PROOF_ERROR"))
        or log_path is not None
        or byte_digest is not None
        or record_digest is not None
    )
    if not validation_expected:
        return
    if (
        not isinstance(log_path, str)
        or not log_path
        or not _hex_digest(byte_digest)
        or not _hex_digest(record_digest)
    ):
        errors.append(f"final run {label} lacks authenticated validation-log hashes")
        return
    if repository_root is None:
        return
    path = _validation_artifact_path(
        log_path,
        repository_root=repository_root,
        label=f"final run {label} validation log",
        errors=errors,
    )
    if path is None:
        return
    try:
        payload = path.read_bytes()
    except OSError as error:
        errors.append(f"cannot reread final run {label} validation log: {error}")
        return
    if hashlib.sha256(payload).hexdigest() != byte_digest:
        errors.append(f"final run {label} validation-log byte hash changed")
        return
    try:
        validation = json.loads(payload)
    except (UnicodeError, json.JSONDecodeError) as error:
        errors.append(f"final run {label} validation log is not valid JSON: {error}")
        return
    if not isinstance(validation, Mapping):
        errors.append(f"final run {label} validation log is not an object")
        return
    if (
        validation.get("record_sha256") != record_digest
        or _canonical_record_sha256(validation, "record_sha256") != record_digest
    ):
        errors.append(f"final run {label} validation record self-hash is invalid")
    authentication = validation.get("authentication")
    plural = task.get("tier") == "T4"
    expected_fields = (
        PLURAL_VALIDATION_AUTHENTICATION_FIELDS
        if plural
        else VALIDATION_AUTHENTICATION_FIELDS
    )
    if not isinstance(authentication, Mapping) or set(authentication) != expected_fields:
        errors.append(f"final run {label} validation authentication schema is invalid")
        return
    common_identity_invalid = (
        authentication.get("run_id") != run.get("run_id")
        or authentication.get("task_id") != run.get("task_id")
        or not _hex_digest(authentication.get("candidate_sha256"))
        or authentication.get("controlled_manifest_sha256")
        != controlled_manifest_sha256
        or not _hex_digest(authentication.get("validator_contract_sha256"))
    )
    if plural:
        expected_required = task.get("required_declarations")
        required = authentication.get("required_declarations")
        holes = authentication.get("controlled_sorries")
        proof_declarations: list[str] = []
        holes_valid = isinstance(holes, list) and bool(holes)
        if holes_valid:
            previous_required_index = -1
            for index, hole in enumerate(holes, start=1):
                if not isinstance(hole, Mapping) or set(hole) != CONTROLLED_SORRY_FIELDS:
                    holes_valid = False
                    break
                lean_name = hole.get("lean_name")
                placeholder_id = hole.get("placeholder_id")
                if (
                    hole.get("placeholder_order") != index
                    or not isinstance(lean_name, str)
                    or not isinstance(placeholder_id, str)
                    or hole.get("marker") != f"-- PROOF_START {placeholder_id}"
                    or not isinstance(required, list)
                    or lean_name not in required
                ):
                    holes_valid = False
                    break
                required_index = required.index(lean_name)
                if required_index <= previous_required_index:
                    holes_valid = False
                    break
                previous_required_index = required_index
                proof_declarations.append(lean_name)
        expected_holes = task.get("controlled_sorries")
        if (
            authentication.get("schema_version") != 2
            or common_identity_invalid
            or not isinstance(required, list)
            or not required
            or required != expected_required
            or not holes_valid
            or (
                expected_holes is not None
                and holes != expected_holes
            )
            or validation.get("required_declarations") != required
            or validation.get("controlled_sorries") != holes
            or validation.get("proof_declarations") != proof_declarations
            or validation.get("target_theorem") != proof_declarations[0]
        ):
            errors.append(
                f"final run {label} validation authentication identity is invalid"
            )
    else:
        expected_target = task.get("target_theorem")
        if (
            authentication.get("schema_version") != 1
            or common_identity_invalid
            or not isinstance(authentication.get("target_theorem"), str)
            or not authentication.get("target_theorem")
            or (
                isinstance(expected_target, str)
                and expected_target
                and authentication.get("target_theorem") != expected_target
            )
        ):
            errors.append(
                f"final run {label} validation authentication identity is invalid"
            )

    request_sha = authentication.get("submission_request_sha256")
    sequence = authentication.get("submission_sequence")
    if ultra:
        if (
            not _hex_digest(request_sha)
            or not isinstance(sequence, int)
            or isinstance(sequence, bool)
            or sequence <= 0
        ):
            errors.append(f"final Ultra run {label} validation lacks request binding")
        boundary = run.get("ultra_submission_boundary")
        usage = run.get("token_usage")
        usage_boundary = (
            usage.get("submission_boundary") if isinstance(usage, Mapping) else None
        )
        if run.get("pass") is True and (
            not isinstance(boundary, Mapping)
            or not isinstance(usage_boundary, Mapping)
            or boundary.get("request_sha256") != request_sha
            or boundary.get("sequence") != sequence
            or usage_boundary.get("request_sha256") != request_sha
            or usage_boundary.get("sequence") != sequence
            or usage_boundary.get("validator_contract_sha256")
            != authentication.get("validator_contract_sha256")
            or usage_boundary.get("candidate_sha256")
            != authentication.get("candidate_sha256")
        ):
            errors.append(f"passing Ultra run {label} validation is not bound to its barrier")
    elif request_sha is not None or sequence is not None:
        errors.append(f"non-Ultra run {label} validation has an Ultra request binding")

    if run.get("pass") is True:
        if (
            validation.get("pass") is not True
            or authentication.get("candidate_sha256") != run.get("submission_sha256")
            or run.get("final_submission_sha256") != run.get("submission_sha256")
        ):
            errors.append(f"passing run {label} validation did not authenticate accepted bytes")
    elif run.get("failure_code") == "PROOF_ERROR" and validation.get("pass") is not False:
        errors.append(f"proof-error run {label} lacks an authenticated rejection")


def _barrier_artifact_path(
    raw_path: Any,
    *,
    repository_root: Path,
    label: str,
    errors: list[str],
) -> Path | None:
    if not isinstance(raw_path, str) or not raw_path:
        errors.append(f"{label} has no retained path")
        return None
    candidate = Path(raw_path)
    unresolved = candidate if candidate.is_absolute() else repository_root / candidate
    try:
        unresolved_metadata = unresolved.lstat()
    except OSError as error:
        errors.append(f"{label} is missing: {error}")
        return None
    if stat.S_ISLNK(unresolved_metadata.st_mode):
        errors.append(f"{label} is a symlink rather than a retained regular file")
        return None
    path = unresolved.resolve()
    root = repository_root.resolve()
    try:
        path.relative_to(root)
    except ValueError:
        errors.append(f"{label} escapes the repository/results root")
        return None
    metadata = unresolved_metadata
    if not stat.S_ISREG(metadata.st_mode):
        errors.append(f"{label} is not a retained regular file")
        return None
    if stat.S_IMODE(metadata.st_mode) != 0o444:
        errors.append(f"{label} is not sealed mode 0444")
        return None
    return path


def _prompt_turn_start_wire(
    *, prompt: str, root_thread_id: str, model: str, reasoning_effort: str
) -> bytes:
    """Independently reconstruct the exact adapter ``turn/start`` wire bytes."""

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


def _check_prompt_release_authentication(
    run: Mapping[str, Any],
    config: Mapping[str, Any],
    effective_prompt: str | None,
    errors: list[str],
    *,
    repository_root: Path | None,
) -> dict[str, Any]:
    """Authenticate the READY/GO/RELEASED chain and its measurement origin.

    This is deliberately a consumer-side reimplementation.  It does not trust
    the runner's normalized booleans, embedded records, descriptor hashes, or
    elapsed-time calculation without rederiving them.
    """

    label = str(run.get("run_id"))
    error_count = len(errors)
    top = run.get("prompt_release")
    top_fields = {
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
    limits = config.get("limits")
    configured_startup = (
        limits.get("prompt_startup_timeout_seconds")
        if isinstance(limits, Mapping)
        else None
    )
    wall_limit = (
        limits.get("wall_clock_seconds") if isinstance(limits, Mapping) else None
    )
    if (
        not isinstance(configured_startup, (int, float))
        or isinstance(configured_startup, bool)
        or float(configured_startup) != PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS
    ):
        errors.append(
            "frozen config must set prompt_startup_timeout_seconds=120 separately "
            "from the scored wall limit"
        )
    if (
        not isinstance(wall_limit, (int, float))
        or isinstance(wall_limit, bool)
        or wall_limit <= 0
    ):
        errors.append("frozen config has no positive scored wall limit")
        wall_limit = None
    if not isinstance(top, Mapping):
        errors.append(f"final run {label} lacks authenticated prompt-release evidence")
        return {
            "run_id": label,
            "valid": False,
            "artifact_set_count": 0,
            "artifact_file_count": 0,
            "artifact_content_verified": False,
            "released_at_monotonic_ns": None,
            "measurement_deadline_monotonic_ns": None,
            "ultra_request_publication_timing_verified": False,
        }
    if set(top) != top_fields:
        errors.append(f"final run {label} prompt-release summary has unexpected fields")
    nonce = top.get("handshake_nonce")
    encoded = effective_prompt.encode("utf-8") if isinstance(effective_prompt, str) else None
    effective_sha = hashlib.sha256(encoded).hexdigest() if encoded is not None else None
    if effective_prompt is None:
        errors.append(f"final run {label} has no authenticated effective prompt bytes")
    expected_top = {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "required": True,
        "status": "released_authenticated",
        "authenticated": True,
        "timing_exact": True,
        "useful_work_basis": "authenticated_release",
        "startup_timeout_seconds": PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS,
        "startup_timeout_triggered": False,
        "go_minimum_release_window_seconds": PROMPT_RELEASE_GO_MINIMUM_WINDOW_SECONDS,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "effective_prompt_sha256": effective_sha,
        "effective_prompt_bytes": len(encoded) if encoded is not None else None,
        "error": None,
    }
    if any(top.get(field) != value for field, value in expected_top.items()):
        errors.append(f"final run {label} has an inexact prompt-release summary")
    if not _hex_digest(nonce):
        errors.append(f"final run {label} has an invalid prompt-handshake nonce")

    stale = top.get("stale_artifacts_removed")
    if (
        not isinstance(stale, list)
        or stale != sorted(set(stale))
        or any(not isinstance(item, str) or not Path(item).is_absolute() for item in stale)
    ):
        errors.append(f"final run {label} has invalid stale prompt-artifact evidence")

    artifact_paths = top.get("artifact_paths")
    if not isinstance(artifact_paths, Mapping) or set(artifact_paths) != {
        "ready",
        "go",
        "release",
    }:
        errors.append(f"final run {label} has invalid prompt artifact paths")
        artifact_paths = {}
    command = run.get("agent_command")
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        errors.append(f"final run {label} lacks an auditable prompt-release command")
        command = []
    command_options = {
        "ready": "--prompt-ready-output",
        "go": "--prompt-go-input",
        "release": "--prompt-release-output",
    }
    command_paths: dict[str, str] = {}
    for name, option in command_options.items():
        count, value = _argv_option(command, option)
        if count != 1 or not isinstance(value, str) or not Path(value).is_absolute():
            errors.append(f"final run {label} agent command has invalid {option}")
        else:
            command_paths[name] = value
            if artifact_paths.get(name) != value:
                errors.append(
                    f"final run {label} {name} artifact path is not command-bound"
                )
    for option, wanted in (
        ("--prompt-handshake-nonce", nonce),
        ("--prompt-run-id", run.get("run_id")),
    ):
        count, value = _argv_option(command, option)
        if count != 1 or value != wanted:
            errors.append(f"final run {label} agent command has invalid {option}")
    count, usage_output = _argv_option(command, "--usage-output")
    if count != 1 or not isinstance(usage_output, str) or not Path(usage_output).is_absolute():
        errors.append(f"final run {label} agent command has invalid --usage-output")
    else:
        usage_path = Path(usage_output)
        suffix = ".usage.json"
        base = (
            usage_path.name[: -len(suffix)]
            if usage_path.name.endswith(suffix)
            else usage_path.stem
        )
        expected_names = {
            "ready": f"{base}.prompt-ready.json",
            "go": f"{base}.prompt-go.json",
            "release": f"{base}.prompt-release.json",
        }
        if not base or base in (".", "..") or any(
            Path(path).parent != usage_path.parent
            or Path(path).name != expected_names[name]
            for name, path in command_paths.items()
        ) or set(command_paths) != set(expected_names):
            errors.append(
                f"final run {label} prompt artifacts are not derived from its usage path"
            )

    agent = run.get("agent")
    usage = run.get("token_usage")
    root_thread_id = usage.get("root_thread_id") if isinstance(usage, Mapping) else None
    expected_common = {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "handshake_nonce": nonce,
        "run_id": run.get("run_id"),
        "condition": run.get("condition"),
        "model": agent.get("model") if isinstance(agent, Mapping) else None,
        "reasoning_effort": (
            agent.get("reasoning_effort") if isinstance(agent, Mapping) else None
        ),
        "root_thread_id": root_thread_id,
        "turn_start_request_id": 3,
        "effective_prompt_sha256": effective_sha,
        "effective_prompt_bytes": len(encoded) if encoded is not None else None,
        "adapter_name": "codex_isolated.py",
        "adapter_version": "1",
        "app_server_client_name": "highambench-isolated",
        "app_server_client_version": "1",
        "elapsed_clock": "CLOCK_MONOTONIC",
    }
    if not isinstance(root_thread_id, str) or not root_thread_id:
        errors.append(f"final run {label} prompt release lacks a rooted usage ledger")

    records: dict[str, Mapping[str, Any]] = {}
    artifact_syntax_ok = True
    for descriptor_name, (hash_field, kind, suffix) in PROMPT_RELEASE_ARTIFACTS.items():
        path_name = "release" if descriptor_name == "released" else descriptor_name
        descriptor = top.get(descriptor_name)
        artifact_label = f"final run {label} prompt {descriptor_name} artifact"
        record = descriptor.get("record") if isinstance(descriptor, Mapping) else None
        expected_record_fields = set(PROMPT_RELEASE_COMMON_FIELDS)
        if descriptor_name == "ready":
            expected_record_fields.update(
                {"kind", "turn_start_write_state", "ready_at_monotonic_ns", "ready_at_unix_ns"}
            )
        elif descriptor_name == "go":
            expected_record_fields.update(
                {
                    "kind",
                    "ready_sha256",
                    "turn_start_write_authorized",
                    "authorized_at_monotonic_ns",
                    "authorized_at_unix_ns",
                }
            )
        else:
            expected_record_fields.update(
                {
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
                }
            )
        expected_record_fields.add(hash_field)
        if (
            not isinstance(descriptor, Mapping)
            or set(descriptor) != {"path", "file_sha256", "record_sha256", "record"}
            or not isinstance(descriptor.get("path"), str)
            or not Path(descriptor.get("path", "")).is_absolute()
            or not descriptor.get("path", "").endswith(suffix)
            or descriptor.get("path") != artifact_paths.get(path_name)
            or not _hex_digest(descriptor.get("file_sha256"))
            or not _hex_digest(descriptor.get("record_sha256"))
            or not isinstance(record, Mapping)
            or set(record) != expected_record_fields
            or record.get(hash_field) != descriptor.get("record_sha256")
            or _canonical_record_sha256(record, hash_field) != record.get(hash_field)
            or any(record.get(field) != value for field, value in expected_common.items())
            or record.get("kind") != kind
        ):
            errors.append(f"{artifact_label} has invalid authenticated structure")
            artifact_syntax_ok = False
            continue
        records[descriptor_name] = record
        if repository_root is None:
            continue
        path = _barrier_artifact_path(
            descriptor.get("path"),
            repository_root=repository_root,
            label=artifact_label,
            errors=errors,
        )
        if path is None:
            artifact_syntax_ok = False
            continue
        try:
            payload = path.read_bytes()
        except OSError as error:
            errors.append(f"cannot reread {artifact_label}: {error}")
            artifact_syntax_ok = False
            continue
        canonical = (
            json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        if (
            payload != canonical
            or hashlib.sha256(payload).hexdigest() != descriptor.get("file_sha256")
        ):
            errors.append(f"{artifact_label} failed canonical retained-file authentication")
            artifact_syntax_ok = False

    ready = records.get("ready", {})
    go = records.get("go", {})
    released = records.get("released", {})
    timestamp_fields = (
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
        for value in timestamp_fields
    ):
        errors.append(f"final run {label} prompt-release timestamps are invalid")
    elif not (
        timestamp_fields[0] <= timestamp_fields[2] <= timestamp_fields[4] <= timestamp_fields[6]
        and timestamp_fields[5] <= timestamp_fields[7]
    ):
        errors.append(f"final run {label} prompt-release timestamp order is invalid")
    if records:
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
            errors.append(f"final run {label} prompt-release chain is inconsistent")
        if encoded is not None and isinstance(root_thread_id, str) and isinstance(agent, Mapping):
            wire = _prompt_turn_start_wire(
                prompt=effective_prompt,
                root_thread_id=root_thread_id,
                model=str(agent.get("model")),
                reasoning_effort=str(agent.get("reasoning_effort")),
            )
            if (
                released.get("turn_start_request_sha256")
                != hashlib.sha256(wire).hexdigest()
                or released.get("turn_start_request_bytes") != len(wire)
            ):
                errors.append(f"final run {label} released the wrong turn/start wire")

    release_mono = released.get("released_at_monotonic_ns")
    deadline_ns = (
        release_mono + int(float(wall_limit) * 1_000_000_000)
        if isinstance(release_mono, int)
        and not isinstance(release_mono, bool)
        and wall_limit is not None
        else None
    )
    first_valid = run.get("first_valid_seconds")
    actual_stop = run.get("actual_stop_seconds")
    if "authenticated CLOCK_MONOTONIC turn/start write" not in str(
        run.get("time_measurement")
    ):
        errors.append(f"final run {label} does not name its authenticated timing origin")
    if run.get("pass") is True:
        if (
            not isinstance(first_valid, (int, float))
            or isinstance(first_valid, bool)
            or first_valid < 0
            or wall_limit is None
            or first_valid >= wall_limit
            or run.get("scored_elapsed_seconds") != first_valid
        ):
            errors.append(f"passing run {label} has invalid release-based elapsed time")
    elif first_valid is not None:
        errors.append(f"failed run {label} records a first-valid elapsed time")
    if (
        isinstance(actual_stop, (int, float))
        and not isinstance(actual_stop, bool)
        and isinstance(first_valid, (int, float))
        and not isinstance(first_valid, bool)
        and actual_stop < first_valid
    ):
        errors.append(f"final run {label} stops before its first valid proof")

    ultra_timing_verified = False
    frozen = config.get("frozen_environment")
    is_ultra = (
        isinstance(frozen, Mapping)
        and frozen.get("model_reasoning_effort") == "ultra"
    )
    if is_ultra and run.get("pass") is True:
        boundary = usage.get("submission_boundary") if isinstance(usage, Mapping) else None
        boundary_published = (
            boundary.get("request_published_at_monotonic_ns")
            if isinstance(boundary, Mapping)
            else None
        )
        outer_exec_started = (
            boundary.get("outer_raw_item_observed_at_monotonic_ns")
            if isinstance(boundary, Mapping)
            else None
        )
        published: Any = None
        ultra_summary = run.get("ultra_submission_boundary")
        ultra_artifacts = (
            ultra_summary.get("artifacts")
            if isinstance(ultra_summary, Mapping)
            else None
        )
        request_descriptor = (
            ultra_artifacts.get("request")
            if isinstance(ultra_artifacts, Mapping)
            else None
        )
        if repository_root is None:
            errors.append(
                f"passing Ultra run {label} cannot reauthenticate request publication "
                "without the repository/results root"
            )
        elif not isinstance(request_descriptor, Mapping):
            errors.append(
                f"passing Ultra run {label} lacks its retained submission request"
            )
        else:
            request_path = _barrier_artifact_path(
                request_descriptor.get("path"),
                repository_root=repository_root,
                label=f"passing Ultra run {label} publication request artifact",
                errors=errors,
            )
            if request_path is not None:
                try:
                    request_payload = request_path.read_bytes()
                    parsed_request = json.loads(request_payload)
                except (OSError, UnicodeError, json.JSONDecodeError) as error:
                    errors.append(
                        f"passing Ultra run {label} cannot authenticate request publication: {error}"
                    )
                else:
                    canonical_request = (
                        json.dumps(
                            parsed_request,
                            sort_keys=True,
                            separators=(",", ":"),
                            ensure_ascii=False,
                        )
                        + "\n"
                    ).encode("utf-8")
                    if (
                        not isinstance(parsed_request, Mapping)
                        or not _hex_digest(request_descriptor.get("file_sha256"))
                        or hashlib.sha256(request_payload).hexdigest()
                        != request_descriptor.get("file_sha256")
                        or parsed_request.get("request_sha256")
                        != request_descriptor.get("record_sha256")
                        or parsed_request.get("request_sha256")
                        != boundary.get("request_sha256")
                        or _canonical_record_sha256(parsed_request, "request_sha256")
                        != parsed_request.get("request_sha256")
                        or request_payload != canonical_request
                    ):
                        errors.append(
                            f"passing Ultra run {label} retained request publication is unauthenticated"
                        )
                    else:
                        published = parsed_request.get(
                            "request_published_at_monotonic_ns"
                        )
                        if (
                            published != boundary_published
                            or parsed_request.get("request_published_at_unix_ns")
                            != boundary.get("request_published_at_unix_ns")
                        ):
                            errors.append(
                                f"passing Ultra run {label} request publication disagrees "
                                "with its usage boundary"
                            )
        if (
            not isinstance(published, int)
            or isinstance(published, bool)
            or not isinstance(release_mono, int)
            or isinstance(release_mono, bool)
            or not isinstance(outer_exec_started, int)
            or isinstance(outer_exec_started, bool)
            or outer_exec_started < release_mono
            or outer_exec_started > published
            or published < release_mono
            or deadline_ns is None
            or published >= deadline_ns
        ):
            errors.append(
                f"passing Ultra run {label} has invalid release-to-publication timing"
            )
        else:
            derived = round((published - release_mono) / 1_000_000_000, 6)
            if first_valid != derived:
                errors.append(
                    f"passing Ultra run {label} first-valid time is not request publication"
                )
            else:
                ultra_timing_verified = True

    protocol = run.get("protocol")
    verified = protocol.get("verified") if isinstance(protocol, Mapping) else None
    if (
        not isinstance(verified, Mapping)
        or verified.get("authenticated_prompt_release") is not True
    ):
        errors.append(f"final run {label} protocol does not verify prompt release")
    valid = len(errors) == error_count
    return {
        "run_id": label,
        "valid": valid,
        "artifact_set_count": 1,
        "artifact_file_count": len(PROMPT_RELEASE_ARTIFACTS),
        "artifact_content_verified": repository_root is not None and artifact_syntax_ok,
        "released_at_monotonic_ns": release_mono,
        "measurement_deadline_monotonic_ns": deadline_ns,
        "ultra_request_publication_timing_verified": (
            ultra_timing_verified if is_ultra and run.get("pass") is True else None
        ),
    }


def _check_ultra_outcome_boundary(
    run: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
    *,
    repository_root: Path | None,
) -> dict[str, Any] | None:
    """Validate the mutually exclusive exact Ultra pass/failure boundaries.

    A pass is exact after one frozen outer code-mode ``exec`` raw item starts
    the authenticated inner ``submit_proof`` dynamic call in the same provider
    response.  The inner call remains unanswered, every descendant is
    quiescent, and no later model response can occur.  A natural failure has no
    submission boundary and is exact only after the whole tree drains.  A
    TOKEN_LIMIT failure is the explicit exception: its tree may remain active,
    but only a sealed, sole-inflight sanitized provider-gate crossing with
    quiescent provider requests and immediate clean teardown is exact.
    """

    frozen = config.get("frozen_environment")
    if not isinstance(frozen, Mapping) or frozen.get("model_reasoning_effort") != "ultra":
        return None
    usage = run.get("token_usage")
    if not isinstance(usage, Mapping) or usage.get("usage_scope") != TOKEN_USAGE_SCOPE:
        return None

    label = str(run.get("run_id"))
    passed = run.get("pass") is True
    root_thread_id = usage.get("root_thread_id")
    active = usage.get("active_thread_ids")
    unresolved = usage.get("unresolved_thread_ids")
    invalid = usage.get("invalid_reasons")
    protocol = run.get("protocol")
    verified = protocol.get("verified") if isinstance(protocol, Mapping) else None
    protocol_boundary = (
        verified.get("authenticated_first_valid_proof_boundary")
        if isinstance(verified, Mapping)
        else None
    )
    summary = run.get("ultra_submission_boundary")
    boundary = usage.get("submission_boundary")
    measurement = run.get("token_measurement")
    capture = measurement.get("capture_grace") if isinstance(measurement, Mapping) else None
    clean_adapter_exit = (
        type(run.get("agent_exit_code")) is int
        and run.get("agent_exit_code") == 0
    )
    if not clean_adapter_exit:
        errors.append(f"Ultra run {label} does not have a clean adapter exit")

    if not passed and run.get("failure_code") == "TOKEN_LIMIT":
        gate = usage.get("provider_token_gate")
        terminal = gate.get("terminal") if isinstance(gate, Mapping) else None
        gate_crossing = (
            terminal.get("crossing") if isinstance(terminal, Mapping) else None
        )
        first_crossing = usage.get("first_crossing")
        teardown = usage.get("adapter_teardown")
        exact_crossing = not (
            not clean_adapter_exit
            or usage.get("measurement_exact") is not True
            or usage.get("drain_complete") is not False
            or usage.get("tree_quiescent") is not False
            or invalid != []
            or usage.get("submission_boundary_exact") is not False
            or boundary is not None
            or usage.get("stop_reason") != "token_limit"
            or usage.get("interrupt_requested") is not False
            or not isinstance(first_crossing, Mapping)
            or not isinstance(terminal, Mapping)
            or terminal.get("phase") != "CLOSED"
            or terminal.get("close_reason") != "token_limit"
            or terminal.get("open_request_ids") != []
            or terminal.get("all_complete") is not True
            or terminal.get("poisoned") is not False
            or not isinstance(gate_crossing, Mapping)
            or gate_crossing.get("request_kind") not in {"turn", "compaction"}
            or gate_crossing.get("response_id") != first_crossing.get("response_id")
            or gate_crossing.get("completed_tokens") != first_crossing.get("tokens")
            or gate_crossing.get("sole_inflight") is not True
            or gate_crossing.get("release_kind")
            != (
                ultra_canary.runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
                if gate_crossing.get("request_kind") == "compaction"
                else ultra_canary.runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE
            )
            or not isinstance(teardown, Mapping)
            or teardown.get("process_group_isolated") is not True
            or teardown.get("immediate") is not True
            or teardown.get("stdin_closed") is not True
            or teardown.get("completed") is not True
            or not isinstance(summary, Mapping)
            or dict(summary) != {"verified": False}
            or protocol_boundary is not False
            or not isinstance(measurement, Mapping)
            or measurement.get("tree_drain_complete") is not False
        )
        if not exact_crossing:
            errors.append(
                f"TOKEN_LIMIT Ultra run {label} lacks an exact sanitized provider-gate crossing"
            )
        return {
            "run_id": label,
            "outcome": (
                "exact_provider_gate_crossing"
                if exact_crossing
                else "invalid_token_limit_boundary"
            ),
            "artifact_set_count": 0,
            "artifact_file_count": 0,
            "artifact_content_verified": repository_root is not None,
        }

    if not passed:
        exact_failure = not (
            not clean_adapter_exit
            or run.get("failure_code") == "TIME_LIMIT"
            or usage.get("measurement_exact") is not True
            or usage.get("drain_complete") is not True
            or usage.get("tree_quiescent") is not True
            or active != []
            or unresolved != []
            or invalid != []
            or usage.get("submission_boundary_exact") is not False
            or boundary is not None
            or usage.get("interrupt_requested") is not False
            or not isinstance(summary, Mapping)
            or dict(summary) != {"verified": False}
            or protocol_boundary is not False
            or not isinstance(measurement, Mapping)
            or measurement.get("tree_drain_complete") is not True
        )
        if not exact_failure:
            errors.append(
                f"failed Ultra run {label} lacks an exact natural rooted-tree drain"
            )
        return {
            "run_id": label,
            "outcome": (
                "exact_natural_failure" if exact_failure else "invalid_failure_boundary"
            ),
            "artifact_set_count": 0,
            "artifact_file_count": 0,
            "artifact_content_verified": repository_root is not None,
        }

    if (
        not clean_adapter_exit
        or usage.get("measurement_exact") is not True
        or usage.get("drain_complete") is not False
        or usage.get("tree_quiescent") is not False
        or not isinstance(root_thread_id, str)
        or not root_thread_id
        or active != [root_thread_id]
        or unresolved != []
        or invalid != []
        or usage.get("submission_boundary_exact") is not True
        or usage.get("stop_reason") != "first_valid_proof"
        or usage.get("interrupt_requested") is not False
        or usage.get("first_crossing") is not None
        or not isinstance(boundary, Mapping)
    ):
        errors.append(
            f"passing Ultra run {label} lacks an exact authenticated submission boundary"
        )
        return {
            "run_id": label,
            "outcome": "invalid_pass_boundary",
            "artifact_set_count": 0,
            "artifact_file_count": 0,
            "artifact_content_verified": False,
        }

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
        errors.append(
            f"passing Ultra run {label} lacks its authenticated provider-gate close"
        )

    required_true = (
        "authenticated",
        "exact",
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
        "outer_raw_item_observed_before_inner_dynamic_call",
        "inner_dynamic_call_left_blocked",
    )
    boundary_identity_fields = (
        "challenge_sha256",
        "call_sha256",
        "request_sha256",
        "ack_sha256",
        "validator_contract_sha256",
        "candidate_sha256",
    )
    response_ids = usage.get("response_ids")
    if (
        not _valid_nested_submission_wire(boundary)
        or not _valid_submission_event_order(
            boundary, derive_from_timestamps=False
        )
        or boundary.get("status") != "accepted"
        or any(boundary.get(field) is not True for field in required_true)
        or boundary.get("inner_dynamic_tool_response_sent") is not False
        or boundary.get("outer_exec_output_emitted") is not False
        or boundary.get("later_model_response_possible") is not False
        or boundary.get("current_response_cumulative_required") is not False
        or boundary.get("thread_id") != root_thread_id
        or not isinstance(response_ids, list)
        or boundary.get("response_id") not in response_ids
        or boundary.get("candidate_path") != "Candidate.lean"
        or not isinstance(boundary.get("sequence"), int)
        or isinstance(boundary.get("sequence"), bool)
        or boundary.get("sequence") <= 0
        or not isinstance(boundary.get("candidate_size_bytes"), int)
        or isinstance(boundary.get("candidate_size_bytes"), bool)
        or boundary.get("candidate_size_bytes") <= 0
        or any(not _hex_digest(boundary.get(field)) for field in boundary_identity_fields)
        or protocol_boundary is not True
        or not isinstance(measurement, Mapping)
        or measurement.get("tree_drain_complete") is not False
        or not isinstance(capture, Mapping)
        or capture.get("freshness_basis")
        != ULTRA_PASS_FRESHNESS_BASIS
        or capture.get("ultra_tree_drain") is not False
        or capture.get("ultra_submission_boundary") is not True
        or capture.get("captured_notification_sequence")
        != usage.get("notification_sequence")
        or run.get("time_measurement") != ULTRA_PASS_TIME_MEASUREMENT
    ):
        errors.append(f"passing Ultra run {label} has malformed boundary evidence")

    if (
        not isinstance(summary, Mapping)
        or summary.get("verified") is not True
        or summary.get("sequence") != boundary.get("sequence")
        or summary.get("request_sha256") != boundary.get("request_sha256")
        or summary.get("ack_sha256") != boundary.get("ack_sha256")
    ):
        errors.append(f"passing Ultra run {label} has a stale top-level boundary summary")
        artifacts: Any = None
    else:
        artifacts = summary.get("artifacts")
    if not isinstance(artifacts, Mapping) or set(artifacts) != set(
        SUBMISSION_BARRIER_ARTIFACTS
    ):
        errors.append(f"passing Ultra run {label} lacks the retained barrier artifact set")
        return {
            "run_id": label,
            "outcome": "authenticated_pass_boundary",
            "artifact_set_count": 0,
            "artifact_file_count": 0,
            "artifact_content_verified": False,
        }

    artifact_records: dict[str, Mapping[str, Any]] = {}
    snapshot_bytes: bytes | None = None
    syntax_ok = True
    for artifact_name in SUBMISSION_BARRIER_ARTIFACTS:
        descriptor = artifacts.get(artifact_name)
        artifact_label = f"passing Ultra run {label} {artifact_name} artifact"
        if not isinstance(descriptor, Mapping) or not _hex_digest(
            descriptor.get("file_sha256")
        ):
            errors.append(f"{artifact_label} has an invalid descriptor")
            syntax_ok = False
            continue
        if artifact_name == "snapshot":
            if (
                descriptor.get("file_sha256") != boundary.get("candidate_sha256")
                or descriptor.get("size_bytes") != boundary.get("candidate_size_bytes")
            ):
                errors.append(f"{artifact_label} does not bind the accepted candidate")
                syntax_ok = False
        else:
            hash_field, _kind = SUBMISSION_BARRIER_RECORD_FIELDS[artifact_name]
            if descriptor.get("record_sha256") != boundary.get(hash_field):
                errors.append(f"{artifact_label} does not bind the accepted boundary")
                syntax_ok = False
        if repository_root is None:
            continue
        path = _barrier_artifact_path(
            descriptor.get("path"),
            repository_root=repository_root,
            label=artifact_label,
            errors=errors,
        )
        if path is None:
            syntax_ok = False
            continue
        try:
            payload = path.read_bytes()
        except OSError as error:
            errors.append(f"cannot reread {artifact_label}: {error}")
            syntax_ok = False
            continue
        if hashlib.sha256(payload).hexdigest() != descriptor.get("file_sha256"):
            errors.append(f"{artifact_label} failed retained SHA-256 verification")
            syntax_ok = False
            continue
        if artifact_name == "snapshot":
            snapshot_bytes = payload
            if len(payload) != descriptor.get("size_bytes"):
                errors.append(f"{artifact_label} changed size")
                syntax_ok = False
            continue
        hash_field, kind = SUBMISSION_BARRIER_RECORD_FIELDS[artifact_name]
        try:
            record = json.loads(payload)
        except (UnicodeError, json.JSONDecodeError) as error:
            errors.append(f"{artifact_label} is not valid JSON: {error}")
            syntax_ok = False
            continue
        if (
            not isinstance(record, Mapping)
            or record.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
            or record.get("kind") != kind
            or record.get(hash_field) != descriptor.get("record_sha256")
            or _canonical_record_sha256(record, hash_field) != record.get(hash_field)
        ):
            errors.append(f"{artifact_label} failed authenticated-record verification")
            syntax_ok = False
            continue
        artifact_records[artifact_name] = record

    if repository_root is not None and syntax_ok:
        challenge = artifact_records.get("challenge", {})
        call = artifact_records.get("call", {})
        request = artifact_records.get("request", {})
        ack = artifact_records.get("ack", {})
        wire_identity_fields = (
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
        )
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
        event_order_fields = (
            "submission_event_order",
            "dynamic_call_observed_before_raw_response_completed",
            "raw_response_completed_before_dynamic_call_observed",
        )
        if (
            not _valid_nested_submission_wire(call)
            or not _valid_nested_submission_wire(request)
            or any(
                challenge.get(field) != expected
                for field, expected in NESTED_SUBMISSION_EXEC_YIELD_RECORD.items()
            )
            or not _valid_submission_event_order(
                request, derive_from_timestamps=True
            )
            or not _valid_submission_event_order(
                boundary, derive_from_timestamps=False
            )
            or challenge.get("challenge_sha256") != boundary.get("challenge_sha256")
            or call.get("call_sha256") != boundary.get("call_sha256")
            or request.get("request_sha256") != boundary.get("request_sha256")
            or ack.get("ack_sha256") != boundary.get("ack_sha256")
            or call.get("challenge_sha256") != challenge.get("challenge_sha256")
            or request.get("challenge_sha256") != challenge.get("challenge_sha256")
            or request.get("call_sha256") != call.get("call_sha256")
            or ack.get("request_sha256") != request.get("request_sha256")
            or ack.get("candidate_sha256") != request.get("candidate_sha256")
            or ack.get("decision") != "accept"
            or request.get("candidate_path") != "Candidate.lean"
            or request.get("candidate_sha256") != boundary.get("candidate_sha256")
            or request.get("candidate_size_bytes") != boundary.get("candidate_size_bytes")
            or request.get("request_published_at_monotonic_ns")
            != boundary.get("request_published_at_monotonic_ns")
            or request.get("request_published_at_unix_ns")
            != boundary.get("request_published_at_unix_ns")
            or any(
                call.get(field) != request.get(field)
                or request.get(field) != boundary.get(field)
                for field in wire_identity_fields
            )
            or any(
                request.get(field) is not True
                or boundary.get(field) is not True
                for field in request_truth_flags
            )
            or any(
                request.get(field) != boundary.get(field)
                for field in event_order_fields
            )
            or any(
                challenge.get(field) != boundary.get(field)
                or call.get(field) != boundary.get(field)
                or request.get(field) != boundary.get(field)
                for field in (
                    "attempt_nonce",
                    "run_id",
                    "validator_contract_sha256",
                    *NESTED_SUBMISSION_EXEC_YIELD_RECORD,
                )
            )
            or snapshot_bytes is None
            or hashlib.sha256(snapshot_bytes).hexdigest()
            != boundary.get("candidate_sha256")
        ):
            errors.append(f"passing Ultra run {label} retained barrier chain is inconsistent")
            syntax_ok = False

    submission_digest = run.get("submission_sha256")
    final_digest = run.get("final_submission_sha256")
    if (
        submission_digest != boundary.get("candidate_sha256")
        or final_digest != submission_digest
        or run.get("submission_changed_after_acceptance") is not False
    ):
        errors.append(f"passing Ultra run {label} changed its accepted candidate")

    return {
        "run_id": label,
        "outcome": "authenticated_pass_boundary",
        "artifact_set_count": 1,
        "artifact_file_count": len(SUBMISSION_BARRIER_ARTIFACTS),
        "artifact_content_verified": repository_root is not None and syntax_ok,
    }


def _check_token_usage(
    run: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
) -> None:
    """Check cached-inclusive usage and the schema's exact limit accounting."""

    label = str(run.get("run_id"))
    usage = run.get("token_usage")
    token_fields = (
        "input_tokens",
        "cached_input_tokens",
        "output_tokens",
        "model_tokens",
    )
    if not isinstance(usage, Mapping) or any(
        not isinstance(usage.get(field), int)
        or isinstance(usage.get(field), bool)
        or usage.get(field) < 0
        for field in token_fields
    ):
        errors.append(f"final run {label} lacks exact model-token usage")
        return

    if usage["cached_input_tokens"] > usage["input_tokens"]:
        errors.append(f"final run {label} has cached input above total input")
    if usage["model_tokens"] != usage["input_tokens"] + usage["output_tokens"]:
        errors.append(f"final run {label} has inconsistent total model-token usage")

    measurement_source = usage.get("measurement_source")
    usage_scope = usage.get("usage_scope")
    ultra = (
        measurement_source == TOKEN_USAGE_MEASUREMENT_SOURCE
        or usage_scope == TOKEN_USAGE_SCOPE
    )
    legacy = (
        measurement_source == LEGACY_TOKEN_USAGE_MEASUREMENT_SOURCE
        and usage_scope in (None, LEGACY_TOKEN_USAGE_SCOPE)
    )
    if not ultra and not legacy:
        errors.append(f"final run {label} lacks a recognized Codex token-usage schema")
        return
    if ultra and (
        measurement_source != TOKEN_USAGE_MEASUREMENT_SOURCE
        or usage_scope != TOKEN_USAGE_SCOPE
    ):
        errors.append(f"final run {label} mixes Ultra token-usage schemas")
    configured_control = config.get("token_control")
    configured_scope = (
        configured_control.get("usage_scope")
        if isinstance(configured_control, Mapping)
        else None
    )
    expected_scope = TOKEN_USAGE_SCOPE if ultra else LEGACY_TOKEN_USAGE_SCOPE
    if configured_scope != expected_scope:
        errors.append(
            f"final run {label} token usage disagrees with the frozen token-control schema"
        )

    call_count = usage.get("call_count")
    sequence = usage.get("notification_sequence")
    if ultra:
        frozen = config.get("frozen_environment")
        authenticated_ultra = (
            isinstance(frozen, Mapping)
            and frozen.get("model_reasoning_effort") == "ultra"
        )
        authenticated_pass_boundary = authenticated_ultra and run.get("pass") is True
        authenticated_token_crossing = (
            authenticated_ultra
            and run.get("pass") is False
            and run.get("failure_code") == "TOKEN_LIMIT"
        )
        extra_fields = (
            "cache_write_input_tokens",
            "reasoning_output_tokens",
        )
        if any(
            not isinstance(usage.get(field), int)
            or isinstance(usage.get(field), bool)
            or usage.get(field) < 0
            for field in extra_fields
        ):
            errors.append(f"final run {label} lacks exact Ultra token breakdowns")
        elif (
            usage["cache_write_input_tokens"] > usage["input_tokens"]
            or usage["reasoning_output_tokens"] > usage["output_tokens"]
        ):
            errors.append(f"final run {label} has inconsistent Ultra token breakdowns")
        provider_totals = {
            "input_tokens": usage.get("input_tokens"),
            "cached_input_tokens": usage.get("cached_input_tokens"),
            "cache_write_input_tokens": usage.get("cache_write_input_tokens"),
            "output_tokens": usage.get("output_tokens"),
            "reasoning_output_tokens": usage.get("reasoning_output_tokens"),
            "total_tokens": usage.get("model_tokens"),
        }
        try:
            reconciliation = run_matrix.verify_provider_usage_reconciliation(
                usage.get("provider_usage_reconciliation"),
                expected_provider_usage=provider_totals,
                expected_provider_response_ids=usage.get("response_ids"),
                expected_thread_accounting=usage.get("thread_accounting"),
                expected_root_thread_id=usage.get("root_thread_id"),
                expected_appserver_response_ledger=usage.get(
                    "appserver_response_ledger"
                ),
            )
        except BenchmarkToolError as error:
            errors.append(
                f"final run {label} has invalid provider/app-server reconciliation: {error}"
            )
            reconciliation = None
        if reconciliation is not None and (
            usage.get("provider_response_count")
            != reconciliation["provider_response_count"]
            or usage.get("provider_response_ids")
            != reconciliation["provider_response_ids"]
            or usage.get("provider_usage") != reconciliation["provider_usage"]
            or usage.get("appserver_response_count")
            != reconciliation["appserver_response_count"]
            or usage.get("appserver_response_ids")
            != reconciliation["appserver_response_ids"]
            or usage.get("appserver_usage") != reconciliation["appserver_usage"]
            or usage.get("suppressed_collaboration_wait_response_count")
            != reconciliation["suppressed_collaboration_wait_response_count"]
            or usage.get("suppressed_collaboration_wait_response_ids")
            != reconciliation["suppressed_collaboration_wait_response_ids"]
            or usage.get("suppressed_collaboration_wait_usage")
            != reconciliation["suppressed_collaboration_wait_usage"]
            or usage.get("suppressed_collaboration_wait_evidence")
            != reconciliation["suppressed_collaboration_wait_evidence"]
            or usage.get("superseded_by_collaboration_message_response_count")
            != reconciliation[
                "superseded_by_collaboration_message_response_count"
            ]
            or usage.get("superseded_by_collaboration_message_response_ids")
            != reconciliation[
                "superseded_by_collaboration_message_response_ids"
            ]
            or usage.get("superseded_by_collaboration_message_usage")
            != reconciliation["superseded_by_collaboration_message_usage"]
            or usage.get("superseded_by_collaboration_message_evidence")
            != reconciliation[
                "superseded_by_collaboration_message_evidence"
            ]
            or usage.get(
                "discarded_after_explicit_child_interrupt_response_count"
            )
            != reconciliation[
                "discarded_after_explicit_child_interrupt_response_count"
            ]
            or usage.get(
                "discarded_after_explicit_child_interrupt_response_ids"
            )
            != reconciliation[
                "discarded_after_explicit_child_interrupt_response_ids"
            ]
            or usage.get("discarded_after_explicit_child_interrupt_usage")
            != reconciliation[
                "discarded_after_explicit_child_interrupt_usage"
            ]
            or usage.get("discarded_after_explicit_child_interrupt_evidence")
            != reconciliation[
                "discarded_after_explicit_child_interrupt_evidence"
            ]
            or usage.get("notification_sequence")
            != reconciliation["appserver_response_count"]
            or not isinstance(usage.get("appserver_response_ledger"), list)
            or len(usage.get("appserver_response_ledger"))
            != reconciliation["appserver_response_count"]
            or [
                item.get("response_id") if isinstance(item, Mapping) else None
                for item in usage.get("appserver_response_ledger")
            ]
            != reconciliation["appserver_response_ids"]
        ):
            errors.append(
                f"final run {label} has inconsistent provider/app-server aliases"
            )
        thread_count = usage.get("thread_count")
        if (
            not isinstance(thread_count, int)
            or isinstance(thread_count, bool)
            or thread_count <= 0
        ):
            errors.append(f"final run {label} has no rooted thread-tree count")
        if (
            not isinstance(call_count, int)
            or isinstance(call_count, bool)
            or call_count <= 0
            or usage.get("response_count") != call_count
            or usage.get("provider_response_count") != call_count
            or usage.get("response_id_deduplicated") is not True
        ):
            errors.append(
                f"final run {label} has inconsistent deduplicated response accounting"
            )
        if usage.get("notification") != TOKEN_LIMIT_NOTIFICATION:
            errors.append(f"final run {label} has the wrong Ultra usage notification")
        root_thread_id = usage.get("root_thread_id")
        if not isinstance(root_thread_id, str) or not root_thread_id:
            errors.append(f"final run {label} has no rooted Ultra thread tree")
        active = usage.get("active_thread_ids")
        unresolved = usage.get("unresolved_thread_ids")
        invalid_reasons = usage.get("invalid_reasons")
        if not all(
            isinstance(values, list)
            and all(isinstance(item, str) and item for item in values)
            and len(values) == len(set(values))
            for values in (active, unresolved, invalid_reasons)
        ):
            errors.append(f"final run {label} has malformed Ultra tree-lifecycle evidence")
        if authenticated_pass_boundary:
            if (
                usage.get("drain_complete") is not False
                or usage.get("measurement_exact") is not True
                or usage.get("tree_quiescent") is not False
                or active != [root_thread_id]
                or unresolved != []
                or invalid_reasons != []
                or usage.get("submission_boundary_exact") is not True
            ):
                errors.append(
                    f"passing run {label} lacks an exact accepted Ultra boundary ledger"
                )
        elif authenticated_token_crossing:
            gate = usage.get("provider_token_gate")
            terminal = gate.get("terminal") if isinstance(gate, Mapping) else None
            first_crossing = usage.get("first_crossing")
            gate_crossing = (
                terminal.get("crossing") if isinstance(terminal, Mapping) else None
            )
            teardown = usage.get("adapter_teardown")
            if (
                usage.get("drain_complete") is not False
                or usage.get("measurement_exact") is not True
                or usage.get("tree_quiescent") is not False
                or invalid_reasons != []
                or usage.get("submission_boundary_exact") is not False
                or usage.get("submission_boundary") is not None
                or usage.get("stop_reason") != "token_limit"
                or not isinstance(first_crossing, Mapping)
                or not isinstance(terminal, Mapping)
                or terminal.get("phase") != "CLOSED"
                or terminal.get("close_reason") != "token_limit"
                or terminal.get("open_request_ids") != []
                or terminal.get("all_complete") is not True
                or terminal.get("poisoned") is not False
                or not isinstance(gate_crossing, Mapping)
                or gate_crossing.get("request_kind") not in {"turn", "compaction"}
                or gate_crossing.get("response_id")
                != first_crossing.get("response_id")
                or gate_crossing.get("completed_tokens")
                != first_crossing.get("tokens")
                or gate_crossing.get("sole_inflight") is not True
                or gate_crossing.get("release_kind")
                != (
                    ultra_canary.runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
                    if gate_crossing.get("request_kind") == "compaction"
                    else ultra_canary.runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE
                )
                or not isinstance(teardown, Mapping)
                or teardown.get("process_group_isolated") is not True
                or teardown.get("immediate") is not True
                or teardown.get("stdin_closed") is not True
                or teardown.get("completed") is not True
            ):
                errors.append(
                    f"TOKEN_LIMIT run {label} lacks an exact provider-gate crossing ledger"
                )
        elif (
            usage.get("drain_complete") is not True
            or usage.get("measurement_exact") is not True
            or usage.get("tree_quiescent") is not True
            or active != []
            or unresolved != []
            or invalid_reasons != []
            or (authenticated_ultra and usage.get("submission_boundary_exact") is not False)
        ):
            errors.append(
                f"final run {label} lacks an exact, naturally drained Ultra tree ledger"
            )
        if authenticated_ultra:
            response_ids = usage.get("response_ids")
            if (
                not isinstance(response_ids, list)
                or len(response_ids) != call_count
                or any(not isinstance(item, str) or not item for item in response_ids)
                or len(response_ids) != len(set(response_ids))
            ):
                errors.append(f"final run {label} has a malformed Ultra response-ID ledger")
        if usage.get("interrupt_requested") is not False:
            errors.append(
                f"final run {label} cannot claim exact Ultra usage after interruption"
            )
    elif (
        not isinstance(call_count, int)
        or isinstance(call_count, bool)
        or call_count != 1
    ):
        errors.append(f"final run {label} is not one atomic cumulative usage snapshot")

    limits = config.get("limits")
    token_limit = limits.get("total_model_tokens") if isinstance(limits, Mapping) else None
    if (
        not isinstance(token_limit, int)
        or isinstance(token_limit, bool)
        or token_limit <= 0
    ):
        # The surrounding metadata checks report the malformed limit.  There is no
        # meaningful threshold against which to check this record.
        return

    model_tokens = usage["model_tokens"]
    at_or_above_limit = model_tokens >= token_limit
    passed = run.get("pass")
    failure = run.get("failure_code")
    limit_outcome = passed is False and failure in ("TIME_LIMIT", "TOKEN_LIMIT")

    if at_or_above_limit and not limit_outcome:
        errors.append(
            f"final run {label} reached or exceeded the fixed model-token limit "
            "without pass=false and failure_code=TIME_LIMIT or TOKEN_LIMIT"
        )
    if failure == "TOKEN_LIMIT" and not at_or_above_limit:
        errors.append(
            f"final TOKEN_LIMIT run {label} has model-token usage below the fixed limit"
        )

    # Observation status may relax unavailable backend controls, but it never
    # relaxes token measurement.  Ultra records use a response-ID-deduplicated
    # completed-response ledger; legacy records use one cumulative root-thread
    # notification and remain valid only with legacy frozen metadata.
    if usage.get("live_cumulative") is not True:
        errors.append(f"final run {label} does not mark token usage live and cumulative")
    if usage.get("input_includes_cached") is not True:
        errors.append(
            f"final run {label} does not use cached-inclusive input-token accounting"
        )
    for field in ("notification_sequence", "observed_at_unix_ns"):
        value = usage.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            errors.append(f"final run {label} has invalid live token provenance field {field}")
    observed_at = usage.get("observed_at_unix_ns")
    started = _iso_time(run.get("started_at_utc"))
    finished = _iso_time(run.get("finished_at_utc"))
    if (
        isinstance(observed_at, int)
        and not isinstance(observed_at, bool)
        and started is not None
        and finished is not None
    ):
        started_ns = int(started.timestamp() * 1_000_000_000)
        finished_ns = int(finished.timestamp() * 1_000_000_000)
        if not (
            started_ns - TOKEN_TIMESTAMP_TOLERANCE_NS
            <= observed_at
            <= finished_ns + TOKEN_TIMESTAMP_TOLERANCE_NS
        ):
            errors.append(
                f"final run {label} token observation falls outside its run timestamps"
            )

    measurement = run.get("token_measurement")
    enforcement = (
        measurement.get("limit_enforcement")
        if isinstance(measurement, Mapping)
        else None
    )
    if not isinstance(enforcement, Mapping):
        errors.append(f"final run {label} lacks live token-limit enforcement evidence")
        return
    expected_measurement_source = (
        TOKEN_MEASUREMENT_SOURCE if ultra else LEGACY_TOKEN_MEASUREMENT_SOURCE
    )
    if (
        measurement.get("source") != expected_measurement_source
        or measurement.get("provider_cumulative_total_exact") is not True
        or measurement.get("cached_input_counted_once") is not True
        or measurement.get("measurement_error") is not None
    ):
        errors.append(f"final run {label} has invalid live token-measurement metadata")
    if ultra and (
        measurement.get("usage_scope") != TOKEN_USAGE_SCOPE
        or measurement.get("thread_count") != usage.get("thread_count")
        or measurement.get("response_count") != call_count
        or measurement.get("tree_drain_complete") is not usage.get("drain_complete")
    ):
        errors.append(
            f"final run {label} has inconsistent Ultra tree-measurement metadata"
        )
    if measurement.get("trusted_usage_path_outside_workspace") is not True:
        errors.append(f"final run {label} lacks a trusted external token-usage path")
    post_submission_usage = measurement.get("post_submission_usage_established")
    if not isinstance(post_submission_usage, bool):
        errors.append(
            f"final run {label} has no Boolean post-submission token-usage marker"
        )
    elif passed is True and post_submission_usage is not True:
        errors.append(
            f"passing run {label} lacks post-submission live token-usage evidence"
        )

    capture = measurement.get("capture_grace")
    if not isinstance(capture, Mapping):
        errors.append(f"final run {label} lacks structured token capture-grace evidence")
    else:
        capture_post_submission = capture.get("post_submission_usage_established")
        if (
            not isinstance(capture_post_submission, bool)
            or capture_post_submission is not post_submission_usage
        ):
            errors.append(
                f"final run {label} has contradictory post-submission usage evidence"
            )
        freshness_basis = capture.get("freshness_basis")
        captured_sequence = capture.get("captured_notification_sequence")
        if post_submission_usage is True:
            submission_detected = capture.get("submission_detected_at_unix_ns")
            if (
                not isinstance(submission_detected, int)
                or isinstance(submission_detected, bool)
                or submission_detected <= 0
                or freshness_basis not in POST_SUBMISSION_FRESHNESS_BASES
                or not isinstance(captured_sequence, int)
                or isinstance(captured_sequence, bool)
                or captured_sequence != usage.get("notification_sequence")
            ):
                errors.append(
                    f"final run {label} has invalid post-submission usage freshness evidence"
                )
            elif freshness_basis == (
                "trusted_notification_observed_at_or_after_submission_detection"
            ) and (
                not isinstance(observed_at, int)
                or isinstance(observed_at, bool)
                or observed_at < submission_detected
            ):
                errors.append(
                    f"final run {label} token observation predates submission detection"
                )
            elif freshness_basis == "newer_notification_sequence":
                baseline = capture.get("baseline_notification_sequence")
                if (
                    not isinstance(baseline, int)
                    or isinstance(baseline, bool)
                    or captured_sequence <= baseline
                ):
                    errors.append(
                        f"final run {label} lacks a newer post-submission usage update"
                    )
            elif ultra and freshness_basis not in (
                "ultra_tree_quiescence_with_final_ledger",
                ULTRA_PASS_FRESHNESS_BASIS,
            ):
                errors.append(f"final run {label} lacks an exact Ultra usage boundary")
            elif (
                ultra
                and freshness_basis
                == ULTRA_PASS_FRESHNESS_BASIS
                and (
                    usage.get("submission_boundary_exact") is not True
                    or usage.get("drain_complete") is not False
                    or capture.get("ultra_submission_boundary") is not True
                    or capture.get("ultra_tree_drain") is not False
                )
            ):
                errors.append(
                    f"final run {label} has inconsistent authenticated boundary freshness"
                )
            elif not ultra and freshness_basis == "ultra_tree_quiescence_with_final_ledger":
                errors.append(
                    f"final run {label} gives legacy usage an Ultra freshness basis"
                )
            elif (
                freshness_basis == "clean_adapter_exit_with_final_usage"
                and capture.get("process_exited_during_grace") is not True
            ):
                errors.append(
                    f"final run {label} claims final usage without a clean adapter exit"
                )
        elif freshness_basis is not None or captured_sequence is not None:
            errors.append(
                f"final run {label} records freshness evidence without establishing usage"
            )

    expected_mode = (
        TOKEN_LIMIT_ENFORCEMENT_MODE
        if ultra
        else LEGACY_TOKEN_LIMIT_ENFORCEMENT_MODE
    )
    expected_notification = (
        TOKEN_LIMIT_NOTIFICATION if ultra else LEGACY_TOKEN_LIMIT_NOTIFICATION
    )
    if (
        enforcement.get("mode") != expected_mode
        or enforcement.get("notification") != expected_notification
        or not isinstance(enforcement.get("configured_limit_tokens"), int)
        or isinstance(enforcement.get("configured_limit_tokens"), bool)
        or enforcement.get("configured_limit_tokens") != token_limit
        or enforcement.get("checked_before_submission_validation") is not True
        or enforcement.get("one_response_overshoot_possible") is not True
        or (
            ultra
            and enforcement.get("concurrent_inflight_overshoot_possible") is not False
        )
        or (
            not ultra
            and enforcement.get("concurrent_inflight_overshoot_possible")
            not in (None, False)
        )
    ):
        errors.append(f"final run {label} has invalid live token-limit enforcement metadata")

    first_crossing = usage.get("first_crossing") if ultra else None
    crossing_tokens: int | None = None
    if ultra and first_crossing is not None:
        crossing_tokens = (
            first_crossing.get("tokens")
            if isinstance(first_crossing, Mapping)
            else None
        )
        crossing_sequence = (
            first_crossing.get("notification_sequence")
            if isinstance(first_crossing, Mapping)
            else None
        )
        crossing_time = (
            first_crossing.get("observed_at_unix_ns")
            if isinstance(first_crossing, Mapping)
            else None
        )
        crossing_response = (
            first_crossing.get("response_id")
            if isinstance(first_crossing, Mapping)
            else None
        )
        crossing_active = (
            first_crossing.get("active_thread_ids")
            if isinstance(first_crossing, Mapping)
            else None
        )
        if (
            not isinstance(crossing_tokens, int)
            or isinstance(crossing_tokens, bool)
            or not token_limit <= crossing_tokens <= model_tokens
            or not isinstance(crossing_sequence, int)
            or isinstance(crossing_sequence, bool)
            or not 1 <= crossing_sequence <= call_count
            or not isinstance(crossing_time, int)
            or isinstance(crossing_time, bool)
            or crossing_time <= 0
            or (
                isinstance(observed_at, int)
                and not isinstance(observed_at, bool)
                and crossing_time > observed_at
            )
            or not isinstance(crossing_response, str)
            or not crossing_response
            or not isinstance(crossing_active, list)
            or any(not isinstance(item, str) or not item for item in crossing_active)
            or len(crossing_active) != len(set(crossing_active))
            or usage.get("stop_reason") != "token_limit"
        ):
            errors.append(f"final run {label} has an invalid first Ultra threshold crossing")
    elif ultra and first_crossing is not None:
        errors.append(f"final run {label} has a malformed first Ultra threshold crossing")

    triggered = enforcement.get("triggered")
    expected_triggered = first_crossing is not None if ultra else at_or_above_limit
    if not isinstance(triggered, bool):
        errors.append(f"final run {label} has no Boolean token-limit trigger marker")
    elif triggered is not expected_triggered or expected_triggered is not at_or_above_limit:
        errors.append(
            f"final run {label} token-limit trigger disagrees with the first "
            "completed-response aggregate threshold crossing"
        )

    observed = enforcement.get("observed_tokens")
    expected_observed = crossing_tokens if ultra else model_tokens
    observed_is_valid = (
        isinstance(observed, int)
        and not isinstance(observed, bool)
        and isinstance(expected_observed, int)
        and not isinstance(expected_observed, bool)
        and observed == expected_observed
        if at_or_above_limit
        else "observed_tokens" in enforcement and observed is None
    )
    if not observed_is_valid:
        errors.append(f"final run {label} has inconsistent token-limit observed usage")
    overshoot = enforcement.get("overshoot_tokens")
    overshoot_is_valid = (
        isinstance(overshoot, int)
        and not isinstance(overshoot, bool)
        and isinstance(expected_observed, int)
        and not isinstance(expected_observed, bool)
        and overshoot == expected_observed - token_limit
        if at_or_above_limit
        else "overshoot_tokens" in enforcement and overshoot is None
    )
    if not overshoot_is_valid:
        errors.append(f"final run {label} has missing or inconsistent token-limit overshoot")

    if ultra:
        if (
            enforcement.get("first_crossing_tokens") != observed
            or enforcement.get("first_crossing_overshoot_tokens") != overshoot
        ):
            errors.append(
                f"final run {label} has inconsistent first-crossing Ultra aliases"
            )
        expected_final = model_tokens if at_or_above_limit else None
        expected_final_overshoot = max(0, model_tokens - token_limit) if at_or_above_limit else None
        if (
            enforcement.get("final_endpoint_tokens") != expected_final
            or enforcement.get("final_overshoot_tokens") != expected_final_overshoot
        ):
            errors.append(
                f"final run {label} has inconsistent final provider-gate endpoint token totals"
            )
        if (
            at_or_above_limit
            and isinstance(overshoot, int)
            and isinstance(enforcement.get("final_overshoot_tokens"), int)
            and enforcement["final_overshoot_tokens"] < overshoot
        ):
            errors.append(
                f"final run {label} final Ultra tail precedes its first crossing"
            )


def _check_final_record(
    run: Mapping[str, Any],
    expected: Mapping[str, Any],
    task: Mapping[str, Any],
    config: Mapping[str, Any],
    errors: list[str],
    *,
    allow_observational_unscored: bool,
    controlled_manifest_sha256: str | None,
    repository_root: Path | None,
    ultra_boundary_audits: list[dict[str, Any]],
    ultra_accounting_audits: list[dict[str, Any]],
) -> bool:
    run_id = run.get("run_id")
    label = str(run_id or expected["run_id"])
    _check_planned_metadata(
        run, expected, task, errors, require_planned_run_id=True
    )
    _check_limits(run, config, errors, final_record=True)
    _check_network_evidence(run, errors)
    _check_n_preflight_evidence(
        run, errors, controlled_manifest_sha256=controlled_manifest_sha256
    )
    officially_scored = _check_protocol(
        run,
        errors,
        allow_observational_unscored=allow_observational_unscored,
    )
    passed = run.get("pass")
    failure = run.get("failure_code")
    useful_work_started = run.get("useful_work_started")
    if not isinstance(useful_work_started, bool):
        errors.append(f"final run {label} has no Boolean useful_work_started marker")
    if not isinstance(passed, bool):
        errors.append(f"final run {label} has no Boolean pass result")
    if passed is True and failure is not None:
        errors.append(f"passing run {label} has failure code {failure!r}")
    if passed is True and useful_work_started is not True:
        errors.append(f"passing run {label} says useful work never started")
    if passed is not True and failure not in FAILURE_CODES:
        errors.append(f"failed final run {label} has invalid failure code {failure!r}")
    if failure == "SYSTEM_ERROR" and useful_work_started is not True:
        errors.append(
            f"final system-error run {label} did not start useful work and belongs in incident handling"
        )
    actual_stop = run.get("actual_stop_seconds")
    if (
        not isinstance(actual_stop, (int, float))
        or isinstance(actual_stop, bool)
        or actual_stop < 0
    ):
        errors.append(f"final run {label} has invalid actual stop time")
    _check_token_usage(run, config, errors)
    frozen = config.get("frozen_environment")
    if (
        isinstance(frozen, Mapping)
        and frozen.get("model_reasoning_effort") == "ultra"
    ):
        try:
            run_matrix.authenticate_runner_provider_gate_summary(run)
        except (OSError, BenchmarkToolError, ValueError) as error:
            errors.append(
                f"final run {label} provider-token-gate authentication failed: {error}"
            )
        ultra_accounting_audits.append(
            _check_ultra_accounting_projection(run, errors)
        )
    boundary_audit = _check_ultra_outcome_boundary(
        run, config, errors, repository_root=repository_root
    )
    if boundary_audit is not None:
        ultra_boundary_audits.append(boundary_audit)
    _check_validation_authentication(
        run,
        task,
        config,
        errors,
        controlled_manifest_sha256=controlled_manifest_sha256,
        repository_root=repository_root,
    )
    if run.get("condition") == "N" and run.get("library_use") is not False:
        errors.append(f"condition-N run {label} does not record library_use=false")
    if run.get("condition") == "L" and passed is True and not isinstance(
        run.get("library_use"), bool
    ):
        errors.append(f"passing condition-L run {label} lacks library-use classification")
    declarations = run.get("library_declarations")
    if not isinstance(declarations, list) or not all(
        isinstance(name, str) and name for name in declarations
    ):
        errors.append(f"final run {label} has invalid library declaration evidence")
    elif run.get("library_use") is True and not declarations:
        errors.append(
            f"final run {label} claims library use without a library declaration"
        )
    elif run.get("library_use") is False and declarations:
        errors.append(
            f"final run {label} records library declarations while library_use=false"
        )
    if run.get("condition") == "N" and declarations:
        errors.append(f"condition-N run {label} records forbidden library declarations")
    if passed is True and not _hex_digest(run.get("submission_sha256")):
        errors.append(f"passing run {label} has no fixed submission SHA-256")
    return officially_scored


def _check_matrix_record_authentication(
    run: Mapping[str, Any], errors: list[str]
) -> dict[str, Any]:
    """Recompute the orchestrator-owned final-record self-authentication."""

    label = str(run.get("run_id"))
    attempt = run.get("matrix_attempt")
    recorded = run.get("matrix_record_sha256")
    recomputed = _canonical_record_sha256(run, "matrix_record_sha256")
    valid = True
    if (
        not isinstance(attempt, int)
        or isinstance(attempt, bool)
        or attempt not in (1, 2)
    ):
        errors.append(f"final run {label} has invalid matrix_attempt")
        valid = False
    if not _hex_digest(recorded) or recorded != recomputed:
        errors.append(
            f"final run {label} has invalid matrix_record_sha256 authentication"
        )
        valid = False
    return {
        "run_id": label,
        "matrix_attempt": attempt,
        "matrix_record_sha256": recorded,
        "recomputed_matrix_record_sha256": recomputed,
        "valid": valid,
        "record": dict(run),
    }


def check_result_set(
    runs: Sequence[Mapping[str, Any]],
    *,
    run_order: Mapping[str, Any],
    config: Mapping[str, Any],
    manifest: Mapping[str, Any],
    repository_root: Path | None = None,
    allow_observational_unscored: bool = False,
) -> dict[str, Any]:
    """Return a detailed matrix check; callers must require ``ok`` for final analysis."""

    errors: list[str] = []
    warnings: list[str] = []
    benchmark_id_values = (
        run_order.get("benchmark_id"),
        config.get("benchmark_id"),
        manifest.get("benchmark_id"),
    )
    benchmark_ids = {value for value in benchmark_id_values if isinstance(value, str)}
    if (
        len(benchmark_ids) != 1
        or any(not isinstance(value, str) or not value for value in benchmark_id_values)
    ):
        errors.append(f"benchmark_id disagrees across metadata: {sorted(map(str, benchmark_ids))}")
    tasks = _metadata_tasks(manifest, errors)
    controlled_manifest_hashes: dict[str, str] = {}
    if repository_root is not None:
        for task_id in tasks:
            path = (
                repository_root.resolve()
                / "paper_bencmark"
                / "highambench"
                / "metadata"
                / "controlled"
                / f"{task_id}.json"
            )
            if not path.is_file():
                errors.append(f"controlled manifest is missing for {task_id}: {path}")
            else:
                controlled_manifest_hashes[task_id] = sha256_file(path)
            task = tasks[task_id]
            if task.get("tier") == "T4":
                target_file = task.get("target_file")
                if not isinstance(target_file, str) or not target_file:
                    errors.append(f"T4 task {task_id} has no target path")
                    continue
                task_path = (
                    repository_root.resolve()
                    / "paper_bencmark"
                    / "highambench"
                    / PurePosixPath(target_file).parent
                    / "task.json"
                )
                try:
                    task_record = read_json(task_path)
                except (OSError, BenchmarkToolError, json.JSONDecodeError) as error:
                    errors.append(f"cannot read T4 task record {task_id}: {error}")
                    continue
                validation = (
                    task_record.get("validation")
                    if isinstance(task_record, Mapping)
                    else None
                )
                if not isinstance(validation, Mapping):
                    errors.append(f"T4 task {task_id} has no validation object")
                    continue
                raw_required = validation.get("required_declarations")
                raw_holes = validation.get("controlled_sorries")
                if raw_required != task.get("required_declarations"):
                    errors.append(
                        f"T4 task {task_id} required_declarations disagrees with manifest"
                    )
                if not isinstance(raw_holes, list) or not raw_holes or any(
                    not isinstance(hole, Mapping) or set(hole) != CONTROLLED_SORRY_FIELDS
                    for hole in raw_holes
                ):
                    errors.append(f"T4 task {task_id} controlled_sorries is invalid")
                else:
                    task["controlled_sorries"] = [dict(hole) for hole in raw_holes]
    (
        configured_prompt_protocol,
        expected_prompt_provenance,
        expected_effective_prompt_texts,
        prompt_benchmark_root,
    ) = _expected_prompt_provenance(
        config,
        tasks,
        repository_root=repository_root,
        errors=errors,
    )
    repetitions = _repetitions(config, errors)
    expected, planned_pairs = _expected_assignments(
        run_order, tasks, repetitions, errors
    )
    (
        metadata_errors,
        metadata_warnings,
        verified_hashes,
        metadata_nonreference_reasons,
    ) = _metadata_readiness(
        config,
        manifest,
        repository_root=repository_root,
        allow_observational_unscored=allow_observational_unscored,
    )
    errors.extend(metadata_errors)
    warnings.extend(metadata_warnings)
    (
        freeze_check_sha256,
        production_canary_bindings_authenticated,
    ) = _check_frozen_run_evidence(
        runs,
        config=config,
        manifest=manifest,
        run_order=run_order,
        repository_root=repository_root,
        errors=errors,
        warnings=warnings,
    )
    nonreference_reasons: set[str] = set(metadata_nonreference_reasons)
    repetitions_without_seed = sorted(
        repetition_id for repetition_id, seed in repetitions.items() if seed is None
    )
    if repetitions_without_seed:
        reason = (
            "backend seeds are unavailable for repetitions: "
            + ", ".join(repetitions_without_seed)
        )
        nonreference_reasons.add(reason)
        if not allow_observational_unscored:
            errors.append(reason)

    counts = config.get("planned_counts_per_agent")
    if isinstance(counts, Mapping):
        expected_counts = {
            "papers": len({task["paper_id"] for task in tasks.values()}),
            "tasks": len(tasks),
            "repetitions_per_task": len(repetitions),
            "conditions": 2,
            "paired_assignments": len(expected) // 2,
            "runs": len(expected),
        }
        for field, wanted in expected_counts.items():
            if counts.get(field) != wanted:
                errors.append(
                    f"config planned count {field}={counts.get(field)!r}; expected {wanted}"
                )
    else:
        errors.append("config has no planned_counts_per_agent object")

    frozen = config.get("frozen_environment")
    frozen = frozen if isinstance(frozen, Mapping) else {}
    expected_agent_fields = {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
    }
    expected_environment_id = frozen.get("environment_id")

    run_ids: set[str] = set()
    groups: dict[tuple[AgentKey, AssignmentKey], list[Mapping[str, Any]]] = {}
    agent_keys: set[AgentKey] = set()
    for index, run in enumerate(runs):
        if run.get("schema_version") != SCHEMA_VERSION:
            errors.append(
                f"input record {index} has schema_version={run.get('schema_version')!r}; "
                f"expected {SCHEMA_VERSION!r}"
            )
        if run.get("kind") != "highambench-run":
            errors.append(f"input record {index} is not a highambench-run")
            continue
        run_id = run.get("run_id")
        if not isinstance(run_id, str) or not run_id:
            errors.append(f"input record {index} has no run_id")
        elif run_id in run_ids:
            errors.append(f"run_id {run_id} is repeated; incident logs would not be distinct")
        else:
            run_ids.add(run_id)
        agent_record = run.get("agent")
        if not isinstance(agent_record, Mapping):
            errors.append(f"run {run_id!r} lacks frozen agent metadata")
        else:
            for field, wanted in expected_agent_fields.items():
                if agent_record.get(field) != wanted:
                    errors.append(
                        f"run {run_id!r} has agent.{field}={agent_record.get(field)!r}; "
                        f"expected frozen {wanted!r}"
                    )
        if run.get("environment_id") != expected_environment_id:
            errors.append(
                f"run {run_id!r} has environment_id={run.get('environment_id')!r}; "
                f"expected frozen {expected_environment_id!r}"
            )
        started = _iso_time(run.get("started_at_utc"))
        finished = _iso_time(run.get("finished_at_utc"))
        if started is None or finished is None:
            errors.append(f"run {run_id!r} lacks usable UTC timestamps")
        elif started > finished:
            errors.append(f"run {run_id!r} finishes before it starts")
        assignment = _assignment_key(run)
        if assignment is None:
            errors.append(f"run {run_id!r} has an invalid assignment identity")
            continue
        key = _agent_key(run)
        agent_keys.add(key)
        groups.setdefault((key, assignment), []).append(run)

    if not agent_keys:
        errors.append("result set contains no evaluated agent")
    final_records: list[Mapping[str, Any]] = []
    system_incidents: list[dict[str, Any]] = []
    selected_run_ids: list[str] = []
    official_final_count = 0
    prompt_verified_final_count = 0
    system_error_issues: list[str] = []
    ultra_boundary_audits: list[dict[str, Any]] = []
    ultra_accounting_audits: list[dict[str, Any]] = []
    matrix_record_audits: list[dict[str, Any]] = []
    prompt_release_audits: list[dict[str, Any]] = []
    paired_hardware_audits: list[dict[str, Any]] = []
    expected_agent_version = frozen.get("agent_version")
    expected_model_version = frozen.get("model_version")
    for agent in sorted(agent_keys):
        if agent[1] != expected_agent_version:
            errors.append(
                f"agent {agent[0]} uses version {agent[1]!r}; expected {expected_agent_version!r}"
            )
        if agent[2] != expected_model_version:
            errors.append(
                f"agent {agent[0]} uses model {agent[2]!r}; expected {expected_model_version!r}"
            )
        actual_assignments = {
            assignment for key, assignment in groups if key == agent
        }
        for assignment in sorted(set(expected) - actual_assignments):
            errors.append(
                f"agent {agent} is missing assignment {'/'.join(assignment)}"
            )
        for assignment in sorted(actual_assignments - set(expected)):
            errors.append(
                f"agent {agent} has unplanned assignment {'/'.join(assignment)}"
            )
        for assignment in sorted(set(expected) & actual_assignments):
            records = groups[(agent, assignment)]
            incidents = [
                record
                for record in records
                if record.get("failure_code") == "SYSTEM_ERROR"
                and record.get("useful_work_started") is False
            ]
            candidates = [record for record in records if record not in incidents]
            if len(incidents) > 1:
                issue = (
                    f"agent {agent} assignment {'/'.join(assignment)} has {len(incidents)} "
                    "system errors; the one allowed rerun is exhausted"
                )
                errors.append(issue)
                system_error_issues.append(issue)
            for incident in incidents:
                planned_run_id = expected[assignment]["run_id"]
                incident_run_id = incident.get("run_id")
                if incident.get("planned_run_id") != planned_run_id:
                    issue = (
                        f"system-error run {incident_run_id} does not name planned run "
                        f"{planned_run_id}"
                    )
                    errors.append(issue)
                    system_error_issues.append(issue)
                if (
                    not isinstance(incident_run_id, str)
                    or not incident_run_id.startswith(f"{planned_run_id}-system-attempt-")
                ):
                    issue = f"system-error incident has no stable unique retry ID: {incident_run_id!r}"
                    errors.append(issue)
                    system_error_issues.append(issue)
                if incident.get("scored") is not False:
                    issue = f"system-error run {incident.get('run_id')} is incorrectly scored"
                    errors.append(issue)
                    system_error_issues.append(issue)
                if incident.get("pass") is not False:
                    issue = f"system-error run {incident.get('run_id')} must record pass=false"
                    errors.append(issue)
                    system_error_issues.append(issue)
                if not isinstance(incident.get("failure_note"), str) or not incident.get(
                    "failure_note"
                ):
                    issue = f"system-error run {incident.get('run_id')} lacks an incident note"
                    errors.append(issue)
                    system_error_issues.append(issue)
                incident_check_start = len(errors)
                _check_planned_metadata(
                    incident,
                    expected[assignment],
                    tasks[assignment[0]],
                    errors,
                    require_planned_run_id=False,
                )
                _check_limits(incident, config, errors, final_record=False)
                system_error_issues.extend(errors[incident_check_start:])
            if len(candidates) != 1:
                issue = (
                    f"agent {agent} assignment {'/'.join(assignment)} has {len(candidates)} "
                    "non-system final records; expected exactly one"
                )
                errors.append(issue)
                if incidents:
                    system_error_issues.append(issue)
                continue
            final = candidates[0]
            if incidents:
                incident = incidents[0]
                incident_finished = _iso_time(incident.get("finished_at_utc"))
                final_started = _iso_time(final.get("started_at_utc"))
                if incident_finished is None or final_started is None:
                    issue = (
                        f"system-error retry for {final.get('run_id')} lacks usable UTC timestamps"
                    )
                    errors.append(issue)
                    system_error_issues.append(issue)
                elif incident_finished > final_started:
                    issue = (
                        f"system-error retry for {final.get('run_id')} started before the incident ended"
                    )
                    errors.append(issue)
                    system_error_issues.append(issue)
                system_incidents.append(
                    {
                        "agent_id": agent[0],
                        "agent_version": agent[1],
                        "model": agent[2],
                        "assignment": "/".join(assignment),
                        "incident_run_id": incident.get("run_id"),
                        "replacement_run_id": final.get("run_id"),
                        "status": "resolved_by_one_rerun",
                        "note": incident.get("failure_note"),
                    }
                )
            prompt_ok = _check_prompt_provenance(
                final,
                expected_prompt_provenance.get(
                    (str(final.get("task_id")), str(final.get("condition")))
                ),
                protocol=configured_prompt_protocol,
                benchmark_root=prompt_benchmark_root,
                errors=errors,
            )
            if prompt_ok:
                prompt_verified_final_count += 1
            if configured_prompt_protocol is not None:
                prompt_release_audits.append(
                    _check_prompt_release_authentication(
                        final,
                        config,
                        expected_effective_prompt_texts.get(
                            (
                                str(final.get("task_id")),
                                str(final.get("condition")),
                            )
                        ),
                        errors,
                        repository_root=repository_root,
                    )
                )
            matrix_record_audits.append(
                _check_matrix_record_authentication(final, errors)
            )
            officially_scored = _check_final_record(
                final,
                expected[assignment],
                tasks[assignment[0]],
                config,
                errors,
                allow_observational_unscored=allow_observational_unscored,
                controlled_manifest_sha256=controlled_manifest_hashes.get(assignment[0]),
                repository_root=repository_root,
                ultra_boundary_audits=ultra_boundary_audits,
                ultra_accounting_audits=ultra_accounting_audits,
            )
            if officially_scored:
                official_final_count += 1
            else:
                protocol = final.get("protocol")
                if isinstance(protocol, Mapping):
                    notes = protocol.get("notes")
                    if isinstance(notes, list):
                        nonreference_reasons.update(str(note) for note in notes)
                    claims = protocol.get("claims")
                    if isinstance(claims, Mapping):
                        nonreference_reasons.update(
                            f"protocol claim not met: {name}"
                            for name, value in claims.items()
                            if value is not True
                        )
            final_records.append(final)
            if isinstance(final.get("run_id"), str):
                selected_run_ids.append(final["run_id"])

        environments = {
            record.get("environment_id")
            for record in final_records
            if _agent_key(record) == agent
        }
        if None in environments or "" in environments:
            errors.append(f"agent {agent} has a final run without environment_id")
        if len(environments) > 1:
            errors.append(f"agent {agent} uses multiple environment_id values: {environments}")

        for pair_id, planned in sorted(planned_pairs.items()):
            first_key = (planned["task_id"], planned["repetition_id"], planned["condition_order"][0])
            second_key = (planned["task_id"], planned["repetition_id"], planned["condition_order"][1])
            first_records = groups.get((agent, first_key), [])
            second_records = groups.get((agent, second_key), [])
            if not first_records or not second_records:
                continue
            first_finish = max(
                (_iso_time(record.get("finished_at_utc")) for record in first_records),
                default=None,
                key=lambda value: value or dt.datetime.min.replace(tzinfo=dt.timezone.utc),
            )
            second_start = min(
                (_iso_time(record.get("started_at_utc")) for record in second_records),
                default=None,
                key=lambda value: value or dt.datetime.max.replace(tzinfo=dt.timezone.utc),
            )
            if first_finish is None or second_start is None:
                errors.append(f"pair {pair_id} for agent {agent} lacks usable order timestamps")
            elif first_finish > second_start:
                errors.append(f"pair {pair_id} for agent {agent} ran out of planned N/L order")

        seeds_by_pair: dict[str, set[Any]] = {}
        for record in final_records:
            if _agent_key(record) == agent:
                seeds_by_pair.setdefault(str(record.get("pair_id")), set()).add(
                    record.get("backend_seed")
                )
        for pair_id, seeds in seeds_by_pair.items():
            if len(seeds) != 1:
                errors.append(f"pair {pair_id} for agent {agent} does not use one matching seed")

        hardware_policy = frozen.get("hardware_matching_policy")
        if hardware_policy is not None:
            if hardware_policy != getattr(run_matrix, "HARDWARE_MATCHING_POLICY", None):
                errors.append("config has an unsupported paired-hardware policy")
            for pair_id in sorted(planned_pairs):
                pair_finals = [
                    record
                    for record in final_records
                    if _agent_key(record) == agent
                    and record.get("pair_id") == pair_id
                ]
                by_condition = {
                    str(record.get("condition")): record for record in pair_finals
                }
                valid = True
                if set(by_condition) != {"N", "L"} or len(pair_finals) != 2:
                    errors.append(
                        f"pair {pair_id} for agent {agent} lacks exactly one N/L final"
                    )
                    continue
                n, l = by_condition["N"], by_condition["L"]
                n_hardware = n.get("allocation_hardware")
                l_hardware = l.get("allocation_hardware")
                descriptor_fields = {"path", "sha256", "record_sha256", "job_id"}
                if (
                    not isinstance(n_hardware, Mapping)
                    or set(n_hardware) != descriptor_fields
                    or not isinstance(l_hardware, Mapping)
                    or set(l_hardware) != descriptor_fields
                    or dict(n_hardware) != dict(l_hardware)
                    or not _hex_digest(n_hardware.get("sha256"))
                    or not _hex_digest(n_hardware.get("record_sha256"))
                    or not isinstance(n_hardware.get("path"), str)
                    or not n_hardware.get("path")
                    or not isinstance(n_hardware.get("job_id"), str)
                    or not n_hardware.get("job_id")
                ):
                    errors.append(
                        f"pair {pair_id} for agent {agent} does not use one exact "
                        "authenticated allocation descriptor"
                    )
                    valid = False
                n_wrapper = n.get("frozen_run_verification")
                l_wrapper = l.get("frozen_run_verification")
                if (
                    not isinstance(n_wrapper, Mapping)
                    or not isinstance(l_wrapper, Mapping)
                    or n_wrapper.get("freeze_check_sha256")
                    != l_wrapper.get("freeze_check_sha256")
                    or n_wrapper.get("freeze_check") != l_wrapper.get("freeze_check")
                ):
                    errors.append(
                        f"pair {pair_id} for agent {agent} does not share one exact "
                        "allocation freeze"
                    )
                    valid = False
                paired_hardware_audits.append(
                    {
                        "pair_id": pair_id,
                        "agent_id": agent[0],
                        "allocation_hardware": (
                            dict(n_hardware)
                            if isinstance(n_hardware, Mapping)
                            else None
                        ),
                        "freeze_check_sha256": (
                            n_wrapper.get("freeze_check_sha256")
                            if isinstance(n_wrapper, Mapping)
                            else None
                        ),
                        "same_authenticated_allocation": valid,
                    }
                )

    expected_final_count = len(expected) * len(agent_keys)
    if len(final_records) != expected_final_count:
        errors.append(
            f"selected {len(final_records)} final records; expected {expected_final_count}"
        )
    if (
        allow_observational_unscored
        and (repetitions_without_seed or metadata_nonreference_reasons)
        and official_final_count
    ):
        errors.append(
            "a non-reference observational configuration requires every final run to be "
            "explicitly marked scored=false"
        )
    reference_compliant = (
        not errors
        and production_canary_bindings_authenticated
        and not repetitions_without_seed
        and not metadata_nonreference_reasons
        and official_final_count == expected_final_count
    )
    check_ok = not errors
    analysis_profile = (
        "reference"
        if reference_compliant
        else "observational_pilot"
        if check_ok and allow_observational_unscored
        else "invalid"
    )
    network_violation_run_count = sum(
        1
        for record in final_records
        if isinstance(record.get("network_violation"), Mapping)
        and record["network_violation"].get("detected") is True
    )
    network_integrity_failure_count = sum(
        1
        for record in final_records
        if isinstance(record.get("network_violation"), Mapping)
        and record["network_violation"].get("integrity_ok") is False
    )
    prompt_summary = {
        "protocol_version": (
            configured_prompt_protocol.get("version")
            if isinstance(configured_prompt_protocol, Mapping)
            else "legacy-common-prompt"
        ),
        "signposted": configured_prompt_protocol is not None,
        "verified_final_runs": prompt_verified_final_count,
        "expected_final_runs": len(final_records),
        "condition_n_supplement_count": sum(
            1
            for record in final_records
            if record.get("condition") == "N"
            and isinstance(record.get("prompt_provenance"), Mapping)
            and record["prompt_provenance"].get("condition_supplement") is not None
        ),
        "condition_l_supplement_count": sum(
            1
            for record in final_records
            if record.get("condition") == "L"
            and isinstance(record.get("prompt_provenance"), Mapping)
            and isinstance(
                record["prompt_provenance"].get("condition_supplement"), Mapping
            )
        ),
        "complete": prompt_verified_final_count == len(final_records),
    }
    valid_prompt_releases = [
        audit for audit in prompt_release_audits if audit.get("valid") is True
    ]
    prompt_release_summary = {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "timing_origin": "authenticated_turn_start_write",
        "ultra_success_endpoint": (
            "authenticated_nested_submission_boundary_publication_after_"
            "outer_exec_raw_response_completion"
        ),
        "startup_timeout_seconds": PROMPT_RELEASE_STARTUP_TIMEOUT_SECONDS,
        "startup_timeout_separate_from_scored_wall_limit": True,
        "selected_final_run_count": len(prompt_release_audits),
        "authenticated_release_count": len(valid_prompt_releases),
        "retained_artifact_set_count": len(valid_prompt_releases),
        "retained_artifact_file_count": sum(
            int(audit.get("artifact_file_count", 0))
            for audit in valid_prompt_releases
        ),
        "retained_artifacts_reauthenticated": bool(
            repository_root is not None
            and all(
                audit.get("artifact_content_verified") is True
                for audit in valid_prompt_releases
            )
        ),
        "all_selected_final_releases_authenticated": bool(
            len(valid_prompt_releases) == len(prompt_release_audits)
            and len(prompt_release_audits) == len(final_records)
        ),
        "run_evidence": prompt_release_audits,
    }
    accepted_boundary_audits = [
        audit
        for audit in ultra_boundary_audits
        if audit.get("outcome") == "authenticated_pass_boundary"
    ]
    natural_failure_audits = [
        audit
        for audit in ultra_boundary_audits
        if audit.get("outcome") == "exact_natural_failure"
    ]
    invalid_boundary_audits = [
        audit
        for audit in ultra_boundary_audits
        if audit.get("outcome") not in (
            "authenticated_pass_boundary",
            "exact_provider_gate_crossing",
            "exact_natural_failure",
        )
    ]
    submission_boundary_summary = {
        "protocol": "authenticated-submit-proof-v1",
        "selected_ultra_run_count": len(ultra_boundary_audits),
        "passing_ultra_run_count": len(accepted_boundary_audits),
        "verified_accepted_boundary_count": len(accepted_boundary_audits),
        "naturally_drained_failure_count": len(natural_failure_audits),
        "provider_gate_crossing_failure_count": sum(
            audit.get("outcome") == "exact_provider_gate_crossing"
            for audit in ultra_boundary_audits
        ),
        "invalid_or_inexact_outcome_count": len(invalid_boundary_audits),
        "retained_artifact_set_count": sum(
            int(audit.get("artifact_set_count", 0))
            for audit in accepted_boundary_audits
        ),
        "retained_artifact_file_count": sum(
            int(audit.get("artifact_file_count", 0))
            for audit in accepted_boundary_audits
        ),
        "retained_artifacts_reauthenticated": bool(
            repository_root is not None
            and all(
                audit.get("artifact_content_verified") is True
                for audit in accepted_boundary_audits
            )
        ),
        "pass_drain_complete": False,
        "failure_natural_drain_complete": True,
        "root_active_at_pass_boundary": True,
        "descendants_quiescent_at_pass_boundary": True,
        "later_model_response_possible_after_pass_boundary": False,
        "all_selected_ultra_outcomes_exact": (
            not invalid_boundary_audits
            and len(ultra_boundary_audits) == len(final_records)
        ),
    }
    valid_accounting_audits = [
        audit for audit in ultra_accounting_audits if audit.get("valid") is True
    ]
    accounting_projection_summary = {
        "schema_version": ACCOUNTING_PROJECTION_SCHEMA_VERSION,
        "spawn_binding_source": ACCOUNTING_SPAWN_BINDING_SOURCE,
        "selected_ultra_run_count": len(ultra_accounting_audits),
        "complete_projection_count": len(valid_accounting_audits),
        "accepted_boundary_projection_count": sum(
            audit.get("outcome") == "accepted_boundary"
            for audit in valid_accounting_audits
        ),
        "natural_drain_projection_count": sum(
            audit.get("outcome") == "natural_drain"
            for audit in valid_accounting_audits
        ),
        "token_gate_crossing_projection_count": sum(
            audit.get("outcome") == "token_gate_crossing"
            for audit in valid_accounting_audits
        ),
        "all_selected_ultra_projections_complete": bool(
            len(valid_accounting_audits) == len(ultra_accounting_audits)
            and len(ultra_accounting_audits) == len(final_records)
        ),
        "run_evidence": ultra_accounting_audits,
    }
    valid_matrix_records = [
        audit for audit in matrix_record_audits if audit.get("valid") is True
    ]
    matrix_record_summary = {
        "schema_version": 1,
        "hash_field": "matrix_record_sha256",
        "canonicalization": "compact_sorted_key_utf8_json_remove_only_hash_field",
        "selected_final_record_count": len(matrix_record_audits),
        "authenticated_final_record_count": len(valid_matrix_records),
        "all_selected_final_records_authenticated": (
            len(valid_matrix_records) == len(matrix_record_audits)
            and len(matrix_record_audits) == len(final_records)
        ),
        "run_evidence": matrix_record_audits,
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-result-set-check",
        "ok": check_ok,
        "benchmark_id": next(iter(benchmark_ids)) if len(benchmark_ids) == 1 else None,
        "metadata_document_sha256": {
            "config": _document_digest(config),
            "manifest": _document_digest(manifest),
            "run_order": _document_digest(run_order),
        },
        "freeze_check_sha256": freeze_check_sha256,
        "production_canary_bindings_authenticated": (
            production_canary_bindings_authenticated
        ),
        "network_violation_run_count": network_violation_run_count,
        "network_integrity_failure_count": network_integrity_failure_count,
        "prompt_provenance": prompt_summary,
        "prompt_release_authentication": prompt_release_summary,
        "ultra_submission_boundaries": submission_boundary_summary,
        "ultra_accounting_projections": accounting_projection_summary,
        "matrix_record_authentication": matrix_record_summary,
        "paired_hardware_authentication": {
            "schema_version": 1,
            "policy": "exact_same_authenticated_slurm_allocation_per_pair",
            "selected_pair_count": len(paired_hardware_audits),
            "authenticated_pair_count": sum(
                audit.get("same_authenticated_allocation") is True
                for audit in paired_hardware_audits
            ),
            "cross_pair_hardware_variation_allowed": True,
            "all_selected_pairs_authenticated": bool(
                paired_hardware_audits
                and all(
                    audit.get("same_authenticated_allocation") is True
                    for audit in paired_hardware_audits
                )
            ),
            "pair_evidence": paired_hardware_audits,
        },
        "expected_agents": len(agent_keys),
        "expected_pairs_per_agent": len(expected) // 2,
        "expected_final_runs_per_agent": len(expected),
        "input_record_count": len(runs),
        "selected_final_record_count": len(final_records),
        "official_final_record_count": official_final_count,
        "selected_final_run_ids": sorted(selected_run_ids),
        "analysis_profile": analysis_profile,
        "reference_compliant": reference_compliant,
        "official_scores_valid": reference_compliant,
        "observational_results_allowed": allow_observational_unscored,
        "nonreference_reasons": sorted(nonreference_reasons),
        "system_error_incident_count": len(system_incidents),
        "system_error_incidents": system_incidents,
        "system_error_issue_count": len(system_error_issues),
        "system_error_issues": system_error_issues,
        "system_error_handling_complete": not system_error_issues,
        "verified_hashes": verified_hashes,
        "errors": errors,
        "warnings": warnings,
    }


def require_complete_result_set(check: Mapping[str, Any]) -> None:
    if (
        check.get("ok") is True
        and check.get("production_canary_bindings_authenticated") is True
    ):
        return
    errors = check.get("errors")
    details = "; ".join(str(error) for error in errors[:8]) if isinstance(errors, list) else ""
    if isinstance(errors, list) and len(errors) > 8:
        details += f"; ... and {len(errors) - 8} more"
    if check.get("production_canary_bindings_authenticated") is not True:
        binding_error = (
            "both frozen live canaries were not authenticated against the current "
            "production prompt protocol and execution components"
        )
        details = f"{details}; {binding_error}" if details else binding_error
    raise BenchmarkToolError("result set is not complete or frozen: " + details)


def _load_jsonl(paths: Sequence[Path]) -> list[dict[str, Any]]:
    runs: list[dict[str, Any]] = []
    for path in paths:
        try:
            stream = path.open(encoding="utf-8")
        except OSError as error:
            raise BenchmarkToolError(f"cannot open raw results {path}: {error}") from error
        with stream:
            for line_number, line in enumerate(stream, start=1):
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except json.JSONDecodeError as error:
                    raise BenchmarkToolError(f"invalid JSON at {path}:{line_number}: {error}") from error
                if not isinstance(value, dict):
                    raise BenchmarkToolError(f"non-object result at {path}:{line_number}")
                runs.append(value)
    return runs


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw_jsonl", type=Path, nargs="+")
    parser.add_argument("--run-order", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--repository-root", type=Path, required=True)
    parser.add_argument(
        "--allow-observational-unscored",
        action="store_true",
        help=(
            "accept a complete matrix whose final runs are explicitly unscored; "
            "the check remains non-reference and official scores stay invalid"
        ),
    )
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        runs = _load_jsonl(args.raw_jsonl)
        run_order = read_json(args.run_order)
        config = read_json(args.config)
        manifest = read_json(args.manifest)
        if not all(isinstance(value, dict) for value in (run_order, config, manifest)):
            raise BenchmarkToolError("run order, config, and manifest must be JSON objects")
        check = check_result_set(
            runs,
            run_order=run_order,
            config=config,
            manifest=manifest,
            repository_root=args.repository_root,
            allow_observational_unscored=args.allow_observational_unscored,
        )
        if args.output:
            write_json(args.output, check)
        else:
            print(json.dumps(check, indent=2, sort_keys=True))
        return 0 if check["ok"] else 1
    except BenchmarkToolError as error:
        print(f"error: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
