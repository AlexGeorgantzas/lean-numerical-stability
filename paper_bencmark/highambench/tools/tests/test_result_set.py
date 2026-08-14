from __future__ import annotations

import copy
import datetime as dt
import hashlib
import json
from pathlib import Path
import platform
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from analyze import analyze, render_latex, write_csv_tables  # noqa: E402
import result_set as result_set_module  # noqa: E402
import refresh_snapshot  # noqa: E402
from common import BenchmarkToolError  # noqa: E402
from result_set import (  # noqa: E402
    ENVIRONMENT_BUNDLE_DEFINITION,
    _check_prompt_release_authentication,
    _check_prompt_provenance,
    _check_token_usage,
    _check_ultra_outcome_boundary,
    _check_validation_authentication,
    _derive_ultra_accounting_projection,
    _environment_bundle_digest,
    _valid_token_control,
    _valid_ultra_canary_summary,
    check_result_set,
    require_complete_result_set,
)


SHA_A = "a" * 64
SHA_B = "b" * 64
SHA_C = "c" * 64
SALT = "test-highambench-order"
PYTHON_VERSION = platform.python_version()
PYTHON_SHA256 = hashlib.sha256(Path(sys.executable).resolve().read_bytes()).hexdigest()
TOKEN_CANARY_PATH = (
    "paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json"
)
ULTRA_CANARY_PATH = (
    "paper_bencmark/highambench/metadata/evidence/"
    "ultra_orchestration_live_canary.json"
)
ULTRA_ORCHESTRATION = {"enabled": True, "multi_agent_version": "v2"}
PRODUCTION_PROMPT_PROTOCOL = {"version": "fixture-production-prompt-v1"}
PRODUCTION_EXECUTION_COMPONENTS = {
    field: str(index) * 64
    for index, field in enumerate(
        result_set_module.run_matrix.EXECUTION_COMPONENT_FIELDS, start=1
    )
}


def empty_reconciliation_v3_delivery_fields(
    zero_usage: dict[str, int],
) -> dict[str, object]:
    return {
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_usage": copy.deepcopy(zero_usage),
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_usage": copy.deepcopy(zero_usage),
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_evidence": [],
    }


def nested_submission_wire_fixture() -> dict:
    codex = result_set_module.ultra_canary.codex_isolated
    return {
        "schema_version": codex.SUBMISSION_BARRIER_SCHEMA_VERSION,
        "candidate_path": "Candidate.lean",
        "call_id": "inner-submit-call",
        "submission_transport": codex.NESTED_SUBMISSION_WIRE_FORMAT,
        "outer_raw_item_id": "outer-raw-item",
        "outer_raw_item_type": "custom_tool_call",
        "outer_exec_name": "exec",
        "outer_exec_call_id": "outer-exec-call",
        "outer_exec_program": codex.NESTED_SUBMISSION_EXEC_SOURCE,
        "outer_exec_program_bytes": codex.NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
        "outer_exec_program_sha256": codex.NESTED_SUBMISSION_EXEC_SOURCE_SHA256,
        **codex.nested_submission_exec_yield_record(),
        "outer_raw_item_observed_at_monotonic_ns": 8,
        "inner_dynamic_item_started_at_monotonic_ns": 9,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "inner_dynamic_call_id": "inner-submit-call",
        "inner_dynamic_tool_name": "submit_proof",
        "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
    }


def authenticate_matrix_record(record: dict, attempt: int = 1) -> None:
    record["matrix_attempt"] = attempt
    unsigned = dict(record)
    unsigned.pop("matrix_record_sha256", None)
    record["matrix_record_sha256"] = hashlib.sha256(
        json.dumps(
            unsigned,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
    ).hexdigest()


def authenticate_matrix_records(records: list[dict]) -> None:
    for record in records:
        authenticate_matrix_record(record, int(record.get("matrix_attempt", 1)))


def projection_usage(*, accepted: bool) -> dict:
    def tokens(input_tokens: int, output_tokens: int, *, cached: int = 0) -> dict:
        return {
            "input_tokens": input_tokens,
            "cached_input_tokens": cached,
            "cache_write_input_tokens": 0,
            "output_tokens": output_tokens,
            "reasoning_output_tokens": min(output_tokens, 2),
            "total_tokens": input_tokens + output_tokens,
        }

    zero = tokens(0, 0)
    root_raw = tokens(100, 10, cached=10)
    root_exempt = tokens(20, 2, cached=2)
    root_pre_submit = {
        field: root_raw[field] - root_exempt[field]
        for field in root_raw
    }
    root_expected = root_pre_submit if accepted else root_raw
    child_baseline = dict(root_pre_submit)
    child_raw = tokens(50, 5, cached=5)
    child_full = {
        field: child_baseline[field] + child_raw[field]
        for field in child_raw
    }
    boundary = (
        {
            "status": "accepted",
            "exact": True,
            "authenticated": True,
            "thread_id": "root",
            "response_id": "root-submit",
        }
        if accepted
        else None
    )
    spawn_id = "call_spawn_1"
    policy_static = (
        result_set_module.ultra_canary.codex_isolated.ultra_fork_policy_static_record()
    )
    fork_policy = {
        **policy_static,
        "call_evidence": [
            {
                "call_id": spawn_id,
                "parent_thread_id": "root",
                "parent_turn_id": "root-turn-2",
                "parent_response_id": "root-before",
                "fork_turns": "all",
                "fork_semantics": "full_history_parent_pre_response",
                "hook_run_id": (
                    f"pre-tool-use:0:{policy_static['source_path']}:{spawn_id}"
                ),
                "hook_source_path": policy_static["source_path"],
                "hook_thread_id": "root",
                "hook_turn_id": "root-turn-2",
                "hook_started_observed": True,
                "hook_started_count": 1,
                "hook_completed_observed": True,
                "hook_completed_count": 1,
                "hook_status": "completed",
                "decision": "allow",
                "feedback": None,
                "resolution_status": "resolved_child",
                "child_activity_observed": True,
            }
        ],
        "complete": True,
    }
    response_rows = [
        ("root-before", "root", "root-turn-1", root_pre_submit),
        ("child-response", "child", "child-turn", child_raw),
        ("root-submit", "root", "root-submit-turn", root_exempt),
    ]
    runner = result_set_module.ultra_canary.runner
    gate_calls = []
    response_ledger = []
    for sequence, (response_id, thread_id, turn_id, response_usage) in enumerate(
        response_rows, start=1
    ):
        call = {field: None for field in runner.PROVIDER_GATE_CALL_KEYS}
        crossbind = {
            field: None for field in runner.PROVIDER_GATE_CROSSBIND_KEYS
        }
        crossbind.update(
            {
                "thread_id": thread_id,
                "turn_id": turn_id,
                "event_sequence": sequence,
                "normalized_usage": copy.deepcopy(response_usage),
                "bind_unix_ns": 10_000 + sequence,
                "bind_monotonic_ns": 1_000 + sequence,
            }
        )
        call.update(
            {
                "call_id": f"provider-call-{sequence}",
                "response_id": response_id,
                "upstream_status": 200,
                "upstream_content_type": "text/event-stream; charset=utf-8",
                "upstream_content_type_occurrences": 1,
                "upstream_content_encoding": "identity",
                "upstream_content_encoding_occurrences": 1,
                "upstream_body_sha256": hashlib.sha256(
                    response_id.encode("utf-8")
                ).hexdigest(),
                "upstream_body_bytes": len(response_id.encode("utf-8")),
                "upstream_sse_authentication": {
                    "schema_version": 1,
                    "protocol": runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT[
                        "protocol"
                    ],
                    "parser": runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT[
                        "parser"
                    ],
                    "complete": True,
                    "content_type_basis": "declared_text_event_stream",
                    "content_encoding_basis": "declared_identity",
                    "json_event_count": 1,
                    "completed_event_index": 0,
                    "done_count": 0,
                    "body_sha256": hashlib.sha256(
                        response_id.encode("utf-8")
                    ).hexdigest(),
                    "body_bytes": len(response_id.encode("utf-8")),
                    "response_id": response_id,
                    "downstream_content_type_synthesized": False,
                },
                "response_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                "request_metadata": {
                    "installation_id": "installation",
                    "session_id": "session",
                    "thread_id": thread_id,
                    "turn_id": turn_id,
                    "request_kind": "turn",
                    "window_id": "window",
                },
                "normalized_usage": copy.deepcopy(response_usage),
                "crossed_cap": False,
                "release_kind": "byte_identity",
                "client_release_complete": True,
                "appserver_crossbind": crossbind,
                "appserver_delivery": {
                    "kind": "direct_raw_response",
                    "successor_call_id": None,
                    "successor_response_id": None,
                    "bind_unix_ns": crossbind["bind_unix_ns"],
                    "bind_monotonic_ns": crossbind["bind_monotonic_ns"],
                },
                "response_output_manifest": {
                    "schema_version": 1,
                    "response_id": response_id,
                    "output_item_count": 0,
                    "action_capable_item_count": 0,
                    "items": [],
                },
                "error": None,
            }
        )
        gate_calls.append(call)
        ledger = {field: None for field in runner.ULTRA_RESPONSE_LEDGER_KEYS}
        ledger.update(
            {
                "response_id": response_id,
                "thread_id": thread_id,
                "turn_id": turn_id,
                "raw_response_notification_sequence": sequence,
                "usage": copy.deepcopy(response_usage),
                "provider_gate_call": call,
            }
        )
        response_ledger.append(ledger)
    close_reason = "accepted_submission" if accepted else "natural_end"
    terminal = {field: None for field in runner.PROVIDER_GATE_STATE_KEYS}
    terminal.update(
        {
            "phase": "CLOSED",
            "close_reason": close_reason,
            "completed_tokens": 165,
            "crossing": None,
            "crossing_closed": False,
            "open_request_ids": [],
            "all_complete": True,
            "no_post_close_upstream": True,
            "poisoned": False,
            "poison_reasons": [],
            "active_handler_count": 0,
            "handlers_quiescent": True,
        }
    )
    provider_gate = {
        field: None for field in runner.ULTRA_PROVIDER_GATE_SUMMARY_KEYS
    }
    provider_gate.update(
        {
            "enabled": True,
            "response_token_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
            "artifact_path": "/trusted/provider-token-gate.json",
            "record_sha256": SHA_A,
            "final_attached": True,
            "exact_for_usage": True,
            "live": copy.deepcopy(terminal),
            "terminal": terminal,
        }
    )
    adapter_teardown = {
        field: None for field in runner.ULTRA_ADAPTER_TEARDOWN_KEYS
    }
    adapter_teardown.update(
        {
            "process_group_isolated": True,
            "immediate": accepted,
            "stdin_closed": True,
            "completed": True,
        }
    )
    provider_usage = {
        "input_tokens": 150,
        "cached_input_tokens": 15,
        "cache_write_input_tokens": 0,
        "output_tokens": 15,
        "reasoning_output_tokens": 4,
        "total_tokens": 165,
    }
    provider_ids = ["root-before", "child-response", "root-submit"]
    zero_provider_usage = {field: 0 for field in provider_usage}
    reconciliation = {
        "schema_version": (
            result_set_module.run_matrix.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
        ),
        "provider_response_count": 3,
        "appserver_response_count": 3,
        "suppressed_collaboration_wait_response_count": 0,
        "provider_usage": provider_usage,
        "appserver_usage": provider_usage,
        "suppressed_collaboration_wait_usage": zero_provider_usage,
        "provider_response_ids": provider_ids,
        "appserver_response_ids": provider_ids,
        "suppressed_collaboration_wait_response_ids": [],
        "suppressed_collaboration_wait_evidence": [],
        **empty_reconciliation_v3_delivery_fields(zero_provider_usage),
    }
    return {
        "accounting_projection_schema_version": (
            result_set_module.ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "raw_spawn_call_ids": [spawn_id],
        "activity_spawn_call_ids": [spawn_id],
        "collab_spawn_call_ids": [spawn_id],
        "resolved_spawn_call_ids": [spawn_id],
        "failed_spawn_call_ids": [],
        "policy_blocked_spawn_call_ids": [],
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": ["child"],
        "hook_observed_spawn_call_ids": [spawn_id],
        "hook_allowed_spawn_call_ids": [spawn_id],
        "hook_blocked_spawn_call_ids": [],
        "hook_invalid_spawn_call_ids": [],
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "fork_policy_complete": True,
        "accounting_complete": True,
        "fork_policy": fork_policy,
        "root_thread_id": "root",
        "thread_count": 2,
        "response_count": 3,
        "call_count": 3,
        "response_ids": provider_ids,
        "provider_response_count": 3,
        "provider_response_ids": provider_ids,
        "provider_usage": provider_usage,
        "appserver_response_count": 3,
        "appserver_response_ids": provider_ids,
        "appserver_usage": provider_usage,
        "suppressed_collaboration_wait_response_count": 0,
        "suppressed_collaboration_wait_response_ids": [],
        "suppressed_collaboration_wait_usage": reconciliation[
            "suppressed_collaboration_wait_usage"
        ],
        "suppressed_collaboration_wait_evidence": [],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_usage": copy.deepcopy(
            zero_provider_usage
        ),
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_usage": copy.deepcopy(
            zero_provider_usage
        ),
        "discarded_after_explicit_child_interrupt_evidence": [],
        "provider_usage_reconciliation": reconciliation,
        "input_tokens": 150,
        "cached_input_tokens": 15,
        "cache_write_input_tokens": 0,
        "output_tokens": 15,
        "reasoning_output_tokens": 4,
        "model_tokens": 165,
        "submission_boundary_exact": accepted,
        "submission_boundary": boundary,
        "first_crossing": None,
        "stop_reason": "first_valid_proof" if accepted else "natural_end",
        "drain_complete": not accepted,
        "active_thread_ids": ["root"] if accepted else [],
        "unresolved_thread_ids": [],
        "invalid_reasons": [],
        "interrupt_requested": False,
        "pending_interrupt_response_count": 0,
        "appserver_response_ledger": response_ledger,
        "provider_token_gate": provider_gate,
        "adapter_teardown": adapter_teardown,
        "thread_accounting": [
            {
                "thread_id": "root",
                "parent_thread_id": None,
                "agent_path": "/root",
                "response_count": 2,
                **root_raw,
                "spawn_call_id": None,
                "spawn_parent_turn_id": None,
                "spawn_parent_response_id": None,
                "spawn_fork_turns": None,
                "spawn_fork_semantics": None,
                "spawn_binding_status": "root_zero",
                "expected_cumulative_baseline": zero,
                "expected_cumulative_projection": dict(root_expected),
                "full_cumulative_projection": dict(root_raw),
                "last_cumulative": dict(root_expected),
                "cumulative_observation_count": 1,
                "observed_cumulative_baseline": zero,
                "cumulative_baseline_matches_expected": True,
                "cumulative_projection_status": (
                    "matched_pre_exempt_response"
                    if accepted
                    else "matched_full_projection"
                ),
                "cumulative_projection_match": True,
                "cumulative_projection_exempt_response_id": (
                    "root-submit" if accepted else None
                ),
                "cumulative_projection_exempt_response_usage": (
                    root_exempt if accepted else None
                ),
                "accounting_complete": True,
            },
            {
                "thread_id": "child",
                "parent_thread_id": "root",
                "agent_path": "/root/child",
                "response_count": 1,
                **child_raw,
                "spawn_call_id": spawn_id,
                "spawn_parent_turn_id": "root-turn-2",
                "spawn_parent_response_id": "root-before",
                "spawn_fork_turns": "all",
                "spawn_fork_semantics": "full_history_parent_pre_response",
                "spawn_binding_status": "resolved",
                "expected_cumulative_baseline": child_baseline,
                "expected_cumulative_projection": dict(child_full),
                "full_cumulative_projection": dict(child_full),
                "last_cumulative": dict(child_full),
                "cumulative_observation_count": 1,
                "observed_cumulative_baseline": child_baseline,
                "cumulative_baseline_matches_expected": True,
                "cumulative_projection_status": "matched_full_projection",
                "cumulative_projection_match": True,
                "cumulative_projection_exempt_response_id": None,
                "cumulative_projection_exempt_response_usage": None,
                "accounting_complete": True,
            },
        ],
    }


def token_control_record(limit_tokens: int) -> dict:
    return refresh_snapshot._token_control_record(limit_tokens)


def token_canary_descriptor(digest: str = SHA_B) -> dict:
    return {"path": TOKEN_CANARY_PATH, "sha256": digest, "status": "passed"}


def token_canary_prompt_release() -> dict:
    released = 1_000_000_000
    wall = 300
    hashes = {"ready": SHA_A, "go": SHA_B, "release": SHA_C}
    return {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "status": "released_authenticated",
        "authenticated": True,
        "timing_exact": True,
        "useful_work_basis": "authenticated_release",
        "startup_timeout_seconds": 120.0,
        "startup_timeout_triggered": False,
        "go_minimum_release_window_seconds": 5.0,
        "artifact_content_verified": True,
        "artifact_count": 3,
        "artifacts": {
            label: {
                "path": f"/trusted/logs/canary.prompt-{label}.json",
                "file_sha256": (SHA_C, SHA_A, SHA_B)[index],
                "record_sha256": hashes[label],
            }
            for index, label in enumerate(("ready", "go", "release"))
        },
        "canonical_encoding": "compact_sorted_key_utf8_json_newline",
        "sealed_mode": "0444",
        "handshake_nonce": SHA_A,
        "root_thread_id": "root",
        "effective_prompt_sha256": SHA_B,
        "effective_prompt_bytes": 12001,
        "turn_start_request_sha256": SHA_C,
        "turn_start_wire_verified": True,
        "command_binding_verified": True,
        "root_identity_verified": True,
        "ready_sha256": hashes["ready"],
        "go_sha256": hashes["go"],
        "release_sha256": hashes["release"],
        "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
        "released_at_monotonic_ns": released,
        "deadline_monotonic_ns": released + wall * 1_000_000_000,
        "deadline_derivation": (
            "released_at_monotonic_ns + wall_time_seconds*1000000000"
        ),
        "wall_time_seconds": wall,
        "actual_stop_seconds": 5.75,
        "token_crossing_within_deadline": True,
        "first_valid_seconds": None,
        "submission_boundary": None,
        "sanitized_provider_gate_crossing": True,
        "top_level_artifact_count_unchanged": len(
            result_set_module.token_canary.ARTIFACT_LABELS
        ),
    }


def token_canary_summary(descriptor: dict) -> dict:
    artifacts = {
        label: {
            "path": f"artifacts/{label}",
            "sha256": (SHA_A, SHA_B, SHA_C)[index % 3],
            "bytes": 101 + index,
        }
        for index, label in enumerate(
            result_set_module.token_canary.ARTIFACT_LABELS
        )
    }
    zero = {
        field: 0
        for field in (
            "input_tokens",
            "cached_input_tokens",
            "cache_write_input_tokens",
            "output_tokens",
            "reasoning_output_tokens",
            "total_tokens",
        )
    }
    projection = {
        "accounting_projection_schema_version": (
            result_set_module.token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "provider_gate_protocol": result_set_module.ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": SHA_A,
        "provider_gate_close_reason": "token_limit",
        "provider_gate_response_ids": ["prompt-response", "compaction-response"],
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": {
            "schema_version": (
                result_set_module.run_matrix.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
            ),
            "provider_response_count": 2,
            "appserver_response_count": 2,
            "suppressed_collaboration_wait_response_count": 0,
            "provider_usage": {
                "input_tokens": 180_000,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 1,
                "reasoning_output_tokens": 0,
                "total_tokens": 180_001,
            },
            "appserver_usage": {
                "input_tokens": 180_000,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 1,
                "reasoning_output_tokens": 0,
                "total_tokens": 180_001,
            },
            "suppressed_collaboration_wait_usage": zero,
            "provider_response_ids": ["prompt-response", "compaction-response"],
            "appserver_response_ids": ["prompt-response", "compaction-response"],
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_evidence": [],
            **empty_reconciliation_v3_delivery_fields(zero),
        },
        "provider_gate_setup_requests_empty": True,
        "provider_requests_quiescent": True,
        "adapter_teardown_complete": True,
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "root_thread_id": "root",
        "root_expected_cumulative_baseline": zero,
        "root_cumulative_projection_status": "cumulative_projection_mismatch",
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": False,
        "raw_spawn_call_ids": [],
        "activity_spawn_call_ids": [],
        "collab_spawn_call_ids": [],
        "resolved_spawn_call_ids": [],
        "failed_spawn_call_ids": [],
        "policy_blocked_spawn_call_ids": [],
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": [],
        "hook_observed_spawn_call_ids": [],
        "hook_allowed_spawn_call_ids": [],
        "hook_blocked_spawn_call_ids": [],
        "hook_invalid_spawn_call_ids": [],
        "fork_policy_complete": True,
        "fork_policy": {
            **result_set_module.ultra_canary.codex_isolated.ultra_fork_policy_static_record(),
            "call_evidence": [],
            "complete": True,
        },
        "accounting_complete": False,
        "root_only": True,
    }
    projection["projection_payload_sha256"] = hashlib.sha256(
        json.dumps(projection, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        **copy.deepcopy(descriptor),
        "canary_limit_tokens": result_set_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT,
        "first_crossing_tokens": result_set_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT + 23,
        "final_endpoint_tokens": result_set_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT + 23,
        "thread_count": 1,
        "observed_child_thread_count": 0,
        "response_count": 2,
        "drain_complete": False,
        "provider_gate_quiescent": True,
        "measurement_exact": True,
        "synthetic_input": True,
        "matrix_assignment": False,
        "benchmark_task_bytes_used": False,
        "prompt_protocol": result_set_module.token_canary.PROMPT_PROTOCOL,
        "source_separation_audit_sha256": SHA_C,
        "prompt_release": token_canary_prompt_release(),
        "accounting_projection": projection,
        "artifacts": artifacts,
    }


def ultra_canary_descriptor(digest: str = SHA_C) -> dict:
    return {"path": ULTRA_CANARY_PATH, "sha256": digest, "status": "passed"}


def ultra_canary_summary(descriptor: dict) -> dict:
    barrier = {
        **nested_submission_wire_fixture(),
        "sequence": 1,
        "challenge_sha256": SHA_A,
        "call_sha256": SHA_B,
        "request_sha256": SHA_C,
        "ack_sha256": SHA_A,
        "candidate_sha256": SHA_B,
        "candidate_size_bytes": 101,
        "validator_contract_sha256": SHA_C,
        "outer_raw_item_and_call_ids_pairwise_distinct": True,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "submission_event_order": (
            result_set_module.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
        ),
        "dynamic_call_observed_before_raw_response_completed": True,
        "raw_response_completed_before_dynamic_call_observed": False,
        "raw_response_completed_before_boundary_publication": True,
        "captured_at_monotonic_ns": 10,
        "raw_response_observed_at_monotonic_ns": 11,
        "request_published_at_monotonic_ns": 12,
        "inner_dynamic_item_started": True,
        "inner_submit_invocation_exact": True,
        "inner_submit_only_nested_tool_call": True,
        "retained_read_only": True,
    }
    codex = result_set_module.ultra_canary.codex_isolated
    policy_static = codex.ultra_fork_policy_static_record()
    allowed_id = "call_allowed_root"
    blocked_ids = ["call_blocked_child", "call_blocked_root"]

    def policy_call(
        call_id: str,
        *,
        parent: str,
        turn_id: str,
        response_id: str,
        allowed: bool,
    ) -> dict:
        return {
            "call_id": call_id,
            "parent_thread_id": parent,
            "parent_turn_id": turn_id,
            "parent_response_id": response_id,
            "fork_turns": "all" if allowed else "3",
            "fork_semantics": (
                "full_history_parent_pre_response"
                if allowed
                else "unsupported_positive_turn_suffix"
            ),
            "hook_run_id": f"pre-tool-use:0:{policy_static['source_path']}:{call_id}",
            "hook_source_path": policy_static["source_path"],
            "hook_thread_id": parent,
            "hook_turn_id": turn_id,
            "hook_started_observed": True,
            "hook_started_count": 1,
            "hook_completed_observed": True,
            "hook_completed_count": 1,
            "hook_status": "completed" if allowed else "blocked",
            "decision": "allow" if allowed else "block",
            "feedback": (
                None
                if allowed
                else codex.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
            ),
            "resolution_status": (
                "resolved_child"
                if allowed
                else codex.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
            ),
            "child_activity_observed": allowed,
        }

    projection = {
        "accounting_projection_schema_version": (
            result_set_module.ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "provider_gate_protocol": result_set_module.ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": SHA_A,
        "provider_gate_close_reason": "accepted_submission",
        "provider_gate_response_ids": [
            "root-response",
            "suppressed-wait-response",
            "child-response",
            "root-submit-response",
        ],
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": {
            "schema_version": (
                result_set_module.run_matrix.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
            ),
            "provider_response_count": 4,
            "appserver_response_count": 3,
            "suppressed_collaboration_wait_response_count": 1,
            "provider_usage": {
                "input_tokens": 40,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 4,
                "reasoning_output_tokens": 0,
                "total_tokens": 44,
            },
            "appserver_usage": {
                "input_tokens": 30,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 3,
                "reasoning_output_tokens": 0,
                "total_tokens": 33,
            },
            "suppressed_collaboration_wait_usage": {
                "input_tokens": 10,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 1,
                "reasoning_output_tokens": 0,
                "total_tokens": 11,
            },
            "provider_response_ids": [
                "root-response",
                "suppressed-wait-response",
                "child-response",
                "root-submit-response",
            ],
            "appserver_response_ids": [
                "root-response",
                "child-response",
                "root-submit-response",
            ],
            "suppressed_collaboration_wait_response_ids": [
                "suppressed-wait-response"
            ],
            "suppressed_collaboration_wait_evidence": [
                {
                    "response_id": "suppressed-wait-response",
                    "provider_call_id": "provider-wait-call",
                    "thread_id": "root",
                    "turn_id": "root-turn",
                    "successor_response_id": "child-response",
                    "successor_call_id": "provider-child-call",
                    "agent_message_item_id": "child-result-message",
                    "agent_message_sha256": SHA_A,
                    "agent_message_author": "child",
                    "agent_message_recipient": "/root",
                    "agent_message_observed_at_unix_ns": 2,
                    "agent_message_observed_at_monotonic_ns": 1,
                }
            ],
            **empty_reconciliation_v3_delivery_fields(
                {
                    "input_tokens": 0,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 0,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 0,
                }
            ),
        },
        "provider_gate_setup_requests_empty": True,
        "provider_requests_quiescent": True,
        "adapter_teardown_complete": True,
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "raw_spawn_call_ids": [allowed_id, *blocked_ids],
        "activity_spawn_call_ids": [allowed_id],
        "collab_spawn_call_ids": [allowed_id],
        "resolved_spawn_call_ids": [allowed_id],
        "failed_spawn_call_ids": blocked_ids,
        "policy_blocked_spawn_call_ids": blocked_ids,
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": ["child"],
        "hook_observed_spawn_call_ids": [allowed_id, *blocked_ids],
        "hook_allowed_spawn_call_ids": [allowed_id],
        "hook_blocked_spawn_call_ids": blocked_ids,
        "hook_invalid_spawn_call_ids": [],
        "spawn_parent_response_ids": {allowed_id: "root-response"},
        "pre_spawn_completed_root_response_counts": {allowed_id: 2},
        "raw_call_activity_id_match": True,
        "completed_root_response_before_spawn": True,
        "fork_turns_all_child_thread_count": 1,
        "nonzero_inherited_baseline_child_thread_ids": ["child"],
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "fork_policy_complete": True,
        "accounting_complete": True,
        "fork_policy": {
            **policy_static,
            "call_evidence": [
                policy_call(
                    allowed_id,
                    parent="root",
                    turn_id="root-turn",
                    response_id="root-response",
                    allowed=True,
                ),
                policy_call(
                    "call_blocked_child",
                    parent="child",
                    turn_id="child-turn",
                    response_id="child-blocked-response",
                    allowed=False,
                ),
                policy_call(
                    "call_blocked_root",
                    parent="root",
                    turn_id="root-turn",
                    response_id="root-blocked-response",
                    allowed=False,
                ),
            ],
            "complete": True,
        },
        "thread_accounting": [
            {
                "thread_id": "child",
                "parent_thread_id": "root",
                "agent_path": "/root/child",
            },
            {
                "thread_id": "root",
                "parent_thread_id": None,
                "agent_path": "/root",
            },
        ],
    }
    projection["projection_payload_sha256"] = hashlib.sha256(
        json.dumps(projection, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        **copy.deepcopy(descriptor),
        "thread_count": 2,
        "observed_descendant_thread_count": 1,
        "positive_usage_descendant_thread_count": 1,
        "response_count": 3,
        "total_model_tokens": 137,
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "accounting_projection": projection,
        "validation_authentication": {
            "schema_version": 1,
            "authenticated": True,
            "record_sha256": SHA_A,
            "validation_log_sha256": SHA_B,
            "candidate_sha256": SHA_B,
            "validator_contract_sha256": SHA_C,
            "submission_request_sha256": SHA_C,
            "submission_sequence": 1,
        },
        "dependency_audit": {
            "complete": True,
            "helper_sha256": SHA_A,
            "command_sha256": SHA_B,
            "library_use": False,
            "library_declarations": [],
            "target_seen": True,
            "semantic_type_equal": True,
        },
        "prompt_release": {
            "schema_version": 1,
            "protocol_version": "highambench-prompt-release-v1",
            "authenticated": True,
            "timing_exact": True,
            "elapsed_clock": "CLOCK_MONOTONIC",
            "startup_timeout_seconds": 120,
            "artifact_count": 3,
            "artifacts_reauthenticated": True,
            "released_at_monotonic_ns": 1_000_000_000,
            "measurement_deadline_monotonic_ns": 301_000_000_000,
            "request_published_at_monotonic_ns": 1_600_000_000,
            "request_publication_timing_verified": True,
        },
        "barrier": barrier,
        "artifacts": {
            label: {
                "path": f"artifacts/{label}",
                "sha256": (SHA_A, SHA_B, SHA_C)[index % 3],
                "bytes": 101 + index,
            }
            for index, label in enumerate(
                result_set_module.ultra_canary.ARTIFACT_LABELS
            )
        },
    }


def benchmark_documents(
    *,
    backend_seed: int | None = 7,
    bubblewrap: bool = False,
    paper_ids: tuple[str, ...] = ("P01",),
) -> tuple[dict, dict, dict]:
    corpus_id = "-".join(paper_id.lower() for paper_id in paper_ids)
    config = {
        "schema_version": "0.1.0",
        "benchmark_id": "test-highambench",
        "frozen_environment": {
            "lean_toolchain": "leanprover/lean4:v4.29.0",
            "lean_commit": "3" * 40,
            "lean_binary_sha256": SHA_A,
            "mathlib_commit": "1" * 40,
            "numstability_commit": "2" * 40,
            "agent_id": "codex",
            "agent_version": "agent-v1",
            "agent_binary_sha256": SHA_B,
            "model_version": "model-v1",
            "model_reasoning_effort": "medium",
            "ultra_orchestration": copy.deepcopy(ULTRA_ORCHESTRATION),
            "prompt_sha256": SHA_A,
            "allowed_tools": ["shell", "Lean"],
            "hardware_class": "test-machine",
            "operating_system": "test-os",
            "environment_id": f"highambench-{corpus_id}-" + SHA_C[:16],
            "environment_bundle_sha256": SHA_C,
            "bubblewrap_binary_sha256": SHA_B,
            "bubblewrap_version": "bubblewrap 1.0",
            "numstability_source_manifest": "metadata/library_source.json",
            "numstability_source_manifest_sha256": SHA_A,
            "numstability_compiled_manifest": "metadata/library_olean.json",
            "numstability_compiled_manifest_sha256": SHA_C,
            "compiled_environment_summary": "metadata/packages_olean.json",
            "compiled_environment_summary_sha256": SHA_B,
            "packages_runtime_manifest": "metadata/packages_runtime.json",
            "packages_runtime_manifest_sha256": SHA_A,
            "python_version": PYTHON_VERSION,
            "python_binary_sha256": PYTHON_SHA256,
            "release_manifest": "metadata/release_files.json",
            "release_manifest_sha256": SHA_C,
            "token_control_canary": token_canary_descriptor(),
            "ultra_orchestration_canary": ultra_canary_descriptor(),
            "container_image_digest": None if bubblewrap else "sha256:" + SHA_C,
        },
        "limits": {
            "wall_clock_seconds": 100,
            "total_model_tokens": 5_000_000,
            "failure_scored_time_seconds": 100,
        },
        "token_control": token_control_record(5_000_000),
        "repetitions": [{"id": "rep-01", "backend_seed": backend_seed}],
        "planned_counts_per_agent": {
            "papers": len(paper_ids),
            "tasks": 3 * len(paper_ids),
            "repetitions_per_task": 1,
            "conditions": 2,
            "paired_assignments": 3 * len(paper_ids),
            "runs": 6 * len(paper_ids),
        },
        "isolation": (
            {
                "implementation": "fresh bubblewrap mount and process namespaces per run",
                "model_shell_network": "blocked inside the namespace",
                "codex_control_process_network": "provider connection retained outside namespace",
            }
            if bubblewrap
            else {"implementation": "frozen OCI container"}
        ),
    }
    papers = []
    for paper_index, paper_id in enumerate(paper_ids):
        targets = []
        for tier in ("T1", "T2", "T3"):
            task_id = f"task-{tier}" if paper_index == 0 else f"task-{paper_id}-{tier}"
            target_file = (
                f"targets/{tier}.lean"
                if paper_index == 0
                else f"targets/{paper_id}/{tier}.lean"
            )
            targets.append(
                {
                    "task_id": task_id,
                    "tier": tier,
                    "lean_target": {
                        "file": target_file,
                        "controlled_file_sha256": SHA_B,
                    },
                }
            )
        papers.append(
            {
                "paper_id": paper_id,
                "source": {
                    "local_path": (
                        "paper.pdf" if paper_index == 0 else f"paper-{paper_id}.pdf"
                    ),
                    "sha256": SHA_C,
                },
                "targets": targets,
            }
        )
    manifest = {
        "schema_version": "0.1.0",
        "benchmark_id": "test-highambench",
        "specification": {"local_path": "spec.pdf", "sha256": SHA_A},
        "papers": papers,
        "controlled_shared_files": [
            {"path": "shared/Definitions.lean", "sha256": SHA_A}
        ],
    }
    pairs = []
    for paper in papers:
        for target in paper["targets"]:
            task_id = target["task_id"]
            repetition_id = "rep-01"
            digest = hashlib.sha256(
                f"{SALT}|{task_id}|{repetition_id}".encode("utf-8")
            ).hexdigest()
            order = ["N", "L"] if int(digest[:2], 16) % 2 == 0 else ["L", "N"]
            pair_id = f"{task_id}-{repetition_id}"
            pairs.append(
                {
                    "pair_id": pair_id,
                    "task_id": task_id,
                    "repetition_id": repetition_id,
                    "sha256": digest,
                    "condition_order": order,
                    "run_ids": [f"{pair_id}-{condition}" for condition in order],
                }
            )
    run_order = {
        "schema_version": "0.1.0",
        "benchmark_id": "test-highambench",
        "method": {"name": "sha256_first_byte_parity", "salt": SALT},
        "pairs": pairs,
    }
    return config, manifest, run_order


def result_records(
    config: dict,
    manifest: dict,
    run_order: dict,
    *,
    observational: bool = False,
) -> list[dict]:
    task_metadata = {
        target["task_id"]: {
            "tier": target["tier"],
            "paper_id": paper["paper_id"],
            "paper_sha256": paper["source"]["sha256"],
        }
        for paper in manifest["papers"]
        for target in paper["targets"]
    }
    seed = config["repetitions"][0]["backend_seed"]
    frozen = config["frozen_environment"]
    freeze_check = {
        "schema_version": 1,
        "kind": "highambench-frozen-run-verification",
        "ok": True,
        "benchmark_id": config["benchmark_id"],
        "environment_id": frozen["environment_id"],
        "environment_bundle_sha256": frozen["environment_bundle_sha256"],
        "agent": {
            "id": frozen["agent_id"],
            "version": frozen["agent_version"],
            "binary_sha256": frozen["agent_binary_sha256"],
            "model": frozen["model_version"],
            "reasoning_effort": frozen["model_reasoning_effort"],
            "ultra_orchestration": copy.deepcopy(frozen["ultra_orchestration"]),
        },
        "python": {
            "version": frozen["python_version"],
            "binary_sha256": frozen["python_binary_sha256"],
        },
        "token_control": copy.deepcopy(config["token_control"]),
        "token_control_canary": token_canary_summary(
            frozen["token_control_canary"]
        ),
        "ultra_orchestration_canary": ultra_canary_summary(
            frozen["ultra_orchestration_canary"]
        ),
        "lean": {
            "version": "4.29.0",
            "commit": frozen["lean_commit"],
            "binary_sha256": frozen["lean_binary_sha256"],
            "mathlib_commit": frozen["mathlib_commit"],
            "numstability_commit": frozen["numstability_commit"],
            "compiled_files_verified": 1,
            "source_files_verified": 1,
        },
        "limits": {
            "wall_clock_seconds": config["limits"]["wall_clock_seconds"],
            "total_model_tokens": config["limits"]["total_model_tokens"],
        },
        "bubblewrap": {
            "version": frozen["bubblewrap_version"],
            "binary_sha256": frozen["bubblewrap_binary_sha256"],
        },
        "compiled_environment_summary": {
            "sha256": frozen["compiled_environment_summary_sha256"],
            "toolchain_file_count": 1,
            "package_count": 1,
            "package_file_count": 1,
        },
        "packages_runtime": {
            "path": frozen["packages_runtime_manifest"],
            "sha256": frozen["packages_runtime_manifest_sha256"],
            "file_count": 3,
            "source_file_count": 1,
            "olean_file_count": 1,
            "compiled_support_file_count": 1,
            "verification": {
                "ok": True,
                "verified": 3,
                "expected": 3,
                "missing": [],
                "changed": [],
            },
        },
        "host_class": {
            "kernel": "test-os",
            "virtualization": "TEST",
            "cpu_vendor": "test-vendor",
            "processor": "test-cpu",
            "cpu_family": 1,
            "cpu_model": 2,
            "cpu_stepping": 3,
            "online_logical_cpus": 1,
            "allocated_physical_cores": 1,
            "allocated_sockets": 1,
            "allocated_threads_per_core": [1],
            "visible_memory_bytes": 1,
            "allocation_memory_limit_bytes": 1,
            "slurm_num_nodes": 1,
            "slurm_num_cpus": 1,
            "slurm_num_tasks": 1,
            "slurm_cpus_per_task": 1,
            "slurm_allocated_memory_bytes": 1,
        },
        "release_manifest": {
            "sha256": frozen["release_manifest_sha256"],
            "file_count": 1,
            "verification": {
                "ok": True,
                "verified": 1,
                "expected": 1,
                "missing": [],
                "changed": [],
            },
        },
        "metadata_document_sha256": {
            "config": hashlib.sha256(
                json.dumps(config, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "manifest": hashlib.sha256(
                json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "run_order": hashlib.sha256(
                json.dumps(run_order, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "environment": SHA_A,
        },
    }
    freeze_digest = hashlib.sha256(
        json.dumps(freeze_check, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    records: list[dict] = []
    epoch = dt.datetime(2026, 7, 25, tzinfo=dt.timezone.utc)
    for pair_number, pair in enumerate(run_order["pairs"]):
        task = task_metadata[pair["task_id"]]
        pair_start = epoch + dt.timedelta(minutes=pair_number)
        pair_order = "N-first" if pair["condition_order"][0] == "N" else "L-first"
        for order_index, (condition, run_id) in enumerate(
            zip(pair["condition_order"], pair["run_ids"], strict=True), start=1
        ):
            started = pair_start + dt.timedelta(seconds=(order_index - 1) * 20)
            finished = started + dt.timedelta(seconds=10)
            model_tokens = 60 if condition == "N" else 40
            input_tokens = 40 if condition == "N" else 25
            output_tokens = model_tokens - input_tokens
            response_ids = [f"{run_id}-response-1", f"{run_id}-response-2"]
            usage_totals = {
                "input_tokens": input_tokens,
                "cached_input_tokens": 5,
                "cache_write_input_tokens": 0,
                "output_tokens": output_tokens,
                "reasoning_output_tokens": min(3, output_tokens),
                "total_tokens": model_tokens,
            }
            zero_usage = {field: 0 for field in usage_totals}
            usage_reconciliation = {
                "schema_version": (
                    result_set_module.run_matrix.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
                ),
                "provider_response_count": 2,
                "appserver_response_count": 2,
                "suppressed_collaboration_wait_response_count": 0,
                "provider_usage": copy.deepcopy(usage_totals),
                "appserver_usage": copy.deepcopy(usage_totals),
                "suppressed_collaboration_wait_usage": zero_usage,
                "provider_response_ids": list(response_ids),
                "appserver_response_ids": list(response_ids),
                "suppressed_collaboration_wait_response_ids": [],
                "suppressed_collaboration_wait_evidence": [],
                **empty_reconciliation_v3_delivery_fields(zero_usage),
            }
            observed_at_unix_ns = int(
                (started + dt.timedelta(seconds=5)).timestamp() * 1_000_000_000
            )
            claims = {
                "fresh_conversation": True,
                "filesystem_isolated": True,
                "network_disabled": True,
                "backend_seed_supplied": seed is not None,
                "seed_enforced_by_agent": seed is not None and not observational,
                "token_limit_enforced_by_agent": not observational,
                "condition_l_library_available": True,
            }
            notes = []
            if observational:
                if seed is None:
                    notes.append("no backend seed was supplied")
                notes.append("provider controls do not enforce the token limit")
            records.append(
                {
                    "schema_version": 1,
                    "kind": "highambench-run",
                    "run_id": run_id,
                    "pair_id": pair["pair_id"],
                    "paper_id": task["paper_id"],
                    "paper_sha256": task["paper_sha256"],
                    "task_id": pair["task_id"],
                    "tier": task["tier"],
                    "condition": condition,
                    "repetition_id": pair["repetition_id"],
                    "backend_seed": seed,
                    "pair_order": pair_order,
                    "order_index": order_index,
                    "agent": {
                        "id": "codex",
                        "version": "agent-v1",
                        "model": "model-v1",
                        "reasoning_effort": "medium",
                    },
                    "environment_id": config["frozen_environment"]["environment_id"],
                    "frozen_run_verification": {
                        "freeze_check_sha256": freeze_digest,
                        "freeze_check": copy.deepcopy(freeze_check),
                    },
                    "limits": {
                        "time_seconds": 100,
                        "model_tokens": config["limits"]["total_model_tokens"],
                    },
                    "started_at_utc": started.isoformat(),
                    "finished_at_utc": finished.isoformat(),
                    "useful_work_started": True,
                    "agent_exit_code": 0,
                    "pass": True,
                    "scored": not observational,
                    "failure_code": None,
                    "failure_note": "",
                    "actual_stop_seconds": 12 if condition == "N" else 7,
                    "scored_elapsed_seconds": 12 if condition == "N" else 7,
                    "token_usage": {
                        "input_tokens": input_tokens,
                        "cached_input_tokens": 5,
                        "cache_write_input_tokens": 0,
                        "output_tokens": output_tokens,
                        "reasoning_output_tokens": min(3, output_tokens),
                        "model_tokens": model_tokens,
                        "call_count": 2,
                        "response_count": 2,
                        "response_ids": list(response_ids),
                        "provider_response_count": 2,
                        "provider_response_ids": list(response_ids),
                        "provider_usage": copy.deepcopy(usage_totals),
                        "appserver_response_count": 2,
                        "appserver_response_ids": list(response_ids),
                        "appserver_response_ledger": [
                            {"response_id": response_id}
                            for response_id in response_ids
                        ],
                        "appserver_usage": copy.deepcopy(usage_totals),
                        "suppressed_collaboration_wait_response_count": 0,
                        "suppressed_collaboration_wait_response_ids": [],
                        "suppressed_collaboration_wait_usage": copy.deepcopy(
                            zero_usage
                        ),
                        "suppressed_collaboration_wait_evidence": [],
                        "superseded_by_collaboration_message_response_count": 0,
                        "superseded_by_collaboration_message_response_ids": [],
                        "superseded_by_collaboration_message_usage": copy.deepcopy(
                            zero_usage
                        ),
                        "superseded_by_collaboration_message_evidence": [],
                        "discarded_after_explicit_child_interrupt_response_count": 0,
                        "discarded_after_explicit_child_interrupt_response_ids": [],
                        "discarded_after_explicit_child_interrupt_usage": copy.deepcopy(
                            zero_usage
                        ),
                        "discarded_after_explicit_child_interrupt_evidence": [],
                        "provider_usage_reconciliation": usage_reconciliation,
                        "thread_count": 2,
                        "thread_accounting": [
                            {
                                "thread_id": (
                                    f"root-{pair['pair_id']}-{condition}"
                                ),
                                "parent_thread_id": None,
                                "agent_path": "/root",
                            },
                            {
                                "thread_id": (
                                    f"child-{pair['pair_id']}-{condition}"
                                ),
                                "parent_thread_id": (
                                    f"root-{pair['pair_id']}-{condition}"
                                ),
                                "agent_path": "/root/child",
                            },
                        ],
                        "measurement_source": "codex_app_server_rawResponse/completed",
                        "notification": "rawResponse/completed",
                        "usage_scope": (
                            "rooted_attempt_thread_tree_completed_responses"
                        ),
                        "live_cumulative": True,
                        "input_includes_cached": True,
                        "notification_sequence": 2,
                        "observed_at_unix_ns": observed_at_unix_ns,
                        "root_thread_id": f"root-{pair['pair_id']}-{condition}",
                        "drain_complete": True,
                        "measurement_exact": True,
                        "tree_quiescent": True,
                        "response_id_deduplicated": True,
                        "first_crossing": None,
                        "stop_reason": None,
                        "interrupt_requested": False,
                        "active_thread_ids": [],
                        "unresolved_thread_ids": [],
                        "invalid_reasons": [],
                    },
                    "token_measurement": {
                        "source": (
                            "Codex app-server rawResponse/completed exact "
                            "rooted-thread-tree ledger"
                        ),
                        "provider_cumulative_total_exact": True,
                        "cached_input_counted_once": True,
                        "measurement_error": None,
                        "trusted_usage_path_outside_workspace": True,
                        "post_submission_usage_established": True,
                        "capture_grace": {
                            "post_submission_usage_established": True,
                            "freshness_basis": "ultra_tree_quiescence_with_final_ledger",
                            "submission_detected_at_unix_ns": (
                                observed_at_unix_ns - 1
                            ),
                            "baseline_notification_sequence": None,
                            "captured_notification_sequence": 2,
                            "process_exited_during_grace": True,
                            "ultra_tree_drain": True,
                        },
                        "usage_scope": (
                            "rooted_attempt_thread_tree_completed_responses"
                        ),
                        "thread_count": 2,
                        "response_count": 2,
                        "tree_drain_complete": True,
                        "limit_enforcement": {
                            "mode": (
                                result_set_module.TOKEN_LIMIT_ENFORCEMENT_MODE
                            ),
                            "notification": "rawResponse/completed",
                            "configured_limit_tokens": config["limits"][
                                "total_model_tokens"
                            ],
                            "triggered": False,
                            "observed_tokens": None,
                            "overshoot_tokens": None,
                            "first_crossing_tokens": None,
                            "first_crossing_overshoot_tokens": None,
                            "final_endpoint_tokens": None,
                            "final_overshoot_tokens": None,
                            "checked_before_submission_validation": True,
                            "one_response_overshoot_possible": True,
                            "concurrent_inflight_overshoot_possible": False,
                        }
                    },
                    "library_use": condition == "L",
                    "library_declarations": (
                        ["NumStability.example"] if condition == "L" else []
                    ),
                    "submission_sha256": SHA_B,
                    "network_violation": {
                        "detected": False,
                        "event_count": 0,
                        "kernel_event_count": 0,
                        "saturated": False,
                        "integrity_ok": True,
                        "note": "no denied socket-related system call was recorded",
                        "saved_marker_log": None,
                        "marker_sha256": None,
                    },
                    "n_preflight": (
                        {
                            "ok": True,
                            "complete": True,
                            "controlled_task_staging": {
                                "manifest_sha256": SHA_A,
                                "verified_files": 4,
                                "expected_files": 4,
                                "complete": True,
                            },
                            "filesystem_scan": {
                                "root": ".",
                                "markers": ["NumStability", "numStability"],
                                "regular_file_count": 5,
                                "directory_count": 2,
                                "symlink_count": 0,
                                "content_limit_bytes": 4194304,
                            },
                            "filesystem_leaks": [],
                            "import_probe": {"reliable": True, "importable": False},
                        }
                        if condition == "N"
                        else None
                    ),
                    "protocol": {
                        "complete": not observational,
                        "claims": claims,
                        "verified": {
                            "fresh_workspace_copy": True,
                            "condition_n_preflight": True,
                            "condition_n_import_probe_complete": True,
                            "network_violation_marker_integrity": True,
                        },
                        "notes": notes,
                    },
                }
            )
    authenticate_matrix_records(records)
    return records


def refresh_freeze_evidence(
    records: list[dict],
    config: dict,
    manifest: dict,
    run_order: dict,
    *,
    environment: dict | None = None,
) -> None:
    frozen = config["frozen_environment"]
    freeze_check = copy.deepcopy(
        records[0]["frozen_run_verification"]["freeze_check"]
    )
    freeze_check["benchmark_id"] = config["benchmark_id"]
    freeze_check["environment_id"] = frozen["environment_id"]
    freeze_check["environment_bundle_sha256"] = frozen["environment_bundle_sha256"]
    freeze_check["release_manifest"]["sha256"] = frozen["release_manifest_sha256"]
    freeze_check["agent"].update(
        id=frozen["agent_id"],
        version=frozen["agent_version"],
        binary_sha256=frozen["agent_binary_sha256"],
        model=frozen["model_version"],
        reasoning_effort=frozen["model_reasoning_effort"],
        ultra_orchestration=copy.deepcopy(frozen["ultra_orchestration"]),
    )
    freeze_check["python"] = {
        "version": frozen["python_version"],
        "binary_sha256": frozen["python_binary_sha256"],
    }
    freeze_check["token_control"] = copy.deepcopy(config["token_control"])
    descriptor = frozen.get("token_control_canary")
    if isinstance(descriptor, dict):
        freeze_check["token_control_canary"].update(
            path=descriptor.get("path"),
            sha256=descriptor.get("sha256"),
            status=descriptor.get("status"),
        )
    ultra_descriptor = frozen.get("ultra_orchestration_canary")
    if isinstance(ultra_descriptor, dict):
        freeze_check["ultra_orchestration_canary"].update(
            path=ultra_descriptor.get("path"),
            sha256=ultra_descriptor.get("sha256"),
            status=ultra_descriptor.get("status"),
        )
    freeze_check["lean"].update(
        commit=frozen["lean_commit"],
        binary_sha256=frozen["lean_binary_sha256"],
        mathlib_commit=frozen["mathlib_commit"],
        numstability_commit=frozen["numstability_commit"],
    )
    freeze_check["limits"] = {
        "wall_clock_seconds": config["limits"]["wall_clock_seconds"],
        "total_model_tokens": config["limits"]["total_model_tokens"],
    }
    freeze_check["bubblewrap"] = {
        "version": frozen["bubblewrap_version"],
        "binary_sha256": frozen["bubblewrap_binary_sha256"],
    }
    freeze_check["compiled_environment_summary"]["sha256"] = frozen[
        "compiled_environment_summary_sha256"
    ]
    freeze_check["packages_runtime"]["path"] = frozen[
        "packages_runtime_manifest"
    ]
    freeze_check["packages_runtime"]["sha256"] = frozen[
        "packages_runtime_manifest_sha256"
    ]
    if environment is not None and isinstance(environment.get("host_class"), dict):
        freeze_check["host_class"] = copy.deepcopy(environment["host_class"])
    freeze_check["metadata_document_sha256"] = {
        "config": hashlib.sha256(
            json.dumps(config, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "manifest": hashlib.sha256(
            json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "run_order": hashlib.sha256(
            json.dumps(run_order, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "environment": (
            hashlib.sha256(
                json.dumps(environment, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest()
            if environment is not None
            else SHA_A
        ),
    }
    freeze_digest = hashlib.sha256(
        json.dumps(freeze_check, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    for record in records:
        record["environment_id"] = frozen["environment_id"]
        record["frozen_run_verification"] = {
            "freeze_check_sha256": freeze_digest,
            "freeze_check": copy.deepcopy(freeze_check),
        }
    authenticate_matrix_records(records)


class ResultSetTests(unittest.TestCase):
    def test_prompt_release_chain_authenticates_origin_wire_deadline_and_files(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            logs = root / "results" / "logs"
            logs.mkdir(parents=True)
            usage_path = logs / "run-1.usage.json"
            prompt = "Solve the fixed theorem.\n"
            prompt_bytes = prompt.encode()
            nonce = "d" * 64
            release_ns = 10_000_000_000
            common = {
                "schema_version": 1,
                "protocol_version": "highambench-prompt-release-v1",
                "handshake_nonce": nonce,
                "run_id": "run-1",
                "condition": "N",
                "model": "model-v1",
                "reasoning_effort": "ultra",
                "root_thread_id": "root-thread",
                "turn_start_request_id": 3,
                "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
                "effective_prompt_bytes": len(prompt_bytes),
                "adapter_name": "codex_isolated.py",
                "adapter_version": "1",
                "app_server_client_name": "highambench-isolated",
                "app_server_client_version": "1",
                "elapsed_clock": "CLOCK_MONOTONIC",
            }

            def signed(value: dict, field: str, path: Path) -> tuple[dict, dict]:
                record = copy.deepcopy(value)
                record[field] = hashlib.sha256(
                    json.dumps(
                        record, sort_keys=True, separators=(",", ":")
                    ).encode()
                ).hexdigest()
                payload = (
                    json.dumps(record, sort_keys=True, separators=(",", ":"))
                    + "\n"
                ).encode()
                path.write_bytes(payload)
                path.chmod(0o444)
                return record, {
                    "path": str(path),
                    "file_sha256": hashlib.sha256(payload).hexdigest(),
                    "record_sha256": record[field],
                    "record": copy.deepcopy(record),
                }

            ready_path = logs / "run-1.prompt-ready.json"
            go_path = logs / "run-1.prompt-go.json"
            release_path = logs / "run-1.prompt-release.json"
            ready, ready_descriptor = signed(
                {
                    **common,
                    "kind": "highambench_prompt_ready",
                    "turn_start_write_state": "not_started",
                    "ready_at_monotonic_ns": release_ns - 2_000_000,
                    "ready_at_unix_ns": 20_000_000_000,
                },
                "ready_sha256",
                ready_path,
            )
            go, go_descriptor = signed(
                {
                    **common,
                    "kind": "highambench_prompt_go",
                    "ready_sha256": ready["ready_sha256"],
                    "turn_start_write_authorized": True,
                    "authorized_at_monotonic_ns": release_ns - 1_000_000,
                    "authorized_at_unix_ns": 20_001_000_000,
                },
                "go_sha256",
                go_path,
            )
            wire = result_set_module._prompt_turn_start_wire(
                prompt=prompt,
                root_thread_id="root-thread",
                model="model-v1",
                reasoning_effort="ultra",
            )
            released, release_descriptor = signed(
                {
                    **common,
                    "kind": "highambench_prompt_released",
                    "ready_sha256": ready["ready_sha256"],
                    "go_sha256": go["go_sha256"],
                    "turn_start_write_state": "flushed",
                    "timestamp_capture_point": "immediately_before_turn_start_write",
                    "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
                    "turn_start_request_bytes": len(wire),
                    "released_at_monotonic_ns": release_ns,
                    "released_at_unix_ns": 20_002_000_000,
                    "turn_start_flushed_at_monotonic_ns": release_ns + 1,
                    "turn_start_flushed_at_unix_ns": 20_002_000_001,
                },
                "release_sha256",
                release_path,
            )
            request_path = logs / "run-1.submission-request.json"
            request, request_descriptor = signed(
                {
                    "schema_version": 1,
                    "kind": "highambench_submission_request",
                    "request_published_at_monotonic_ns": release_ns + 600_000_000,
                    "request_published_at_unix_ns": 20_602_000_000,
                },
                "request_sha256",
                request_path,
            )
            run = {
                "run_id": "run-1",
                "condition": "N",
                "pass": True,
                "first_valid_seconds": 0.6,
                "actual_stop_seconds": 0.7,
                "scored_elapsed_seconds": 0.6,
                "time_measurement": (
                    "authenticated CLOCK_MONOTONIC turn/start write to authenticated "
                    "nested submission-boundary publication after outer exec "
                    "raw-response completion with inner submit_proof blocked; hidden "
                    "validation certifies the immutable requested bytes"
                ),
                "agent": {
                    "model": "model-v1",
                    "reasoning_effort": "ultra",
                },
                "agent_command": [
                    "adapter",
                    "--usage-output",
                    str(usage_path),
                    "--prompt-ready-output",
                    str(ready_path),
                    "--prompt-go-input",
                    str(go_path),
                    "--prompt-release-output",
                    str(release_path),
                    "--prompt-handshake-nonce",
                    nonce,
                    "--prompt-run-id",
                    "run-1",
                ],
                "token_usage": {
                    "root_thread_id": "root-thread",
                    "submission_boundary": {
                        "request_sha256": request["request_sha256"],
                        "outer_raw_item_observed_at_monotonic_ns": (
                            release_ns + 100_000_000
                        ),
                        "request_published_at_monotonic_ns": (
                            release_ns + 600_000_000
                        ),
                        "request_published_at_unix_ns": 20_602_000_000,
                    },
                },
                "ultra_submission_boundary": {
                    "artifacts": {"request": request_descriptor}
                },
                "protocol": {"verified": {"authenticated_prompt_release": True}},
                "prompt_release": {
                    "schema_version": 1,
                    "protocol_version": "highambench-prompt-release-v1",
                    "required": True,
                    "status": "released_authenticated",
                    "authenticated": True,
                    "timing_exact": True,
                    "useful_work_basis": "authenticated_release",
                    "startup_timeout_seconds": 120.0,
                    "startup_timeout_triggered": False,
                    "go_minimum_release_window_seconds": 5.0,
                    "handshake_nonce": nonce,
                    "elapsed_clock": "CLOCK_MONOTONIC",
                    "artifact_paths": {
                        "ready": str(ready_path),
                        "go": str(go_path),
                        "release": str(release_path),
                    },
                    "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
                    "effective_prompt_bytes": len(prompt_bytes),
                    "ready": ready_descriptor,
                    "go": go_descriptor,
                    "released": release_descriptor,
                    "stale_artifacts_removed": [],
                    "error": None,
                },
            }
            config = {
                "limits": {
                    "prompt_startup_timeout_seconds": 120,
                    "wall_clock_seconds": 100,
                },
                "frozen_environment": {"model_reasoning_effort": "ultra"},
            }
            errors: list[str] = []
            audit = _check_prompt_release_authentication(
                run, config, prompt, errors, repository_root=root
            )
            self.assertEqual(errors, [])
            self.assertTrue(audit["valid"])
            self.assertTrue(audit["artifact_content_verified"])
            self.assertEqual(
                audit["measurement_deadline_monotonic_ns"],
                release_ns + 100_000_000_000,
            )
            self.assertTrue(audit["ultra_request_publication_timing_verified"])

            release_path.chmod(0o644)
            release_path.write_bytes(release_path.read_bytes() + b" ")
            errors = []
            tampered = _check_prompt_release_authentication(
                run, config, prompt, errors, repository_root=root
            )
            self.assertFalse(tampered["valid"])
            self.assertFalse(tampered["artifact_content_verified"])
            self.assertTrue(
                any("0444" in error or "canonical" in error for error in errors),
                errors,
            )

    def test_matrix_final_record_self_hash_is_mandatory(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        summary = check["matrix_record_authentication"]
        self.assertTrue(summary["all_selected_final_records_authenticated"])
        self.assertEqual(
            summary["authenticated_final_record_count"], len(records)
        )

        tampered = copy.deepcopy(records)
        tampered[0]["failure_note"] = "changed after matrix authentication"
        changed = check_result_set(
            tampered,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(changed["ok"])
        self.assertTrue(
            any("matrix_record_sha256" in error for error in changed["errors"])
        )

        missing = copy.deepcopy(records)
        missing[0].pop("matrix_record_sha256")
        absent = check_result_set(
            missing,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(absent["ok"])

        wrong_attempt = copy.deepcopy(records)
        authenticate_matrix_record(wrong_attempt[0], attempt=3)
        invalid_attempt = check_result_set(
            wrong_attempt,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(invalid_attempt["ok"])
        self.assertTrue(
            any("matrix_attempt" in error for error in invalid_attempt["errors"])
        )

    def test_projection_v4_accepts_boundary_and_natural_drain(self) -> None:
        accepted = _derive_ultra_accounting_projection(
            projection_usage(accepted=True)
        )
        self.assertEqual(accepted["outcome"], "accepted_boundary")
        self.assertEqual(accepted["nonzero_inherited_child_baseline_count"], 1)

        natural = _derive_ultra_accounting_projection(
            projection_usage(accepted=False)
        )
        self.assertEqual(natural["outcome"], "natural_drain")
        self.assertEqual(natural["resolved_spawn_count"], 1)

        wrong_natural_teardown = projection_usage(accepted=False)
        wrong_natural_teardown["adapter_teardown"]["immediate"] = True
        with self.assertRaisesRegex(ValueError, "clean teardown"):
            _derive_ultra_accounting_projection(wrong_natural_teardown)

        wrong_accepted_teardown = projection_usage(accepted=True)
        wrong_accepted_teardown["adapter_teardown"]["immediate"] = False
        with self.assertRaisesRegex(ValueError, "clean teardown"):
            _derive_ultra_accounting_projection(wrong_accepted_teardown)

    def test_projection_v3_rejects_spawn_cumulative_and_hook_tamper(self) -> None:
        bad_spawn = projection_usage(accepted=True)
        bad_spawn["activity_spawn_call_ids"] = ["other-call"]
        with self.assertRaisesRegex(ValueError, "accounting|fork-policy"):
            _derive_ultra_accounting_projection(bad_spawn)

        bad_projection = projection_usage(accepted=False)
        child = bad_projection["thread_accounting"][1]
        child["last_cumulative"]["input_tokens"] += 1
        child["last_cumulative"]["total_tokens"] += 1
        with self.assertRaisesRegex(ValueError, "attestation"):
            _derive_ultra_accounting_projection(bad_projection)

        bad_hook = projection_usage(accepted=True)
        bad_hook["fork_policy"]["call_evidence"][0]["hook_completed_count"] = 2
        with self.assertRaisesRegex(ValueError, "hook binding"):
            _derive_ultra_accounting_projection(bad_hook)

        bad_helper = projection_usage(accepted=True)
        bad_helper["fork_policy"]["helper_sha256"] = SHA_A
        with self.assertRaisesRegex(ValueError, "freeze"):
            _derive_ultra_accounting_projection(bad_helper)

        bad_request_kind = projection_usage(accepted=True)
        bad_request_kind["appserver_response_ledger"][0]["provider_gate_call"][
            "request_metadata"
        ]["request_kind"] = "unknown"
        with self.assertRaisesRegex(ValueError, "delivery binding"):
            _derive_ultra_accounting_projection(bad_request_kind)

        bad_sse_receipt = projection_usage(accepted=True)
        bad_sse_receipt["appserver_response_ledger"][0]["provider_gate_call"][
            "upstream_sse_authentication"
        ]["downstream_content_type_synthesized"] = True
        with self.assertRaisesRegex(ValueError, "strict SSE authentication"):
            _derive_ultra_accounting_projection(bad_sse_receipt)

        reordered = projection_usage(accepted=True)
        reordered["response_ids"] = list(reversed(reordered["response_ids"]))
        with self.assertRaisesRegex(ValueError, "response IDs"):
            _derive_ultra_accounting_projection(reordered)

    def test_validation_authentication_and_byte_hash_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            authentication = {
                "schema_version": 1,
                "run_id": "run-1",
                "task_id": "task-T1",
                "candidate_sha256": SHA_A,
                "target_theorem": "target",
                "controlled_manifest_sha256": SHA_B,
                "validator_contract_sha256": SHA_C,
                "submission_request_sha256": SHA_B,
                "submission_sequence": 1,
            }
            validation = {
                "pass": True,
                "failure_code": None,
                "authentication": authentication,
            }
            validation["record_sha256"] = hashlib.sha256(
                json.dumps(
                    validation, sort_keys=True, separators=(",", ":")
                ).encode()
            ).hexdigest()
            path = root / "validation.json"
            path.write_text(json.dumps(validation, sort_keys=True) + "\n", encoding="utf-8")
            payload_hash = hashlib.sha256(path.read_bytes()).hexdigest()
            run = {
                "run_id": "run-1",
                "task_id": "task-T1",
                "pass": True,
                "failure_code": None,
                "submission_sha256": SHA_A,
                "final_submission_sha256": SHA_A,
                "validation_log": str(path),
                "validation_log_sha256": payload_hash,
                "validation_record_sha256": validation["record_sha256"],
                "ultra_submission_boundary": {
                    "verified": True,
                    "request_sha256": SHA_B,
                    "sequence": 1,
                },
                "token_usage": {
                    "submission_boundary": {
                        "request_sha256": SHA_B,
                        "sequence": 1,
                        "validator_contract_sha256": SHA_C,
                        "candidate_sha256": SHA_A,
                    }
                },
            }
            errors: list[str] = []
            _check_validation_authentication(
                run,
                {"target_theorem": "target"},
                {"frozen_environment": {"model_reasoning_effort": "ultra"}},
                errors,
                controlled_manifest_sha256=SHA_B,
                repository_root=root,
            )
            self.assertEqual(errors, [])

            path.write_bytes(path.read_bytes() + b" ")
            errors = []
            _check_validation_authentication(
                run,
                {"target_theorem": "target"},
                {"frozen_environment": {"model_reasoning_effort": "ultra"}},
                errors,
                controlled_manifest_sha256=SHA_B,
                repository_root=root,
            )
            self.assertTrue(any("byte hash" in error for error in errors), errors)

    def test_ultra_canary_uses_exact_blocked_boundary_not_a_tree_drain(self) -> None:
        descriptor = ultra_canary_descriptor()
        summary = ultra_canary_summary(descriptor)
        self.assertTrue(_valid_ultra_canary_summary(summary, descriptor))
        drained = copy.deepcopy(summary)
        drained["drain_complete"] = True
        self.assertFalse(_valid_ultra_canary_summary(drained, descriptor))

    def authenticated_ultra_boundary_fixture(
        self, root: Path
    ) -> tuple[dict, dict, dict[str, Path]]:
        run_id = "P01-T1-rep-01-N"
        candidate = b"theorem boundary_fixture : True := by trivial\n"
        candidate_sha = hashlib.sha256(candidate).hexdigest()
        attempt_nonce = "attempt-fixture"
        validator_sha = "d" * 64

        def signed(value: dict, field: str) -> dict:
            result = copy.deepcopy(value)
            result[field] = hashlib.sha256(
                json.dumps(
                    result, sort_keys=True, separators=(",", ":"), ensure_ascii=False
                ).encode("utf-8")
            ).hexdigest()
            return result

        common = {
            "schema_version": result_set_module.SUBMISSION_BARRIER_SCHEMA_VERSION,
            "attempt_nonce": attempt_nonce,
            "run_id": run_id,
            "validator_contract_sha256": validator_sha,
            **result_set_module.ultra_canary.codex_isolated.nested_submission_exec_yield_record(),
        }
        challenge = signed(
            {**common, "kind": "highambench_submission_challenge"},
            "challenge_sha256",
        )
        call = signed(
            {
                **common,
                **nested_submission_wire_fixture(),
                "kind": "highambench_submission_call",
                "sequence": 1,
                "challenge_sha256": challenge["challenge_sha256"],
                "candidate_path": "Candidate.lean",
                "candidate_sha256": candidate_sha,
                "candidate_size_bytes": len(candidate),
            },
            "call_sha256",
        )
        request = signed(
            {
                **common,
                **nested_submission_wire_fixture(),
                "kind": "highambench_submission_request",
                "sequence": 1,
                "challenge_sha256": challenge["challenge_sha256"],
                "call_sha256": call["call_sha256"],
                "candidate_path": "Candidate.lean",
                "candidate_sha256": candidate_sha,
                "candidate_size_bytes": len(candidate),
                "captured_at_monotonic_ns": 8_000_000_000,
                "raw_response_observed_at_monotonic_ns": 9_000_000_000,
                "request_published_at_monotonic_ns": 10_000_000_000,
                "request_published_at_unix_ns": 20_000_000_000,
                "raw_response_completed_before_boundary_publication": True,
                "submission_event_order": (
                    result_set_module.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
                ),
                "dynamic_call_observed_before_raw_response_completed": True,
                "raw_response_completed_before_dynamic_call_observed": False,
                "candidate_captured_at_dynamic_call": True,
                "root_only": True,
                "descendants_quiescent": True,
                "sole_model_tool_call_in_response": True,
                "outer_exec_final_raw_item": True,
                "inner_dynamic_call_observed": True,
                "inner_dynamic_item_started": True,
                "inner_submit_invocation_exact": True,
                "inner_submit_only_nested_tool_call": True,
            },
            "request_sha256",
        )
        ack = signed(
            {
                "schema_version": result_set_module.SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_ack",
                "sequence": 1,
                "request_sha256": request["request_sha256"],
                "candidate_sha256": candidate_sha,
                "decision": "accept",
            },
            "ack_sha256",
        )
        records = {
            "challenge": (challenge, "challenge_sha256"),
            "call": (call, "call_sha256"),
            "request": (request, "request_sha256"),
            "ack": (ack, "ack_sha256"),
        }
        artifacts: dict[str, dict] = {}
        paths: dict[str, Path] = {}
        for name, (record, hash_field) in records.items():
            path = root / f"usage.json.submit-{name}.json"
            path.write_text(json.dumps(record, sort_keys=True) + "\n", encoding="utf-8")
            path.chmod(0o444)
            paths[name] = path
            artifacts[name] = {
                "path": str(path),
                "record_sha256": record[hash_field],
                "file_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        snapshot = root / "usage.json.submit-candidate-1.lean"
        snapshot.write_bytes(candidate)
        snapshot.chmod(0o444)
        paths["snapshot"] = snapshot
        artifacts["snapshot"] = {
            "path": str(snapshot),
            "file_sha256": candidate_sha,
            "size_bytes": len(candidate),
        }
        boundary = {
            **nested_submission_wire_fixture(),
            "authenticated": True,
            "status": "accepted",
            "exact": True,
            "sequence": 1,
            "challenge_sha256": challenge["challenge_sha256"],
            "call_sha256": call["call_sha256"],
            "request_sha256": request["request_sha256"],
            "ack_sha256": ack["ack_sha256"],
            "attempt_nonce": attempt_nonce,
            "run_id": run_id,
            "validator_contract_sha256": validator_sha,
            "thread_id": "root-thread",
            "turn_id": "turn-1",
            "response_id": "response-1",
            "candidate_path": "Candidate.lean",
            "candidate_sha256": candidate_sha,
            "candidate_size_bytes": len(candidate),
            "request_published_at_monotonic_ns": 10_000_000_000,
            "request_published_at_unix_ns": 20_000_000_000,
            "raw_response_notification_sequence": 1,
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": (
                result_set_module.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
            "candidate_captured_at_dynamic_call": True,
            "current_response_cumulative_required": False,
            "root_only": True,
            "descendants_quiescent": True,
            "sole_model_tool_call_in_response": True,
            "outer_exec_final_raw_item": True,
            "inner_dynamic_call_observed": True,
            "inner_dynamic_item_started": True,
            "inner_submit_invocation_exact": True,
            "inner_submit_only_nested_tool_call": True,
            "inner_dynamic_call_left_blocked": True,
            "inner_dynamic_tool_response_sent": False,
            "outer_exec_output_emitted": False,
            "later_model_response_possible": False,
            "provider_gate_close": {
                "won": True,
                "requested_reason": "accepted_submission",
                "effective_reason": "accepted_submission",
                "phase": "CLOSED",
                "sequence": 1,
            },
        }
        run = {
            "run_id": run_id,
            "pass": True,
            "agent_exit_code": 0,
            "time_measurement": result_set_module.ULTRA_PASS_TIME_MEASUREMENT,
            "submission_sha256": candidate_sha,
            "final_submission_sha256": candidate_sha,
            "submission_changed_after_acceptance": False,
            "token_usage": {
                "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                "root_thread_id": "root-thread",
                "response_ids": ["response-1"],
                "notification_sequence": 1,
                "measurement_exact": True,
                "drain_complete": False,
                "tree_quiescent": False,
                "submission_boundary_exact": True,
                "submission_boundary": boundary,
                "stop_reason": "first_valid_proof",
                "interrupt_requested": False,
                "first_crossing": None,
                "active_thread_ids": ["root-thread"],
                "unresolved_thread_ids": [],
                "invalid_reasons": [],
            },
            "token_measurement": {
                "tree_drain_complete": False,
                "capture_grace": {
                    "freshness_basis": result_set_module.ULTRA_PASS_FRESHNESS_BASIS,
                    "captured_notification_sequence": 1,
                    "ultra_tree_drain": False,
                    "ultra_submission_boundary": True,
                },
            },
            "protocol": {
                "verified": {"authenticated_first_valid_proof_boundary": True}
            },
            "ultra_submission_boundary": {
                "verified": True,
                "sequence": 1,
                "request_sha256": request["request_sha256"],
                "ack_sha256": ack["ack_sha256"],
                "artifacts": artifacts,
            },
        }
        config = {"frozen_environment": {"model_reasoning_effort": "ultra"}}
        return config, run, paths

    def test_authenticated_ultra_pass_boundary_and_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            config, run, _paths = self.authenticated_ultra_boundary_fixture(root)
            errors: list[str] = []
            audit = _check_ultra_outcome_boundary(
                run, config, errors, repository_root=root
            )
            self.assertEqual(errors, [])
            self.assertEqual(audit["outcome"], "authenticated_pass_boundary")
            self.assertTrue(audit["artifact_content_verified"])

            for invalid_exit in (2, False, 0.0, None):
                with self.subTest(agent_exit_code=invalid_exit):
                    run["agent_exit_code"] = invalid_exit
                    errors = []
                    audit = _check_ultra_outcome_boundary(
                        run, config, errors, repository_root=root
                    )
                    self.assertEqual(audit["outcome"], "invalid_pass_boundary")
                    self.assertTrue(
                        any("clean adapter exit" in error for error in errors)
                    )

    def test_schema_v5_submission_event_orders_and_yield_wire_are_exact(self) -> None:
        base = {
            "raw_response_completed_before_boundary_publication": True,
            "captured_at_monotonic_ns": 10,
            "raw_response_observed_at_monotonic_ns": 11,
            "request_published_at_monotonic_ns": 12,
        }
        inner_first = {
            **base,
            "submission_event_order": (
                result_set_module.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
        }
        self.assertTrue(
            result_set_module._valid_submission_event_order(
                inner_first, derive_from_timestamps=True
            )
        )
        response_first = {
            **inner_first,
            "submission_event_order": (
                result_set_module.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
            ),
            "dynamic_call_observed_before_raw_response_completed": False,
            "raw_response_completed_before_dynamic_call_observed": True,
            "captured_at_monotonic_ns": 11,
            "raw_response_observed_at_monotonic_ns": 10,
        }
        self.assertTrue(
            result_set_module._valid_submission_event_order(
                response_first, derive_from_timestamps=True
            )
        )
        for changes in (
            {"submission_event_order": "invalid-order"},
            {"raw_response_completed_before_dynamic_call_observed": True},
            {
                "dynamic_call_observed_before_raw_response_completed": False,
                "raw_response_completed_before_dynamic_call_observed": False,
            },
            {"captured_at_monotonic_ns": 11},
            {"request_published_at_monotonic_ns": 10},
        ):
            malformed = {**inner_first, **changes}
            self.assertFalse(
                result_set_module._valid_submission_event_order(
                    malformed, derive_from_timestamps=True
                ),
                changes,
            )
        for stale_schema in (1, 2, 3):
            wire = {**nested_submission_wire_fixture(), "schema_version": stale_schema}
            self.assertFalse(result_set_module._valid_nested_submission_wire(wire))
        for changes in (
            {"submission_transport": "functions_exec_dynamic_submit_proof_v1"},
            {"outer_exec_yield_time_ms": 10_000},
            {"outer_exec_yield_margin_ms": 0},
            {"outer_exec_timer_starts_at_or_after_prompt_release": False},
            {"outer_exec_yield_exceeds_envelope": False},
        ):
            wire = {**nested_submission_wire_fixture(), **changes}
            self.assertFalse(result_set_module._valid_nested_submission_wire(wire))

    def test_exact_natural_ultra_failure_needs_no_submission_boundary(self) -> None:
        config = {"frozen_environment": {"model_reasoning_effort": "ultra"}}
        run = {
            "run_id": "P01-T1-rep-01-N",
            "pass": False,
            "agent_exit_code": 0,
            "token_usage": {
                "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                "measurement_exact": True,
                "drain_complete": True,
                "tree_quiescent": True,
                "submission_boundary_exact": False,
                "submission_boundary": None,
                "interrupt_requested": False,
                "active_thread_ids": [],
                "unresolved_thread_ids": [],
                "invalid_reasons": [],
            },
            "token_measurement": {"tree_drain_complete": True},
            "protocol": {
                "verified": {"authenticated_first_valid_proof_boundary": False}
            },
            "ultra_submission_boundary": {"verified": False},
        }
        errors: list[str] = []
        audit = _check_ultra_outcome_boundary(
            run, config, errors, repository_root=None
        )
        self.assertEqual(errors, [])
        self.assertEqual(audit["outcome"], "exact_natural_failure")

        run["failure_code"] = "TIME_LIMIT"
        errors = []
        audit = _check_ultra_outcome_boundary(
            run, config, errors, repository_root=None
        )
        self.assertEqual(audit["outcome"], "invalid_failure_boundary")
        self.assertTrue(any("exact natural" in error for error in errors))
        run.pop("failure_code")

        for invalid_exit in (2, False, 0.0, None):
            with self.subTest(agent_exit_code=invalid_exit):
                run["agent_exit_code"] = invalid_exit
                errors = []
                audit = _check_ultra_outcome_boundary(
                    run, config, errors, repository_root=None
                )
                self.assertEqual(audit["outcome"], "invalid_failure_boundary")
                self.assertTrue(any("clean adapter exit" in error for error in errors))
        run["agent_exit_code"] = 0

        run["token_usage"].update(
            measurement_exact=False,
            drain_complete=False,
            tree_quiescent=False,
            active_thread_ids=["root-thread"],
        )
        errors = []
        audit = _check_ultra_outcome_boundary(
            run, config, errors, repository_root=None
        )
        self.assertTrue(any("exact natural" in error for error in errors), errors)
        self.assertEqual(audit["outcome"], "invalid_failure_boundary")

    def test_authenticated_ultra_boundary_rejects_retained_artifact_tamper(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            config, run, paths = self.authenticated_ultra_boundary_fixture(root)
            paths["request"].chmod(0o644)
            paths["request"].write_bytes(paths["request"].read_bytes() + b" ")
            errors: list[str] = []
            audit = _check_ultra_outcome_boundary(
                run, config, errors, repository_root=root
            )
            self.assertFalse(audit["artifact_content_verified"])
            self.assertTrue(
                any("mode 0444" in error or "SHA-256" in error for error in errors),
                errors,
            )

    def test_signposted_prompt_provenance_binds_n_invisibility_and_l_supplement(self) -> None:
        protocol = {
            "condition_supplements": {
                "L": {
                    "path": "condition_prompts/L.md",
                    "sha256": SHA_A,
                    "bytes": 10,
                }
            }
        }
        expected_n = {
            "protocol_version": "signposted-library-v1",
            "condition": "N",
            "condition_supplement": None,
        }
        expected_l = {
            **expected_n,
            "condition": "L",
            "condition_supplement": protocol["condition_supplements"]["L"],
        }
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            n_run = {
                "run_id": "n-run",
                "condition": "N",
                "prompt_provenance": expected_n,
                "agent_command": ["adapter", "--condition", "N"],
            }
            errors: list[str] = []
            self.assertTrue(
                _check_prompt_provenance(
                    n_run,
                    expected_n,
                    protocol=protocol,
                    benchmark_root=root,
                    errors=errors,
                )
            )
            self.assertEqual(errors, [])

            l_run = {
                "run_id": "l-run",
                "condition": "L",
                "prompt_provenance": expected_l,
                "agent_command": [
                    "adapter",
                    "--condition",
                    "L",
                    "--condition-prompt-file",
                    str((root / "condition_prompts" / "L.md").resolve()),
                    "--condition-prompt-sha256",
                    SHA_A,
                ],
            }
            self.assertTrue(
                _check_prompt_provenance(
                    l_run,
                    expected_l,
                    protocol=protocol,
                    benchmark_root=root,
                    errors=errors,
                )
            )

            leaked_n = copy.deepcopy(n_run)
            leaked_n["agent_command"].extend(
                ["--condition-prompt-file", "/hidden/L.md"]
            )
            self.assertFalse(
                _check_prompt_provenance(
                    leaked_n,
                    expected_n,
                    protocol=protocol,
                    benchmark_root=root,
                    errors=errors,
                )
            )
            self.assertTrue(any("received L-only" in error for error in errors))

    def reference_fixture(self) -> tuple[dict, dict, dict, list[dict]]:
        config, manifest, run_order = benchmark_documents()
        return config, manifest, run_order, result_records(config, manifest, run_order)

    def test_live_cached_inclusive_token_limit_evidence_is_strict(self) -> None:
        def set_limit_state(
            record: dict,
            *,
            token_limit: int,
            model_tokens: int,
            token_failure: bool,
        ) -> None:
            output_tokens = 10
            record["token_usage"].update(
                input_tokens=model_tokens - output_tokens,
                cached_input_tokens=5,
                output_tokens=output_tokens,
                model_tokens=model_tokens,
            )
            usage = record["token_usage"]
            reconciled_totals = {
                "input_tokens": usage["input_tokens"],
                "cached_input_tokens": usage["cached_input_tokens"],
                "cache_write_input_tokens": usage["cache_write_input_tokens"],
                "output_tokens": usage["output_tokens"],
                "reasoning_output_tokens": usage["reasoning_output_tokens"],
                "total_tokens": usage["model_tokens"],
            }
            usage["provider_usage"] = copy.deepcopy(reconciled_totals)
            usage["appserver_usage"] = copy.deepcopy(reconciled_totals)
            usage["provider_usage_reconciliation"]["provider_usage"] = (
                copy.deepcopy(reconciled_totals)
            )
            usage["provider_usage_reconciliation"]["appserver_usage"] = (
                copy.deepcopy(reconciled_totals)
            )
            record["pass"] = not token_failure
            record["failure_code"] = "TOKEN_LIMIT" if token_failure else None
            record["failure_note"] = (
                "live cumulative token limit reached" if token_failure else ""
            )
            record["scored_elapsed_seconds"] = (
                100 if token_failure else record["actual_stop_seconds"]
            )
            record["token_measurement"]["post_submission_usage_established"] = (
                not token_failure
            )
            if token_failure:
                record["token_measurement"]["capture_grace"].update(
                    post_submission_usage_established=False,
                    freshness_basis=None,
                    submission_detected_at_unix_ns=None,
                    baseline_notification_sequence=None,
                    captured_notification_sequence=None,
                    process_exited_during_grace=False,
                )
            crossed = model_tokens >= token_limit
            crossing_tokens = min(model_tokens, token_limit + 1) if crossed else None
            record["token_usage"].update(
                first_crossing=(
                    {
                        "response_id": "response-at-cap",
                        "notification_sequence": 1,
                        "observed_at_unix_ns": record["token_usage"][
                            "observed_at_unix_ns"
                        ],
                        "tokens": crossing_tokens,
                        "active_thread_ids": [record["token_usage"]["root_thread_id"]],
                    }
                    if crossed
                    else None
                ),
                stop_reason="token_limit" if crossed else None,
            )
            record["token_measurement"]["limit_enforcement"].update(
                triggered=crossed,
                observed_tokens=crossing_tokens,
                overshoot_tokens=(crossing_tokens - token_limit) if crossed else None,
                first_crossing_tokens=crossing_tokens,
                first_crossing_overshoot_tokens=(
                    crossing_tokens - token_limit if crossed else None
                ),
                final_endpoint_tokens=model_tokens if crossed else None,
                final_overshoot_tokens=(model_tokens - token_limit) if crossed else None,
            )

        fixed_limit = 5_000_000
        for total in (fixed_limit, fixed_limit + 37):
            with self.subTest(valid_token_limit_total=total):
                config, manifest, run_order, records = self.reference_fixture()
                set_limit_state(
                    records[0],
                    token_limit=config["limits"]["total_model_tokens"],
                    model_tokens=total,
                    token_failure=True,
                )
                authenticate_matrix_record(records[0])
                check = check_result_set(
                    records,
                    run_order=run_order,
                    config=config,
                    manifest=manifest,
                )
                self.assertTrue(check["ok"], check["errors"])

        config, manifest, run_order, records = self.reference_fixture()
        set_limit_state(
            records[0],
            token_limit=config["limits"]["total_model_tokens"],
            model_tokens=1037,
            token_failure=True,
        )
        records[0]["failure_code"] = "TIME_LIMIT"
        authenticate_matrix_record(records[0])
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertTrue(check["ok"], check["errors"])

        invalid_cases: list[tuple[str, list[dict], str]] = []

        config, manifest, run_order, records = self.reference_fixture()
        set_limit_state(
            records[0],
            token_limit=fixed_limit,
            model_tokens=fixed_limit + 1,
            token_failure=False,
        )
        invalid_cases.append(("over-cap pass", records, "without pass=false"))

        _, _, _, records = self.reference_fixture()
        set_limit_state(
            records[0], token_limit=fixed_limit, model_tokens=fixed_limit, token_failure=False
        )
        invalid_cases.append(("at-cap pass", records, "without pass=false"))

        _, _, _, records = self.reference_fixture()
        set_limit_state(
            records[0],
            token_limit=fixed_limit,
            model_tokens=fixed_limit + 1,
            token_failure=True,
        )
        records[0]["failure_code"] = "PROOF_ERROR"
        invalid_cases.append(("over-cap non-token failure", records, "without pass=false"))

        _, _, _, records = self.reference_fixture()
        set_limit_state(
            records[0],
            token_limit=fixed_limit,
            model_tokens=fixed_limit - 1,
            token_failure=True,
        )
        invalid_cases.append(("token limit below cap", records, "below the fixed limit"))

        _, _, _, records = self.reference_fixture()
        set_limit_state(
            records[0],
            token_limit=fixed_limit,
            model_tokens=fixed_limit + 12,
            token_failure=True,
        )
        records[0]["token_measurement"]["limit_enforcement"][
            "overshoot_tokens"
        ] = 11
        invalid_cases.append(("wrong overshoot", records, "inconsistent token-limit overshoot"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_usage"]["input_includes_cached"] = False
        invalid_cases.append(("cached input double-count risk", records, "cached-inclusive"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["limit_enforcement"]["mode"] = (
            "completed_turn_total"
        )
        invalid_cases.append(
            ("not first live notification", records, "invalid live token-limit")
        )

        _, _, _, records = self.reference_fixture()
        records[0]["token_usage"]["notification_sequence"] = 0
        invalid_cases.append(("untrusted notification", records, "provenance field"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_usage"]["call_count"] = 3
        invalid_cases.append(
            ("mismatched response count", records, "deduplicated response accounting")
        )

        _, _, _, records = self.reference_fixture()
        records[0]["token_usage"]["response_id_deduplicated"] = False
        invalid_cases.append(
            ("response IDs not deduplicated", records, "deduplicated response accounting")
        )

        _, _, _, records = self.reference_fixture()
        records[0]["token_usage"]["tree_quiescent"] = False
        invalid_cases.append(
            ("root completion treated as barrier", records, "naturally drained Ultra tree")
        )

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["thread_count"] = 1
        invalid_cases.append(
            ("wrong descendant thread count", records, "tree-measurement metadata")
        )

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["limit_enforcement"][
            "one_response_overshoot_possible"
        ] = False
        invalid_cases.append(
            ("one-response Ultra bound", records, "limit enforcement metadata")
        )

        _, _, _, records = self.reference_fixture()
        records[0]["token_usage"]["observed_at_unix_ns"] = 1_000_000_000
        invalid_cases.append(("stale observation time", records, "outside its run"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["trusted_usage_path_outside_workspace"] = False
        invalid_cases.append(("workspace usage path", records, "trusted external"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["provider_cumulative_total_exact"] = False
        invalid_cases.append(("inexact provider total", records, "measurement metadata"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["post_submission_usage_established"] = False
        invalid_cases.append(("stale passing usage", records, "post-submission"))

        _, _, _, records = self.reference_fixture()
        records[0]["token_measurement"]["capture_grace"][
            "captured_notification_sequence"
        ] = 3
        invalid_cases.append(("mismatched capture sequence", records, "freshness evidence"))

        _, _, _, records = self.reference_fixture()
        records[0]["scored"] = False
        records[0]["token_usage"].pop("measurement_source")
        invalid_cases.append(("unscored missing live usage", records, "mixes Ultra"))

        for label, candidate_records, expected_error in invalid_cases:
            with self.subTest(invalid=label):
                check = check_result_set(
                    candidate_records,
                    run_order=run_order,
                    config=config,
                    manifest=manifest,
                )
                self.assertFalse(check["ok"], check)
                self.assertTrue(
                    any(expected_error in error for error in check["errors"]),
                    check,
                )

    def test_legacy_xhigh_token_schema_remains_readable_but_cannot_mix_with_ultra(
        self,
    ) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        legacy_control = {
            **token_control_record(1000),
            "control": "app_server_live_cumulative_usage",
            "measurement_source": "codex_app_server_thread/tokenUsage/updated",
            "notification": "thread/tokenUsage/updated",
            "usage_scope": "thread",
            "one_response_overshoot_possible": True,
            "trusted_adapter_freezes_first_threshold": True,
        }
        for field in (
            "concurrent_inflight_overshoot_possible",
            "all_descendant_threads_included",
            "response_ids_deduplicated",
            "outcome_exactness",
            "measurement_exact_required",
            "root_completion_is_tree_barrier",
            "trusted_adapter_latches_first_threshold",
            "provider_gate_protocol",
            "provider_response_bound_tokens",
            "strict_admission_inequality",
            "crossing_response_release",
            "crossing_response_actions_released",
            "provider_requests_quiescent_at_scored_endpoint",
            "tree_quiescence_distinct_from_provider_quiescence",
        ):
            legacy_control.pop(field, None)
        self.assertTrue(_valid_token_control(legacy_control, 1000))

        config["token_control"] = legacy_control
        run = records[0]
        usage = run["token_usage"]
        usage.update(
            call_count=1,
            measurement_source="codex_app_server_thread/tokenUsage/updated",
            notification_sequence=1,
        )
        for field in (
            "cache_write_input_tokens",
            "reasoning_output_tokens",
            "response_count",
            "thread_count",
            "notification",
            "usage_scope",
            "root_thread_id",
            "drain_complete",
            "measurement_exact",
            "tree_quiescent",
            "response_id_deduplicated",
            "first_crossing",
            "stop_reason",
            "interrupt_requested",
            "active_thread_ids",
            "unresolved_thread_ids",
            "invalid_reasons",
        ):
            usage.pop(field, None)
        measurement = run["token_measurement"]
        measurement.update(
            source=(
                "Codex app-server thread/tokenUsage/updated live cumulative notification"
            )
        )
        for field in (
            "usage_scope",
            "thread_count",
            "response_count",
            "tree_drain_complete",
        ):
            measurement.pop(field, None)
        capture = measurement["capture_grace"]
        capture.update(
            freshness_basis=(
                "trusted_notification_observed_at_or_after_submission_detection"
            ),
            captured_notification_sequence=1,
            process_exited_during_grace=False,
        )
        enforcement = measurement["limit_enforcement"]
        enforcement.update(
            mode="first_live_cumulative_update_at_or_above_limit",
            notification="thread/tokenUsage/updated",
            one_response_overshoot_possible=True,
            concurrent_inflight_overshoot_possible=False,
        )
        for field in (
            "first_crossing_tokens",
            "first_crossing_overshoot_tokens",
            "final_endpoint_tokens",
            "final_overshoot_tokens",
        ):
            enforcement.pop(field, None)

        errors: list[str] = []
        _check_token_usage(run, config, errors)
        self.assertEqual(errors, [])

        config["token_control"] = token_control_record(1000)
        mixed_errors: list[str] = []
        _check_token_usage(run, config, mixed_errors)
        self.assertTrue(any("frozen token-control schema" in item for item in mixed_errors))

    def test_frozen_token_control_names_live_outer_runner_as_enforcer(self) -> None:
        stale_controls = (
            {
                "feature": "rollout_budget",
                "feature_row": "rollout_budget under development false",
                "strict_config": True,
                "limit_tokens": 1000,
                "prefill_token_weight": 1,
                "sampling_token_weight": 1,
            },
            {
                **token_control_record(1000),
                "advisory_rollout_budget": {
                    **token_control_record(1000)["advisory_rollout_budget"],
                    "role": "enforcing",
                },
            },
            {
                **token_control_record(1000),
                "response_ids_deduplicated": False,
            },
            {
                **token_control_record(1000),
                "root_completion_is_tree_barrier": True,
            },
            {
                **token_control_record(1000),
                "one_response_overshoot_possible": False,
            },
        )
        for stale_control in stale_controls:
            with self.subTest(control=stale_control):
                config, manifest, run_order, records = self.reference_fixture()
                for record in records:
                    check = record["frozen_run_verification"]["freeze_check"]
                    check["token_control"] = copy.deepcopy(stale_control)
                    record["frozen_run_verification"]["freeze_check_sha256"] = (
                        hashlib.sha256(
                            json.dumps(
                                check, sort_keys=True, separators=(",", ":")
                            ).encode()
                        ).hexdigest()
                    )
                result = check_result_set(
                    records,
                    run_order=run_order,
                    config=config,
                    manifest=manifest,
                )
                self.assertFalse(result["ok"], result)
                self.assertTrue(
                    any(
                        "invalid token-control evidence" in error
                        for error in result["errors"]
                    ),
                    result,
                )

    def test_token_control_canary_descriptor_and_summary_are_mandatory(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()

        missing_summary = copy.deepcopy(records)
        for record in missing_summary:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"].pop("token_control_canary")
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"],
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest()
        result = check_result_set(
            missing_summary,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(result["ok"], result)
        self.assertTrue(
            any("invalid token-control canary summary" in error for error in result["errors"]),
            result,
        )

        wrong_prompt_deadline = copy.deepcopy(records)
        for record in wrong_prompt_deadline:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"]["token_control_canary"]["prompt_release"][
                "deadline_monotonic_ns"
            ] += 1
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"],
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest()
        result = check_result_set(
            wrong_prompt_deadline,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(result["ok"], result)
        self.assertTrue(
            any("invalid token-control canary summary" in error for error in result["errors"]),
            result,
        )

        bad_config = copy.deepcopy(config)
        bad_records = copy.deepcopy(records)
        bad_config["frozen_environment"]["token_control_canary"]["status"] = "failed"
        refresh_freeze_evidence(bad_records, bad_config, manifest, run_order)
        result = check_result_set(
            bad_records,
            run_order=run_order,
            config=bad_config,
            manifest=manifest,
        )
        self.assertFalse(result["ok"], result)
        self.assertTrue(
            any("canary descriptor" in error for error in result["errors"]),
            result,
        )

        wrong_root_cardinality = copy.deepcopy(records)
        for record in wrong_root_cardinality:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"]["token_control_canary"]["thread_count"] = 2
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"],
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest()
        result = check_result_set(
            wrong_root_cardinality,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(result["ok"], result)
        self.assertTrue(
            any("invalid token-control canary summary" in error for error in result["errors"]),
            result,
        )

    def test_token_canary_endpoint_must_equal_first_crossing(self) -> None:
        descriptor = token_canary_descriptor()
        summary = token_canary_summary(descriptor)
        token_limit = 5_000_000
        self.assertTrue(
            result_set_module._valid_token_canary_summary(
                summary, descriptor, token_limit
            )
        )

        summary["final_endpoint_tokens"] += 1
        self.assertFalse(
            result_set_module._valid_token_canary_summary(
                summary, descriptor, token_limit
            )
        )

        summary = token_canary_summary(descriptor)
        summary["accounting_projection"][
            "root_cumulative_projection_status"
        ] = "untrusted_status"
        projection = summary["accounting_projection"]
        unsigned = {
            key: value
            for key, value in projection.items()
            if key != "projection_payload_sha256"
        }
        projection["projection_payload_sha256"] = hashlib.sha256(
            json.dumps(unsigned, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        self.assertFalse(
            result_set_module._valid_token_canary_summary(
                summary, descriptor, token_limit
            )
        )

    def test_library_use_and_declaration_names_must_agree(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        l_run = next(run for run in records if run["condition"] == "L")
        l_run["library_declarations"] = []
        report = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("claims library use without" in error for error in report["errors"]),
            report,
        )

    def test_each_run_must_match_frozen_environment_and_reasoning_effort(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        wrong_environment = copy.deepcopy(records)
        wrong_environment[0]["environment_id"] = "claimed-but-unfrozen"
        check = check_result_set(
            wrong_environment, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("expected frozen" in error for error in check["errors"]))

        wrong_effort = copy.deepcopy(records)
        wrong_effort[0]["agent"]["reasoning_effort"] = "high"
        check = check_result_set(
            wrong_effort, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("reasoning_effort" in error for error in check["errors"]))

    def test_missing_mismatched_and_stale_freeze_evidence_is_rejected(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        missing = copy.deepcopy(records)
        missing[0].pop("frozen_run_verification")
        check = check_result_set(
            missing, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("mandatory frozen-run" in error for error in check["errors"]))

        altered = copy.deepcopy(records)
        altered[0]["frozen_run_verification"]["freeze_check_sha256"] = "0" * 64
        check = check_result_set(
            altered, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("stale or altered" in error for error in check["errors"]))

        stale_config = copy.deepcopy(config)
        stale_config["frozen_note"] = "changed after startup verification"
        check = check_result_set(
            records, run_order=run_order, config=stale_config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("stale for config" in error for error in check["errors"]))

        truncated = copy.deepcopy(records)
        for record in truncated:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"].pop("lean")
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"], sort_keys=True, separators=(",", ":")
                ).encode()
            ).hexdigest()
        check = check_result_set(
            truncated, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("Lean identity" in error for error in check["errors"]))

        missing_runtime = copy.deepcopy(records)
        for record in missing_runtime:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"].pop("packages_runtime")
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"], sort_keys=True, separators=(",", ":")
                ).encode()
            ).hexdigest()
        check = check_result_set(
            missing_runtime,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("packages-runtime evidence" in error for error in check["errors"])
        )

        wrong_python_config = copy.deepcopy(config)
        wrong_python_config["frozen_environment"]["python_version"] = "0.0.0"
        wrong_python_records = copy.deepcopy(records)
        refresh_freeze_evidence(
            wrong_python_records,
            wrong_python_config,
            manifest,
            run_order,
        )
        check = check_result_set(
            wrong_python_records,
            run_order=run_order,
            config=wrong_python_config,
            manifest=manifest,
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("current Python version" in error for error in check["errors"])
        )

    def test_complete_reference_matrix(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertFalse(check["production_canary_bindings_authenticated"])
        self.assertFalse(check["reference_compliant"])
        self.assertFalse(check["official_scores_valid"])
        self.assertEqual(check["analysis_profile"], "invalid")
        self.assertEqual(check["selected_final_record_count"], 6)
        self.assertEqual(check["expected_pairs_per_agent"], 3)
        with self.assertRaisesRegex(
            BenchmarkToolError, "both frozen live canaries were not authenticated"
        ):
            require_complete_result_set(check)

    def test_complete_two_paper_matrix_uses_corpus_environment_id(self) -> None:
        config, manifest, run_order = benchmark_documents(
            paper_ids=("P01", "P02")
        )
        records = result_records(config, manifest, run_order)
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertEqual(
            config["frozen_environment"]["environment_id"],
            "highambench-p01-p02-" + SHA_C[:16],
        )
        self.assertEqual(check["selected_final_record_count"], 12)
        self.assertEqual(check["expected_pairs_per_agent"], 6)

    def test_environment_id_rejects_stale_or_reordered_corpus_prefix(self) -> None:
        config, manifest, run_order = benchmark_documents(
            paper_ids=("P01", "P02")
        )
        records = result_records(config, manifest, run_order)

        stale_config = copy.deepcopy(config)
        stale_config["frozen_environment"]["environment_id"] = (
            "highambench-p01-" + SHA_C[:16]
        )
        stale_records = copy.deepcopy(records)
        refresh_freeze_evidence(stale_records, stale_config, manifest, run_order)
        stale_check = check_result_set(
            stale_records,
            run_order=run_order,
            config=stale_config,
            manifest=manifest,
        )
        self.assertFalse(stale_check["ok"])
        self.assertTrue(
            any(
                "expected 'highambench-p01-p02-" in error
                for error in stale_check["errors"]
            ),
            stale_check,
        )

        reordered_manifest = copy.deepcopy(manifest)
        reordered_manifest["papers"].reverse()
        reordered_records = copy.deepcopy(records)
        refresh_freeze_evidence(
            reordered_records, config, reordered_manifest, run_order
        )
        reordered_check = check_result_set(
            reordered_records,
            run_order=run_order,
            config=config,
            manifest=reordered_manifest,
        )
        self.assertFalse(reordered_check["ok"])
        self.assertTrue(
            any(
                "expected 'highambench-p02-p01-" in error
                for error in reordered_check["errors"]
            ),
            reordered_check,
        )

    def test_package_runtime_support_count_is_required_and_reconciles(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        records[0]["frozen_run_verification"]["freeze_check"][
            "packages_runtime"
        ].pop("compiled_support_file_count")
        refresh_freeze_evidence(records, config, manifest, run_order)
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("packages-runtime evidence" in error for error in check["errors"]),
            check,
        )

        config, manifest, run_order, records = self.reference_fixture()
        records[0]["frozen_run_verification"]["freeze_check"][
            "packages_runtime"
        ]["compiled_support_file_count"] = 2
        refresh_freeze_evidence(records, config, manifest, run_order)
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("packages-runtime evidence" in error for error in check["errors"]),
            check,
        )

    def test_incomplete_and_mismatched_matrices_are_rejected(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        cases: list[tuple[str, list[dict], dict]] = []

        missing = copy.deepcopy(records[:-1])
        cases.append(("missing", missing, run_order))

        wrong_hash = copy.deepcopy(records)
        wrong_hash[0]["paper_sha256"] = "0" * 64
        cases.append(("paper hash", wrong_hash, run_order))

        wrong_limit = copy.deepcopy(records)
        wrong_limit[0]["limits"]["time_seconds"] = 99
        cases.append(("limit", wrong_limit, run_order))

        wrong_agent = copy.deepcopy(records)
        wrong_agent[0]["agent"]["model"] = "different-model"
        cases.append(("agent metadata", wrong_agent, run_order))

        wrong_order = copy.deepcopy(records)
        pair = run_order["pairs"][0]
        first = next(run for run in wrong_order if run["run_id"] == pair["run_ids"][0])
        second = next(run for run in wrong_order if run["run_id"] == pair["run_ids"][1])
        second["started_at_utc"] = first["started_at_utc"]
        cases.append(("chronological order", wrong_order, run_order))

        corrupt_plan = copy.deepcopy(run_order)
        corrupt_plan["pairs"][0]["sha256"] = "f" * 64
        cases.append(("run-order digest", copy.deepcopy(records), corrupt_plan))

        for label, candidate_records, candidate_order in cases:
            with self.subTest(label=label):
                check = check_result_set(
                    candidate_records,
                    run_order=candidate_order,
                    config=config,
                    manifest=manifest,
                )
                self.assertFalse(check["ok"])
                self.assertFalse(check["reference_compliant"])
                with self.assertRaises(BenchmarkToolError):
                    require_complete_result_set(check)

    def test_one_system_error_followed_by_one_rerun_is_resolved(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        final = records[0]
        incident = copy.deepcopy(final)
        incident["planned_run_id"] = final["run_id"]
        incident["run_id"] = final["run_id"] + "-system-attempt-1"
        incident["pass"] = False
        incident["scored"] = False
        incident["failure_code"] = "SYSTEM_ERROR"
        incident["failure_note"] = "temporary executor fault before useful work"
        incident["actual_stop_seconds"] = 1
        incident["scored_elapsed_seconds"] = 1
        incident["token_usage"] = None
        incident["useful_work_started"] = False
        final_start = dt.datetime.fromisoformat(final["started_at_utc"])
        incident["started_at_utc"] = (final_start - dt.timedelta(seconds=10)).isoformat()
        incident["finished_at_utc"] = (final_start - dt.timedelta(seconds=5)).isoformat()
        check = check_result_set(
            [incident, *records],
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertTrue(check["system_error_handling_complete"])
        self.assertEqual(check["system_error_incident_count"], 1)
        self.assertEqual(check["input_record_count"], 7)

        unresolved = check_result_set(
            [incident, *records[1:]],
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(unresolved["ok"])
        self.assertFalse(unresolved["system_error_handling_complete"])
        self.assertTrue(unresolved["system_error_issues"])

    def test_system_error_after_useful_work_is_a_charged_final_failure(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        failed = records[0]
        failed["pass"] = False
        failed["failure_code"] = "SYSTEM_ERROR"
        failed["failure_note"] = "executor failed after the agent turn started"
        failed["useful_work_started"] = True
        failed["scored_elapsed_seconds"] = config["limits"]["failure_scored_time_seconds"]
        authenticate_matrix_record(failed)
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertEqual(check["system_error_incident_count"], 0)
        self.assertIn(failed["run_id"], check["selected_final_run_ids"])

    @mock.patch.object(
        result_set_module.token_canary, "validate_attestation_document"
    )
    @mock.patch.object(result_set_module, "_authenticated_ultra_canary_summary")
    @mock.patch.object(
        result_set_module.run_matrix,
        "production_freeze_bindings",
        return_value=(
            PRODUCTION_PROMPT_PROTOCOL,
            PRODUCTION_EXECUTION_COMPONENTS,
        ),
    )
    def test_file_hashes_are_re_read_when_repository_root_is_given(
        self,
        production_bindings: mock.Mock,
        ultra_auth: mock.Mock,
        token_auth: mock.Mock,
    ) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            frozen = config["frozen_environment"]
            canary_record = {
                "pass": False,
                "failure_code": "TOKEN_LIMIT",
                "token_usage": {
                    "model_tokens": 137,
                    "measurement_source": "codex_app_server_rawResponse/completed",
                    "notification": "rawResponse/completed",
                    "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                    "notification_sequence": 3,
                    "call_count": 3,
                    "thread_count": 2,
                    "drain_complete": True,
                    "measurement_exact": True,
                },
                "token_measurement": {
                    "limit_enforcement": {
                        "triggered": True,
                        "observed_tokens": 123,
                        "overshoot_tokens": 23,
                        "final_endpoint_tokens": 137,
                        "final_overshoot_tokens": 37,
                    }
                },
                "network_violation": {"detected": False, "integrity_ok": True},
            }
            canary_artifact_payloads = {
                "attempts/canary.json": json.dumps(
                    canary_record, sort_keys=True
                ).encode(),
                "logs/canary.log": b"canary log\n",
                "logs/usage.json": b'{"model_tokens":123}\n',
                "attempts/canary.jsonl": b'{"notification_sequence":1}\n',
                "logs/freeze_check.json": json.dumps(
                    {
                        "prompt_protocol": PRODUCTION_PROMPT_PROTOCOL,
                        "execution_components": PRODUCTION_EXECUTION_COMPONENTS,
                    },
                    sort_keys=True,
                ).encode(),
            }
            canary_artifacts = {
                label: {
                    "path": relative,
                    "sha256": hashlib.sha256(
                        canary_artifact_payloads[relative]
                    ).hexdigest(),
                }
                for label, relative in {
                    "record": "attempts/canary.json",
                    "agent_log": "logs/canary.log",
                    "usage": "logs/usage.json",
                    "raw_jsonl": "attempts/canary.jsonl",
                    "freeze_check": "logs/freeze_check.json",
                }.items()
            }
            canary_evidence = {
                "schema_version": 1,
                "kind": "highambench-live-token-control-canary",
                "status": "passed",
                "public_release": False,
                "benchmark_id": config["benchmark_id"],
                "freeze_check_sha256": SHA_A,
                "agent": {
                    "id": frozen["agent_id"],
                    "version": frozen["agent_version"],
                    "binary_sha256": frozen["agent_binary_sha256"],
                    "model": frozen["model_version"],
                    "reasoning_effort": frozen["model_reasoning_effort"],
                    "ultra_orchestration": copy.deepcopy(
                        frozen["ultra_orchestration"]
                    ),
                },
                "controls": {
                    "frozen_benchmark_token_limit": 1000,
                    "outer_canary_token_limit": 100,
                    "nested_advisory_rollout_budget_limit": 1000,
                    "notification": "rawResponse/completed",
                    "cached_input_counted_once": True,
                    "trusted_adapter_freezes_first_threshold": False,
                    "trusted_adapter_latches_first_threshold": True,
                    "all_descendant_threads_included": True,
                    "response_ids_deduplicated": True,
                    "drain_complete_required": True,
                    "measurement_exact_required": True,
                    "root_completion_is_tree_barrier": False,
                    "trusted_usage_path_outside_workspace": True,
                },
                "outcome": {
                    "input_tokens_including_cached": 134,
                    "output_tokens": 3,
                    "total_model_tokens": 137,
                    "first_crossing_tokens": 123,
                    "overshoot_tokens": 23,
                    "final_overshoot_tokens": 37,
                    "thread_count": 2,
                    "response_count": 3,
                    "notification_sequence": 3,
                    "notification_count_in_audit_log": 3,
                    "drain_complete": True,
                    "measurement_exact": True,
                },
                "artifact_root": "canary_artifacts",
                "artifacts": canary_artifacts,
            }
            canary_payload = json.dumps(canary_evidence, sort_keys=True).encode()
            files = {
                "spec.pdf": b"specification",
                "paper.pdf": b"paper",
                "shared/Definitions.lean": b"shared",
                "targets/T1.lean": b"T1",
                "targets/T2.lean": b"T2",
                "targets/T3.lean": b"T3",
                "metadata/library_source.json": b'{"files":[{}]}',
                "metadata/library_olean.json": b'{"files":[{}]}',
                "metadata/packages_olean.json": (
                    b'{"toolchain":{"file_count":1},"packages":[{"file_count":1}]}'
                ),
                "metadata/packages_runtime.json": (
                    b'{"files":['
                    b'{"path":"mathlib/Mathlib.lean"},'
                    b'{"path":"mathlib/.lake/build/lib/lean/Mathlib.olean"},'
                    b'{"path":"mathlib/.lake/build/lib/lean/Mathlib.ir"}'
                    b']}'
                ),
                "metadata/release_files.json": b'{"files":[{}]}',
                TOKEN_CANARY_PATH: canary_payload,
                ULTRA_CANARY_PATH: b"{}",
                "paper_bencmark/highambench/metadata/controlled/task-T1.json": b"controlled T1",
                "paper_bencmark/highambench/metadata/controlled/task-T2.json": b"controlled T2",
                "paper_bencmark/highambench/metadata/controlled/task-T3.json": b"controlled T3",
                **{
                    f"canary_artifacts/{relative}": payload
                    for relative, payload in canary_artifact_payloads.items()
                },
            }
            for relative, payload in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(payload)

            def digest(relative: str) -> str:
                return hashlib.sha256(files[relative]).hexdigest()

            manifest["specification"]["sha256"] = digest("spec.pdf")
            frozen["token_control_canary"] = token_canary_descriptor(
                digest(TOKEN_CANARY_PATH)
            )
            frozen["ultra_orchestration_canary"] = ultra_canary_descriptor(
                digest(ULTRA_CANARY_PATH)
            )
            ultra_auth.return_value = ultra_canary_summary(
                frozen["ultra_orchestration_canary"]
            )
            canary_summary = token_canary_summary(
                frozen["token_control_canary"]
            )
            token_auth.return_value = {
                key: copy.deepcopy(value)
                for key, value in canary_summary.items()
                if key not in {"path", "sha256"}
            }
            records[0]["frozen_run_verification"]["freeze_check"][
                "token_control_canary"
            ] = canary_summary
            frozen["numstability_source_manifest_sha256"] = digest(
                "metadata/library_source.json"
            )
            frozen["numstability_compiled_manifest_sha256"] = digest(
                "metadata/library_olean.json"
            )
            frozen["compiled_environment_summary_sha256"] = digest(
                "metadata/packages_olean.json"
            )
            frozen["packages_runtime_manifest_sha256"] = digest(
                "metadata/packages_runtime.json"
            )
            frozen["release_manifest_sha256"] = digest(
                "metadata/release_files.json"
            )
            manifest["papers"][0]["source"]["sha256"] = digest("paper.pdf")
            manifest["controlled_shared_files"][0]["sha256"] = digest(
                "shared/Definitions.lean"
            )
            for target in manifest["papers"][0]["targets"]:
                target["lean_target"]["controlled_file_sha256"] = digest(
                    target["lean_target"]["file"]
                )
            for record in records:
                record["paper_sha256"] = digest("paper.pdf")
                if record["condition"] == "N":
                    controlled_path = (
                        f"paper_bencmark/highambench/metadata/controlled/"
                        f"{record['task_id']}.json"
                    )
                    record["n_preflight"]["controlled_task_staging"][
                        "manifest_sha256"
                    ] = digest(controlled_path)
            environment = {
                "environment_id": "placeholder",
                "environment_bundle_sha256": "0" * 64,
                "environment_bundle_definition": ENVIRONMENT_BUNDLE_DEFINITION,
                "release_manifest_sha256": frozen["release_manifest_sha256"],
                "token_control": copy.deepcopy(config["token_control"]),
                "token_control_canary": copy.deepcopy(
                    frozen["token_control_canary"]
                ),
                "ultra_orchestration_canary": copy.deepcopy(
                    frozen["ultra_orchestration_canary"]
                ),
                "runtime": {
                    "python": {
                        "version": frozen["python_version"],
                        "binary_sha256": frozen["python_binary_sha256"],
                    },
                    "packages_runtime_manifest": frozen[
                        "packages_runtime_manifest"
                    ],
                    "packages_runtime_manifest_sha256": frozen[
                        "packages_runtime_manifest_sha256"
                    ],
                },
                "host_class": {
                    "kernel": "test-os",
                    "virtualization": "TEST",
                    "cpu_vendor": "test-vendor",
                    "processor": "test-cpu",
                    "cpu_family": 1,
                    "cpu_model": 2,
                    "cpu_stepping": 3,
                    "online_logical_cpus": 1,
                    "allocated_physical_cores": 1,
                    "allocated_sockets": 1,
                    "allocated_threads_per_core": [1],
                    "visible_memory_bytes": 1,
                    "allocation_memory_limit_bytes": 1,
                    "slurm_num_nodes": 1,
                    "slurm_num_cpus": 1,
                    "slurm_num_tasks": 1,
                    "slurm_cpus_per_task": 1,
                    "slurm_allocated_memory_bytes": 1,
                },
            }
            records[0]["frozen_run_verification"]["freeze_check"][
                "prompt_protocol"
            ] = copy.deepcopy(PRODUCTION_PROMPT_PROTOCOL)
            records[0]["frozen_run_verification"]["freeze_check"][
                "execution_components"
            ] = copy.deepcopy(PRODUCTION_EXECUTION_COMPONENTS)
            bundle = _environment_bundle_digest(config, environment)
            environment_id = "highambench-p01-" + bundle[:16]
            frozen["environment_bundle_sha256"] = bundle
            frozen["environment_id"] = environment_id
            environment["environment_bundle_sha256"] = bundle
            environment["environment_id"] = environment_id
            environment_path = (
                root / "paper_bencmark/highambench/metadata/environment.json"
            )
            environment_path.parent.mkdir(parents=True, exist_ok=True)
            environment_path.write_text(json.dumps(environment), encoding="utf-8")
            refresh_freeze_evidence(
                records, config, manifest, run_order, environment=environment
            )
            check = check_result_set(
                records,
                run_order=run_order,
                config=config,
                manifest=manifest,
                repository_root=root,
            )
            self.assertTrue(check["ok"], check["errors"])
            self.assertTrue(check["production_canary_bindings_authenticated"])
            self.assertTrue(all(item["match"] for item in check["verified_hashes"]))
            production_bindings.assert_called_with(config, environment)
            ultra_call = ultra_auth.call_args
            self.assertEqual(
                ultra_call.kwargs["prompt_protocol"], PRODUCTION_PROMPT_PROTOCOL
            )
            self.assertEqual(
                ultra_call.kwargs["execution_components"],
                PRODUCTION_EXECUTION_COMPONENTS,
            )

            canary_path = root / TOKEN_CANARY_PATH
            canary_path.write_bytes(canary_payload + b"\n")
            changed_canary = check_result_set(
                records,
                run_order=run_order,
                config=config,
                manifest=manifest,
                repository_root=root,
            )
            self.assertFalse(changed_canary["ok"])
            self.assertTrue(
                any("canary evidence" in error for error in changed_canary["errors"]),
                changed_canary,
            )
            canary_path.write_bytes(canary_payload)

            stale_canary_summary = copy.deepcopy(records)
            for record in stale_canary_summary:
                wrapper = record["frozen_run_verification"]
                wrapper["freeze_check"]["token_control_canary"]["artifacts"][
                    "record"
                ]["bytes"] += 1
                wrapper["freeze_check_sha256"] = hashlib.sha256(
                    json.dumps(
                        wrapper["freeze_check"],
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode()
                ).hexdigest()
            stale = check_result_set(
                stale_canary_summary,
                run_order=run_order,
                config=config,
                manifest=manifest,
                repository_root=root,
            )
            self.assertFalse(stale["ok"])
            self.assertTrue(
                any("stale token-control canary summary" in error for error in stale["errors"]),
                stale,
            )

            (root / "targets/T2.lean").write_text("changed", encoding="utf-8")
            changed = check_result_set(
                records,
                run_order=run_order,
                config=config,
                manifest=manifest,
                repository_root=root,
            )
            self.assertFalse(changed["ok"])
            self.assertTrue(
                any("target task-T2" in error for error in changed["errors"])
            )

    def test_token_canary_production_freeze_binds_exact_prompt_and_all_components(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            artifact_root = root / "artifacts"
            artifact_root.mkdir()
            freeze_path = artifact_root / "freeze_check.json"

            def evidence_for(value: dict) -> dict:
                freeze_path.write_text(
                    json.dumps(value, sort_keys=True), encoding="utf-8"
                )
                return {
                    "artifact_root": "artifacts",
                    "artifacts": {
                        "freeze_check": {
                            "path": "freeze_check.json",
                            "sha256": hashlib.sha256(
                                freeze_path.read_bytes()
                            ).hexdigest(),
                        }
                    },
                }

            current = {
                "prompt_protocol": copy.deepcopy(PRODUCTION_PROMPT_PROTOCOL),
                "execution_components": copy.deepcopy(
                    PRODUCTION_EXECUTION_COMPONENTS
                ),
            }
            errors: list[str] = []
            self.assertTrue(
                result_set_module._authenticate_token_canary_production_freeze(
                    root,
                    evidence_for(current),
                    prompt_protocol=PRODUCTION_PROMPT_PROTOCOL,
                    execution_components=PRODUCTION_EXECUTION_COMPONENTS,
                    errors=errors,
                ),
                errors,
            )

            stale_prompt = copy.deepcopy(current)
            stale_prompt["prompt_protocol"] = {"version": "stale"}
            errors = []
            self.assertFalse(
                result_set_module._authenticate_token_canary_production_freeze(
                    root,
                    evidence_for(stale_prompt),
                    prompt_protocol=PRODUCTION_PROMPT_PROTOCOL,
                    execution_components=PRODUCTION_EXECUTION_COMPONENTS,
                    errors=errors,
                )
            )
            self.assertIn("production prompt protocol is stale", " ".join(errors))

            for field in PRODUCTION_EXECUTION_COMPONENTS:
                with self.subTest(field=field):
                    stale_component = copy.deepcopy(current)
                    stale_component["execution_components"][field] = "f" * 64
                    errors = []
                    self.assertFalse(
                        result_set_module._authenticate_token_canary_production_freeze(
                            root,
                            evidence_for(stale_component),
                            prompt_protocol=PRODUCTION_PROMPT_PROTOCOL,
                            execution_components=PRODUCTION_EXECUTION_COMPONENTS,
                            errors=errors,
                        )
                    )
                    self.assertIn(
                        "production execution components are stale",
                        " ".join(errors),
                    )

            authenticated = evidence_for(current)
            freeze_path.write_text("{}", encoding="utf-8")
            errors = []
            self.assertFalse(
                result_set_module._authenticate_token_canary_production_freeze(
                    root,
                    authenticated,
                    prompt_protocol=PRODUCTION_PROMPT_PROTOCOL,
                    execution_components=PRODUCTION_EXECUTION_COMPONENTS,
                    errors=errors,
                )
            )
            self.assertIn("wrong SHA-256", " ".join(errors))

    def test_observational_bubblewrap_pilot_is_complete_but_not_a_score(self) -> None:
        config, manifest, run_order = benchmark_documents(
            backend_seed=None, bubblewrap=True
        )
        records = result_records(
            config, manifest, run_order, observational=True
        )
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
            allow_observational_unscored=True,
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertFalse(check["reference_compliant"])
        self.assertFalse(check["official_scores_valid"])
        self.assertEqual(check["analysis_profile"], "observational_pilot")
        self.assertEqual(check["official_final_record_count"], 0)
        reasons = " ".join(check["nonreference_reasons"])
        self.assertIn("backend seeds", reasons)
        self.assertIn("bubblewrap", reasons)
        self.assertIn("provider connection", reasons)

        official_attempt = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(official_attempt["ok"])

        with self.assertRaisesRegex(
            BenchmarkToolError, "both frozen live canaries were not authenticated"
        ):
            analyze(
                records,
                include_unscored=False,
                bootstrap_resamples=25,
                bootstrap_seed=4,
                run_order=run_order,
                config=config,
                manifest=manifest,
                require_complete=True,
                observational_pilot=True,
            )
        analysis = analyze(
            records,
            include_unscored=False,
            bootstrap_resamples=25,
            bootstrap_seed=4,
            run_order=run_order,
            config=config,
            manifest=manifest,
            require_complete=False,
            observational_pilot=True,
        )
        self.assertFalse(analysis["official_scores_valid"])
        self.assertEqual(analysis["analyzed_run_count"], 0)
        self.assertEqual(analysis["condition_summaries"], [])
        self.assertEqual(analysis["paired_comparisons"], [])
        self.assertEqual(len(analysis["per_run_results"]), 6)
        pilot = analysis["observational_pilot_results"]
        self.assertIsNotNone(pilot)
        assert pilot is not None
        self.assertTrue(pilot["condition_summaries"])
        self.assertEqual(len(pilot["per_task_summaries"]), 6)
        self.assertEqual(len(pilot["per_task_paired_comparisons"]), 3)
        overall = next(
            row for row in pilot["paired_comparisons"] if row["scope"] == "overall"
        )
        self.assertEqual(overall["median_observed_paired_time_change"], -5)
        self.assertEqual(overall["median_observed_paired_token_change"], -20)
        self.assertFalse(overall["bootstrap"]["informative"])
        self.assertIn("degenerate", overall["bootstrap"]["note"])

        with tempfile.TemporaryDirectory() as raw:
            output = Path(raw)
            write_csv_tables(output, analysis)
            self.assertTrue((output / "observational_condition_summary.csv").is_file())
            self.assertTrue((output / "observational_task_summary.csv").is_file())
            self.assertTrue((output / "observational_paired_summary.csv").is_file())
            self.assertTrue(
                (output / "observational_task_paired_summary.csv").is_file()
            )
        latex = render_latex(analysis)
        self.assertIn("not official scores", latex)
        self.assertIn("degenerate", latex)
        self.assertIn("Observed per-task paired changes", latex)

    def test_observational_mode_does_not_relax_network_isolation(self) -> None:
        config, manifest, run_order = benchmark_documents(
            backend_seed=None, bubblewrap=True
        )
        records = result_records(config, manifest, run_order, observational=True)
        records[0]["protocol"]["claims"]["network_disabled"] = False
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
            allow_observational_unscored=True,
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("non-relaxable controls" in error for error in check["errors"])
        )

    def test_final_network_evidence_is_mandatory_and_coherent(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        missing = copy.deepcopy(records)
        missing[0].pop("network_violation")
        check = check_result_set(
            missing, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("structured network" in error for error in check["errors"]))

        incoherent = copy.deepcopy(records)
        incoherent[0]["network_violation"]["detected"] = True
        incoherent[0]["network_violation"]["event_count"] = 1
        check = check_result_set(
            incoherent, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("unsafe network" in error for error in check["errors"]))


if __name__ == "__main__":
    unittest.main()
