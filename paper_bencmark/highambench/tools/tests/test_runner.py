from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import stat
import sys
import tempfile
import time
from typing import Mapping
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, write_json  # noqa: E402
from hashes import create_manifest  # noqa: E402
import codex_isolated  # noqa: E402
import runner as runner_module  # noqa: E402
from runner import (  # noqa: E402
    FAILURE_PRECEDENCE,
    NETWORK_VIOLATION_MARKER_ENV,
    PROVIDER_GATE_CLEANUP_GRACE_SECONDS,
    TOKEN_USAGE_MEASUREMENT_SOURCE,
    ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION,
    ULTRA_USAGE_MEASUREMENT_SOURCE,
    ULTRA_USAGE_NOTIFICATION,
    ULTRA_USAGE_SCOPE,
    _authenticate_validation_result,
    _bind_final_submission_boundary,
    _read_submission_request,
    _validate_ultra_submission_yield_envelope,
    _validate_submission_event_order,
    _validate_submission_wire,
    _validator_contract,
    authenticate_provider_gate_artifact,
    apply_ultra_boundary_deviation,
    classify_final_outcome,
    exact_ultra_token_drain_error,
    protocol_status,
    read_token_usage,
    run_one,
    trusted_usage_output,
    validate_provider_gate_outcome,
)
from validator import validate as validate_submission  # noqa: E402


SIGNATURE = "theorem target (n : Nat) : n = n := by\n  rfl\n"
_SYNTHETIC_PROVIDER_TRANSPORT: dict[str, object] | None = None


def synthetic_provider_transport() -> dict[str, object]:
    global _SYNTHETIC_PROVIDER_TRANSPORT
    if _SYNTHETIC_PROVIDER_TRANSPORT is None:
        _SYNTHETIC_PROVIDER_TRANSPORT = (
            runner_module.authenticate_provider_transport_provenance(
                ["/usr/bin/python3.10"]
            )
        )
    return copy.deepcopy(_SYNTHETIC_PROVIDER_TRANSPORT)


def _seal_synthetic_gate(path: Path, record: dict[str, object]) -> None:
    unsigned = {key: value for key, value in record.items() if key != "record_sha256"}
    record["record_sha256"] = hashlib.sha256(
        (
            json.dumps(
                unsigned,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n"
        ).encode("utf-8")
    ).hexdigest()
    path.chmod(0o600) if path.exists() else None
    path.write_text(
        json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        + "\n",
        encoding="utf-8",
    )
    path.chmod(0o444)


def synthetic_provider_gate(
    path: Path,
    *,
    close_reason: str = "token_limit",
    token_limit: int = 10_000,
    request_kind: str = "turn",
    content_type_present: bool = True,
    content_encoding_present: bool = True,
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    """Create one deterministic sealed single-response gate/usage fixture."""

    response_bound = 272_000
    source_sha = "1" * 64
    catalog_sha = "2" * 64
    entry_sha = "3" * 64
    transport = synthetic_provider_transport()
    crossed = close_reason == "token_limit"
    input_tokens = 9_000 if crossed else 400
    output_tokens = 1_500 if crossed else 100
    total_tokens = input_tokens + output_tokens
    normalized = {
        "input_tokens": input_tokens,
        "cached_input_tokens": 1_000 if crossed else 40,
        "cache_write_input_tokens": 200 if crossed else 10,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": 300 if crossed else 20,
        "total_tokens": total_tokens,
    }
    raw_usage = {
        "input_tokens": input_tokens,
        "input_tokens_details": {
            "cached_tokens": normalized["cached_input_tokens"],
            "cache_write_tokens": normalized["cache_write_input_tokens"],
        },
        "output_tokens": output_tokens,
        "output_tokens_details": {
            "reasoning_tokens": normalized["reasoning_output_tokens"]
        },
        "total_tokens": total_tokens,
    }
    response_id = "resp-fixture-1"
    call_id = "provider-call-00000003"
    upstream_events: list[dict[str, object]] = []
    if request_kind == "compaction":
        upstream_events.append(
            {
                "type": "response.output_item.done",
                "item": {
                    "type": "compaction",
                    "encrypted_content": "opaque-compaction-fixture",
                },
            }
        )
    upstream_events.append(
        {
            "type": "response.completed",
            "response": {"id": response_id, "usage": raw_usage},
        }
    )
    upstream = "".join(
        "event: "
        + event["type"]
        + "\ndata: "
        + json.dumps(
            event,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        + "\n\n"
        for event in upstream_events
    ).encode("utf-8")
    output_items = [
        copy.deepcopy(event["item"])
        for event in upstream_events
        if event.get("type") == "response.output_item.done"
    ]
    manifest_items: list[dict[str, object]] = []
    for item_index, output_item in enumerate(output_items):
        payload = json.dumps(
            output_item,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
        arguments = output_item.get("arguments")
        arguments_payload = (
            arguments.encode("utf-8") if isinstance(arguments, str) else None
        )
        manifest_items.append(
            {
                "index": item_index,
                "id": output_item.get("id"),
                "type": output_item["type"],
                "name": output_item.get("name"),
                "namespace": output_item.get("namespace"),
                "call_id": output_item.get("call_id"),
                "payload_sha256": hashlib.sha256(payload).hexdigest(),
                "payload_bytes": len(payload),
                "arguments_sha256": (
                    hashlib.sha256(arguments_payload).hexdigest()
                    if arguments_payload is not None
                    else None
                ),
                "arguments_bytes": (
                    len(arguments_payload)
                    if arguments_payload is not None
                    else None
                ),
                "wait_timeout_ms": None,
            }
        )
    response_output_manifest = {
        "schema_version": 1,
        "response_id": response_id,
        "output_item_count": len(manifest_items),
        "action_capable_item_count": sum(
            item["type"] == "function_call" or str(item["type"]).endswith("_call")
            for item in manifest_items
        ),
        "items": manifest_items,
    }
    upstream_sse_authentication = {
        "schema_version": 1,
        "protocol": "highambench-responses-sse-envelope-v1",
        "parser": "highambench-strict-responses-sse-v2",
        "complete": True,
        "content_type_basis": (
            "declared_text_event_stream"
            if content_type_present
            else "authenticated_stream_request_header_absent"
        ),
        "content_encoding_basis": (
            "declared_identity"
            if content_encoding_present
            else "implicit_identity_header_absent"
        ),
        "json_event_count": len(upstream_events),
        "completed_event_index": len(upstream_events) - 1,
        "done_count": 0,
        "body_sha256": hashlib.sha256(upstream).hexdigest(),
        "body_bytes": len(upstream),
        "response_id": response_id,
        "downstream_content_type_synthesized": not content_type_present,
    }
    if crossed:
        sanitized_event = {
            "type": "response.completed",
            "response": {
                "id": response_id,
                "usage": raw_usage,
                "end_turn": True,
                "output": [],
            },
        }
        sanitized_events = (
            [
                {
                    "type": "response.output_item.done",
                    "item": {
                        "type": "compaction",
                        "encrypted_content": "opaque-compaction-fixture",
                    },
                },
                sanitized_event,
            ]
            if request_kind == "compaction"
            else [sanitized_event]
        )
        released = "".join(
            "event: "
            + event["type"]
            + "\ndata: "
            + json.dumps(
                event,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n\n"
            for event in sanitized_events
        ).encode("utf-8")
        release_kind = (
            "sanitized_compaction_crossing_completion"
            if request_kind == "compaction"
            else "sanitized_crossing_completion"
        )
    else:
        sanitized_event = None
        sanitized_events = None
        released = upstream
        release_kind = "byte_identity"
    call: dict[str, object] = {
        "sequence": 3,
        "call_id": call_id,
        "method": "POST",
        "route": "/responses",
        "request_body_sha256": hashlib.sha256(b"request").hexdigest(),
        "request_bytes": 7,
        "request_model": "gpt-5.6-sol",
        "request_stream": True,
        "request_metadata": {
            "installation_id": "install",
            "session_id": "session",
            "thread_id": "root-thread",
            "turn_id": "root-turn",
            "request_kind": request_kind,
            "window_id": "window",
        },
        "credential_headers_present": ["authorization"],
        "admission_mode": "EXCLUSIVE",
        "response_bound": response_bound,
        "completed_before": 0,
        "open_before": 0,
        "reserved_before": 0,
        "reservation_after": response_bound,
        "admitted_unix_ns": 10_300,
        "admitted_monotonic_ns": 1_300,
        "upstream_started": True,
        "upstream_start_unix_ns": 10_400,
        "upstream_start_monotonic_ns": 1_400,
        "upstream_status": 200,
        "upstream_content_type": (
            "text/event-stream; charset=utf-8" if content_type_present else None
        ),
        "upstream_content_type_occurrences": 1 if content_type_present else 0,
        "upstream_content_encoding": (
            "identity" if content_encoding_present else None
        ),
        "upstream_content_encoding_occurrences": (
            1 if content_encoding_present else 0
        ),
        "upstream_sse_authentication": upstream_sse_authentication,
        "upstream_body_sha256": hashlib.sha256(upstream).hexdigest(),
        "upstream_body_bytes": len(upstream),
        "response_id": response_id,
        "usage": raw_usage,
        "normalized_usage": normalized,
        "previous_total": 0,
        "committed_total": total_tokens,
        "commit_unix_ns": 10_500,
        "commit_monotonic_ns": 1_500,
        "crossed_cap": crossed,
        "release_kind": release_kind,
        "released_body_sha256": hashlib.sha256(released).hexdigest(),
        "released_body_bytes": len(released),
        "released_sanitized_event": sanitized_event,
        "released_sanitized_events": sanitized_events,
        "released_sanitized_body_utf8": (
            released.decode("utf-8") if crossed else None
        ),
        "client_release_complete": True,
        "response_output_manifest": response_output_manifest,
        "appserver_crossbind": {
            "thread_id": "root-thread",
            "turn_id": "root-turn",
            "event_sequence": 1,
            "normalized_usage": normalized,
            "bind_unix_ns": 10_550,
            "bind_monotonic_ns": 1_550,
        },
        "appserver_delivery": {
            "kind": "direct_raw_response",
            "successor_call_id": None,
            "successor_response_id": None,
            "bind_unix_ns": 10_550,
            "bind_monotonic_ns": 1_550,
        },
        "error": None,
    }
    transitions: list[dict[str, object]] = [
        {
            "sequence": 1,
            "from_phase": "CONCURRENT",
            "to_phase": "DRAINING",
            "reason": "concurrent_reservation_would_reach_limit",
            "call_id": None,
            "unix_ns": 10_100,
            "monotonic_ns": 1_100,
        },
        {
            "sequence": 2,
            "from_phase": "DRAINING",
            "to_phase": "EXCLUSIVE",
            "reason": "concurrent_requests_drained",
            "call_id": None,
            "unix_ns": 10_200,
            "monotonic_ns": 1_200,
        },
    ]
    crossing: dict[str, object] | None = None
    if crossed:
        crossing = {
            "call_id": call_id,
            "response_id": response_id,
            "sequence": 4,
            "previous_total": 0,
            "response_tokens": total_tokens,
            "completed_tokens": total_tokens,
            "overshoot_tokens": total_tokens - token_limit,
            "commit_unix_ns": 10_500,
            "commit_monotonic_ns": 1_500,
            "sole_inflight": True,
            "release_kind": release_kind,
            "request_kind": request_kind,
        }
        terminal_sequence = 5
        terminal_reason = "first_token_limit_crossing"
    else:
        terminal_sequence = 4
        terminal_reason = f"terminal_close:{close_reason}"
    transitions.append(
        {
            "sequence": terminal_sequence,
            "from_phase": "EXCLUSIVE",
            "to_phase": "CLOSED",
            "reason": terminal_reason,
            "call_id": call_id if crossed else None,
            "unix_ns": 10_600,
            "monotonic_ns": 1_600,
        }
    )
    state = {
        "phase": "CLOSED",
        "close_reason": close_reason,
        "completed_tokens": total_tokens,
        "crossing": crossing,
        "crossing_closed": crossed,
        "open_request_ids": [],
        "all_complete": True,
        "no_post_close_upstream": True,
        "poisoned": False,
        "poison_reasons": [],
        "active_handler_count": 0,
        "handlers_quiescent": True,
        "sequence": terminal_sequence,
    }
    record: dict[str, object] = {
        "schema_version": 6,
        "protocol": "highambench-provider-token-gate-v6",
        "implementation": {
            "name": "provider_token_gate.py",
            "version": "6",
            "source_sha256": source_sha,
        },
        "configuration": {
            "token_limit": token_limit,
            "response_bound": response_bound,
            "response_bound_enforcement": "runtime_fail_closed_before_buffered_response_release",
            "model_catalog_sha256": catalog_sha,
            "model_entry_sha256": entry_sha,
            "strict_admission_inequality": "completed_tokens + (open_request_count + 1) * response_bound < token_limit",
            "upstream_origin": "https://chatgpt.com",
            "upstream_base_path": "/backend-api/codex",
            "loopback_only": True,
            "capability_persisted": False,
            "websockets_supported": False,
            "request_retries": 0,
            "stream_retries": 0,
            "request_compression": False,
            "response_compression": "identity",
            "counted_route": "POST /responses",
            "counted_request_kinds": ["turn", "compaction"],
            "rejected_inference_routes": ["POST /responses/compact"],
            "allowed_setup_route_prefixes": [],
            "crossing_release_policy": "ordinary_empty_output_or_compaction_single_item_before_minimal_completion",
            "upstream_response_contract": copy.deepcopy(
                runner_module.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT
            ),
            "transport_provenance": transport,
        },
        "bindings": {
            "root_thread_id": "root-thread",
            "prompt_release_sha256": "4" * 64,
            "prompt_release_protocol": "highambench-prompt-release-v1",
            "prompt_sha256": "5" * 64,
            "run_id": "fixture-run",
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
        },
        "lifecycle": {
            "started_unix_ns": 10_000,
            "started_monotonic_ns": 1_000,
            "stopped_unix_ns": 10_700,
            "stopped_monotonic_ns": 1_700,
            "finalized_unix_ns": 10_800,
            "finalized_monotonic_ns": 1_800,
        },
        "state": state,
        "calls": [call],
        "transitions": transitions,
        "denials": [],
        "setup_requests": [],
        "invariants": {
            key: True for key in runner_module.PROVIDER_GATE_INVARIANT_KEYS
        },
        "canonical_encoding": "compact_sorted_key_utf8_json_newline",
        "sealed_mode": "0444",
    }
    _seal_synthetic_gate(path, record)
    usage_crossing = (
        {
            "response_id": response_id,
            "notification_sequence": 1,
            "observed_at_unix_ns": 10_570,
            "tokens": total_tokens,
            "active_thread_ids": ["root-thread"],
        }
        if crossed
        else None
    )
    usage: dict[str, object] = {
        **normalized,
        "model_tokens": total_tokens,
        "response_count": 1,
        "notification_sequence": 1,
        "response_ids": [response_id],
        "provider_response_count": 1,
        "provider_response_ids": [response_id],
        "provider_usage": copy.deepcopy(normalized),
        "appserver_response_count": 1,
        "appserver_response_ids": [response_id],
        "appserver_usage": copy.deepcopy(normalized),
        "suppressed_collaboration_wait_response_count": 0,
        "suppressed_collaboration_wait_response_ids": [],
        "suppressed_collaboration_wait_usage": {
            field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
        },
        "suppressed_collaboration_wait_evidence": [],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_usage": {
            field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
        },
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_usage": {
            field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
        },
        "discarded_after_explicit_child_interrupt_evidence": [],
        "provider_usage_reconciliation": {
            "schema_version": 3,
            "provider_response_count": 1,
            "appserver_response_count": 1,
            "suppressed_collaboration_wait_response_count": 0,
            "provider_usage": copy.deepcopy(normalized),
            "appserver_usage": copy.deepcopy(normalized),
            "suppressed_collaboration_wait_usage": {
                field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
            },
            "provider_response_ids": [response_id],
            "appserver_response_ids": [response_id],
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_count": 0,
            "superseded_by_collaboration_message_usage": {
                field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
            },
            "superseded_by_collaboration_message_response_ids": [],
            "superseded_by_collaboration_message_evidence": [],
            "discarded_after_explicit_child_interrupt_response_count": 0,
            "discarded_after_explicit_child_interrupt_usage": {
                field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
            },
            "discarded_after_explicit_child_interrupt_response_ids": [],
            "discarded_after_explicit_child_interrupt_evidence": [],
        },
        "interrupt_requested": False,
        "pending_interrupt_response_count": 0,
        "invalid_reasons": [],
        "measurement_exact": True,
        "first_crossing": usage_crossing,
        "stop_reason": "token_limit" if crossed else close_reason,
        "appserver_response_ledger": [
            {
                "response_id": response_id,
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "raw_response_notification_sequence": 1,
                "raw_response_observed_at_unix_ns": 10_570,
                "raw_response_observed_at_monotonic_ns": 1_570,
                "usage": normalized,
                "provider_gate_call": call,
            }
        ],
        "provider_token_gate": {
            "enabled": True,
            "response_token_bound": response_bound,
            "artifact_path": str(path),
            "record_sha256": record["record_sha256"],
            "final_attached": True,
            "exact_for_usage": True,
            "live": state,
            "terminal": state,
        },
        "adapter_teardown": {
            "process_group_isolated": True,
            "immediate": crossed or close_reason == "accepted_submission",
            "stdin_closed": True,
            "signal": "SIGTERM" if crossed else None,
            "returncode": 0,
            "completed": True,
            "started_at_unix_ns": 10_900,
            "started_at_monotonic_ns": 1_900,
            "completed_at_unix_ns": 11_000,
            "completed_at_monotonic_ns": 2_000,
        },
    }
    expected = {
        "token_limit": token_limit,
        "run_id": "fixture-run",
        "model": "gpt-5.6-sol",
        "reasoning_effort": "ultra",
        "root_thread_id": "root-thread",
        "prompt_release_sha256": "4" * 64,
        "prompt_release_protocol": "highambench-prompt-release-v1",
        "prompt_sha256": "5" * 64,
        "model_catalog_sha256": catalog_sha,
        "model_entry_sha256": entry_sha,
        "expected_transport_provenance": copy.deepcopy(transport),
        "expected_source_sha256": source_sha,
    }
    return record, usage, expected


def synthetic_job_1508245_gate(
    path: Path,
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    """Create the exact nine-provider/eight-appserver suppression shape."""

    record, _usage, expected = synthetic_provider_gate(
        path,
        close_reason="natural_end",
        token_limit=5_000_000,
    )
    response_bound = 272_000
    provider_totals = [10_000] * 6 + [11_835, 10_000, 24_667]
    calls: list[dict[str, object]] = []
    direct_calls: list[dict[str, object]] = []
    running = 0
    event_sequence = 0
    suppressed_index = 6
    for index, total in enumerate(provider_totals):
        response_id = f"resp-job-1508245-{index + 1}"
        call_sequence = index + 3
        admitted_mono = 1_300 + index * 300
        commit_mono = admitted_mono + 100
        unix_shift = 2_000_000 if index > suppressed_index else 0
        normalized = {
            "input_tokens": total - 100,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 100,
            "reasoning_output_tokens": 0,
            "total_tokens": total,
        }
        raw_usage = {
            "input_tokens": total - 100,
            "input_tokens_details": {
                "cached_tokens": 0,
                "cache_write_tokens": 0,
            },
            "output_tokens": 100,
            "output_tokens_details": {"reasoning_tokens": 0},
            "total_tokens": total,
        }
        output: list[dict[str, object]] = []
        events: list[dict[str, object]] = []
        if index == suppressed_index:
            wait_item: dict[str, object] = {
                "type": "function_call",
                "id": "fc-job-1508245-wait",
                "status": "completed",
                "call_id": "call-job-1508245-wait",
                "name": "wait_agent",
                "namespace": "collaboration",
                "arguments": '{"timeout_ms":1280}',
            }
            output.append(wait_item)
            events.append(
                {
                    "type": "response.output_item.done",
                    "output_index": 0,
                    "item": wait_item,
                }
            )
        events.append(
            {
                "type": "response.completed",
                "response": {
                    "id": response_id,
                    "usage": raw_usage,
                    "end_turn": False,
                    "output": output,
                },
            }
        )
        body = "".join(
            f"event: {event['type']}\ndata: "
            + json.dumps(event, separators=(",", ":"))
            + "\n\n"
            for event in events
        ).encode("utf-8")
        manifest_items: list[dict[str, object]] = []
        for output_index, output_item in enumerate(output):
            payload = json.dumps(
                output_item,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ).encode("utf-8")
            arguments = str(output_item["arguments"])
            arguments_payload = arguments.encode("utf-8")
            manifest_items.append(
                {
                    "index": output_index,
                    "id": output_item["id"],
                    "type": output_item["type"],
                    "name": output_item["name"],
                    "namespace": output_item["namespace"],
                    "call_id": output_item["call_id"],
                    "payload_sha256": hashlib.sha256(payload).hexdigest(),
                    "payload_bytes": len(payload),
                    "arguments_sha256": hashlib.sha256(
                        arguments_payload
                    ).hexdigest(),
                    "arguments_bytes": len(arguments_payload),
                    "wait_timeout_ms": 1280,
                }
            )
        running_before = running
        running += total
        call: dict[str, object] = {
            "sequence": call_sequence,
            "call_id": f"provider-call-{call_sequence:08d}",
            "method": "POST",
            "route": "/responses",
            "request_body_sha256": hashlib.sha256(
                f"request-{index}".encode()
            ).hexdigest(),
            "request_bytes": len(f"request-{index}"),
            "request_model": "gpt-5.6-sol",
            "request_stream": True,
            "request_metadata": {
                "installation_id": "install",
                "session_id": "session",
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "request_kind": "turn",
                "window_id": "window",
            },
            "credential_headers_present": ["authorization"],
            "admission_mode": "EXCLUSIVE",
            "response_bound": response_bound,
            "completed_before": running_before,
            "open_before": 0,
            "reserved_before": running_before,
            "reservation_after": running_before + response_bound,
            "admitted_unix_ns": admitted_mono + 9_000 + unix_shift,
            "admitted_monotonic_ns": admitted_mono,
            "upstream_started": True,
            "upstream_start_unix_ns": admitted_mono + 9_050 + unix_shift,
            "upstream_start_monotonic_ns": admitted_mono + 50,
            "upstream_status": 200,
            "upstream_content_type": "text/event-stream; charset=utf-8",
            "upstream_content_type_occurrences": 1,
            "upstream_content_encoding": "identity",
            "upstream_content_encoding_occurrences": 1,
            "upstream_sse_authentication": {
                "schema_version": 1,
                "protocol": "highambench-responses-sse-envelope-v1",
                "parser": "highambench-strict-responses-sse-v2",
                "complete": True,
                "content_type_basis": "declared_text_event_stream",
                "content_encoding_basis": "declared_identity",
                "json_event_count": len(events),
                "completed_event_index": len(events) - 1,
                "done_count": 0,
                "body_sha256": hashlib.sha256(body).hexdigest(),
                "body_bytes": len(body),
                "response_id": response_id,
                "downstream_content_type_synthesized": False,
            },
            "upstream_body_sha256": hashlib.sha256(body).hexdigest(),
            "upstream_body_bytes": len(body),
            "response_id": response_id,
            "usage": raw_usage,
            "normalized_usage": normalized,
            "previous_total": running_before,
            "committed_total": running,
            "commit_unix_ns": commit_mono + 9_000 + unix_shift,
            "commit_monotonic_ns": commit_mono,
            "crossed_cap": False,
            "release_kind": "byte_identity",
            "released_body_sha256": hashlib.sha256(body).hexdigest(),
            "released_body_bytes": len(body),
            "released_sanitized_event": None,
            "released_sanitized_events": None,
            "released_sanitized_body_utf8": None,
            "client_release_complete": True,
            "response_output_manifest": {
                "schema_version": 1,
                "response_id": response_id,
                "output_item_count": len(manifest_items),
                "action_capable_item_count": len(manifest_items),
                "items": manifest_items,
            },
            "appserver_crossbind": None,
            "appserver_delivery": None,
            "error": None,
        }
        if index != suppressed_index:
            event_sequence += 1
            bind_mono = commit_mono + 20
            crossbind = {
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "event_sequence": event_sequence,
                "normalized_usage": normalized,
                "bind_unix_ns": bind_mono + 9_000 + unix_shift,
                "bind_monotonic_ns": bind_mono,
            }
            call["appserver_crossbind"] = crossbind
            call["appserver_delivery"] = {
                "kind": "direct_raw_response",
                "successor_call_id": None,
                "successor_response_id": None,
                "bind_unix_ns": bind_mono + 9_000 + unix_shift,
                "bind_monotonic_ns": bind_mono,
            }
            direct_calls.append(call)
        calls.append(call)
    suppressed = calls[suppressed_index]
    successor = calls[suppressed_index + 1]
    suppressed["appserver_delivery"] = {
        "kind": "suppressed_collaboration_wait",
        "successor_call_id": successor["call_id"],
        "successor_response_id": successor["response_id"],
        "bind_unix_ns": int(successor["commit_unix_ns"]) + 30,
        "bind_monotonic_ns": int(successor["commit_monotonic_ns"]) + 30,
    }
    record["calls"] = calls
    record["state"].update(
        {"completed_tokens": 106_502, "sequence": 12}
    )
    record["transitions"][-1].update(
        {
            "sequence": 12,
            "unix_ns": 3_013_900,
            "monotonic_ns": 4_900,
        }
    )
    record["lifecycle"].update(
        {
            "stopped_unix_ns": 3_014_000,
            "stopped_monotonic_ns": 5_000,
            "finalized_unix_ns": 3_014_100,
            "finalized_monotonic_ns": 5_100,
        }
    )
    _seal_synthetic_gate(path, record)
    fields = tuple(runner_module.PROVIDER_GATE_USAGE_KEYS)
    provider_usage_sum = {
        field: sum(int(call["normalized_usage"][field]) for call in calls)
        for field in fields
    }
    appserver_usage_sum = {
        field: sum(int(call["normalized_usage"][field]) for call in direct_calls)
        for field in fields
    }
    suppressed_usage = dict(suppressed["normalized_usage"])
    provider_ids = [str(call["response_id"]) for call in calls]
    appserver_ids = [str(call["response_id"]) for call in direct_calls]
    message_mono = int(suppressed["commit_monotonic_ns"]) + 50
    message_wall = 1_000_000
    evidence = {
        "response_id": suppressed["response_id"],
        "provider_call_id": suppressed["call_id"],
        "thread_id": "root-thread",
        "turn_id": "root-turn",
        "successor_response_id": successor["response_id"],
        "successor_call_id": successor["call_id"],
        "agent_message_item_id": "amsg-job-1508245-child",
        "agent_message_sha256": "a" * 64,
        "agent_message_author": "/root/ultra_child",
        "agent_message_recipient": "/root",
        "agent_message_observed_at_unix_ns": message_wall,
        "agent_message_observed_at_monotonic_ns": message_mono,
    }
    reconciliation = {
        "schema_version": 3,
        "provider_response_count": 9,
        "appserver_response_count": 8,
        "suppressed_collaboration_wait_response_count": 1,
        "provider_usage": provider_usage_sum,
        "appserver_usage": appserver_usage_sum,
        "suppressed_collaboration_wait_usage": suppressed_usage,
        "provider_response_ids": provider_ids,
        "appserver_response_ids": appserver_ids,
        "suppressed_collaboration_wait_response_ids": [
            suppressed["response_id"]
        ],
        "suppressed_collaboration_wait_evidence": [evidence],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_usage": {
            field: 0 for field in fields
        },
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_usage": {
            field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
        },
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_evidence": [],
    }
    usage: dict[str, object] = {
        **{
            "input_tokens": provider_usage_sum["input_tokens"],
            "cached_input_tokens": provider_usage_sum["cached_input_tokens"],
            "cache_write_input_tokens": provider_usage_sum[
                "cache_write_input_tokens"
            ],
            "output_tokens": provider_usage_sum["output_tokens"],
            "reasoning_output_tokens": provider_usage_sum[
                "reasoning_output_tokens"
            ],
            "model_tokens": provider_usage_sum["total_tokens"],
        },
        "response_count": 9,
        "response_ids": provider_ids,
        "provider_response_count": 9,
        "provider_response_ids": provider_ids,
        "provider_usage": provider_usage_sum,
        "appserver_response_count": 8,
        "appserver_response_ids": appserver_ids,
        "appserver_usage": appserver_usage_sum,
        "suppressed_collaboration_wait_response_count": 1,
        "suppressed_collaboration_wait_response_ids": [
            suppressed["response_id"]
        ],
        "suppressed_collaboration_wait_usage": suppressed_usage,
        "suppressed_collaboration_wait_evidence": [evidence],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_usage": {
            field: 0 for field in fields
        },
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_usage": {
            field: 0 for field in fields
        },
        "discarded_after_explicit_child_interrupt_evidence": [],
        "provider_usage_reconciliation": reconciliation,
        "notification_sequence": 8,
        "interrupt_requested": False,
        "pending_interrupt_response_count": 0,
        "invalid_reasons": [],
        "measurement_exact": True,
        "first_crossing": None,
        "stop_reason": "natural_end",
        "appserver_response_ledger": [
            {
                "response_id": call["response_id"],
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "raw_response_notification_sequence": call[
                    "appserver_crossbind"
                ]["event_sequence"],
                "raw_response_observed_at_unix_ns": call[
                    "appserver_crossbind"
                ]["bind_unix_ns"]
                + 10,
                "raw_response_observed_at_monotonic_ns": call[
                    "appserver_crossbind"
                ]["bind_monotonic_ns"]
                + 10,
                "usage": call["normalized_usage"],
                "provider_gate_call": call,
            }
            for call in direct_calls
        ],
        "provider_token_gate": {
            "enabled": True,
            "response_token_bound": response_bound,
            "artifact_path": str(path),
            "record_sha256": record["record_sha256"],
            "final_attached": True,
            "exact_for_usage": True,
            "live": record["state"],
            "terminal": record["state"],
        },
        "adapter_teardown": {
            "process_group_isolated": True,
            "immediate": False,
            "stdin_closed": True,
            "signal": None,
            "returncode": 0,
            "completed": True,
            "started_at_unix_ns": 14_200,
            "started_at_monotonic_ns": 5_200,
            "completed_at_unix_ns": 14_300,
            "completed_at_monotonic_ns": 5_300,
        },
    }
    expected["token_limit"] = 5_000_000
    return record, usage, expected


def active_tree_provider_crossing_usage(
    path: Path, *, request_kind: str = "turn"
) -> dict[str, object]:
    """Return a projection-v3 crossing whose cumulative tree tail is incomplete."""

    record, gate_usage, _expected = synthetic_provider_gate(
        path, request_kind=request_kind
    )
    if request_kind == "compaction":
        # Match the pinned adapter canary, rather than merely changing the
        # crossing call's request-kind label: one completed below-cap prompt
        # response is followed by exactly one explicitly authorized root
        # compaction turn.  The compaction RawResponse is crossbound while that
        # distinct second turn is still active.
        crossing_call = copy.deepcopy(record["calls"][0])
        aggregate = copy.deepcopy(crossing_call["normalized_usage"])
        prompt_usage = {
            "input_tokens": 100,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 0,
            "reasoning_output_tokens": 0,
            "total_tokens": 100,
        }
        prompt_raw_usage = {
            "input_tokens": 100,
            "input_tokens_details": {
                "cached_tokens": 0,
                "cache_write_tokens": 0,
            },
            "output_tokens": 0,
            "output_tokens_details": {"reasoning_tokens": 0},
            "total_tokens": 100,
        }
        prompt_event = {
            "type": "response.completed",
            "response": {
                "id": "resp-fixture-prompt",
                "usage": prompt_raw_usage,
            },
        }
        prompt_body = (
            "event: response.completed\ndata: "
            + json.dumps(
                prompt_event,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n\n"
        ).encode("utf-8")
        prompt_call = copy.deepcopy(crossing_call)
        prompt_call.update(
            {
                "sequence": 3,
                "call_id": "provider-call-00000003",
                "request_body_sha256": hashlib.sha256(
                    b"prompt request"
                ).hexdigest(),
                "request_bytes": len(b"prompt request"),
                "request_metadata": {
                    **crossing_call["request_metadata"],
                    "turn_id": "root-turn",
                    "request_kind": "turn",
                },
                "completed_before": 0,
                "previous_total": 0,
                "admitted_unix_ns": 10_250,
                "admitted_monotonic_ns": 1_250,
                "upstream_start_unix_ns": 10_260,
                "upstream_start_monotonic_ns": 1_260,
                "upstream_body_sha256": hashlib.sha256(prompt_body).hexdigest(),
                "upstream_body_bytes": len(prompt_body),
                "response_id": "resp-fixture-prompt",
                "upstream_sse_authentication": {
                    **crossing_call["upstream_sse_authentication"],
                    "json_event_count": 1,
                    "completed_event_index": 0,
                    "body_sha256": hashlib.sha256(prompt_body).hexdigest(),
                    "body_bytes": len(prompt_body),
                    "response_id": "resp-fixture-prompt",
                },
                "usage": prompt_raw_usage,
                "normalized_usage": prompt_usage,
                "committed_total": 100,
                "commit_unix_ns": 10_300,
                "commit_monotonic_ns": 1_300,
                "crossed_cap": False,
                "release_kind": "byte_identity",
                "released_body_sha256": hashlib.sha256(prompt_body).hexdigest(),
                "released_body_bytes": len(prompt_body),
                "released_sanitized_event": None,
                "released_sanitized_events": None,
                "released_sanitized_body_utf8": None,
                "appserver_crossbind": {
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "event_sequence": 1,
                    "normalized_usage": prompt_usage,
                    "bind_unix_ns": 10_350,
                    "bind_monotonic_ns": 1_350,
                },
            }
        )

        compaction_usage = copy.deepcopy(aggregate)
        compaction_usage["input_tokens"] -= prompt_usage["input_tokens"]
        compaction_usage["total_tokens"] -= prompt_usage["total_tokens"]
        compaction_raw_usage = copy.deepcopy(crossing_call["usage"])
        compaction_raw_usage["input_tokens"] = compaction_usage["input_tokens"]
        compaction_raw_usage["total_tokens"] = compaction_usage["total_tokens"]
        completed_event = copy.deepcopy(crossing_call["released_sanitized_event"])
        completed_event["response"]["usage"] = compaction_raw_usage
        compaction_events = [
            copy.deepcopy(crossing_call["released_sanitized_events"][0]),
            completed_event,
        ]
        compaction_wire = "".join(
            "event: "
            + event["type"]
            + "\ndata: "
            + json.dumps(
                event,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n\n"
            for event in compaction_events
        ).encode("utf-8")
        crossing_call.update(
            {
                "sequence": 4,
                "call_id": "provider-call-00000004",
                "request_metadata": {
                    **crossing_call["request_metadata"],
                    "turn_id": "compaction-turn",
                    "request_kind": "compaction",
                },
                "completed_before": 100,
                "reserved_before": 100,
                "reservation_after": 272_100,
                "previous_total": 100,
                "admitted_unix_ns": 10_400,
                "admitted_monotonic_ns": 1_400,
                "upstream_start_unix_ns": 10_500,
                "upstream_start_monotonic_ns": 1_500,
                "usage": compaction_raw_usage,
                "normalized_usage": compaction_usage,
                "upstream_body_sha256": hashlib.sha256(compaction_wire).hexdigest(),
                "upstream_body_bytes": len(compaction_wire),
                "upstream_sse_authentication": {
                    **crossing_call["upstream_sse_authentication"],
                    "json_event_count": 2,
                    "completed_event_index": 1,
                    "body_sha256": hashlib.sha256(compaction_wire).hexdigest(),
                    "body_bytes": len(compaction_wire),
                },
                "committed_total": aggregate["total_tokens"],
                "commit_unix_ns": 10_600,
                "commit_monotonic_ns": 1_600,
                "released_body_sha256": hashlib.sha256(compaction_wire).hexdigest(),
                "released_body_bytes": len(compaction_wire),
                "released_sanitized_event": completed_event,
                "released_sanitized_events": compaction_events,
                "released_sanitized_body_utf8": compaction_wire.decode("utf-8"),
                "appserver_crossbind": {
                    "thread_id": "root-thread",
                    "turn_id": "compaction-turn",
                    "event_sequence": 2,
                    "normalized_usage": compaction_usage,
                    "bind_unix_ns": 10_650,
                    "bind_monotonic_ns": 1_650,
                },
            }
        )
        crossing = record["state"]["crossing"]
        crossing.update(
            {
                "call_id": crossing_call["call_id"],
                "sequence": 5,
                "previous_total": 100,
                "response_tokens": compaction_usage["total_tokens"],
                "commit_unix_ns": crossing_call["commit_unix_ns"],
                "commit_monotonic_ns": crossing_call["commit_monotonic_ns"],
            }
        )
        record["calls"] = [prompt_call, crossing_call]
        record["transitions"][-1].update(
            {
                "sequence": 6,
                "call_id": crossing_call["call_id"],
                "unix_ns": 10_700,
                "monotonic_ns": 1_700,
            }
        )
        record["state"]["sequence"] = 6
        record["lifecycle"].update(
            {
                "stopped_unix_ns": 10_800,
                "stopped_monotonic_ns": 1_800,
                "finalized_unix_ns": 10_900,
                "finalized_monotonic_ns": 1_900,
            }
        )
        _seal_synthetic_gate(path, record)
        gate_usage.update(
            {
                "response_count": 2,
                "notification_sequence": 2,
                "response_ids": [
                    prompt_call["response_id"],
                    crossing_call["response_id"],
                ],
                "first_crossing": {
                    "response_id": crossing_call["response_id"],
                    "notification_sequence": 2,
                    "observed_at_unix_ns": 10_670,
                    "tokens": aggregate["total_tokens"],
                    "active_thread_ids": ["root-thread"],
                },
                "response_ledger": [
                    {
                        "response_id": prompt_call["response_id"],
                        "thread_id": "root-thread",
                        "turn_id": "root-turn",
                        "raw_response_notification_sequence": 1,
                        "raw_response_observed_at_unix_ns": 10_360,
                        "raw_response_observed_at_monotonic_ns": 1_360,
                        "usage": prompt_usage,
                        "provider_gate_call": prompt_call,
                    },
                    {
                        "response_id": crossing_call["response_id"],
                        "thread_id": "root-thread",
                        "turn_id": "compaction-turn",
                        "raw_response_notification_sequence": 2,
                        "raw_response_observed_at_unix_ns": 10_670,
                        "raw_response_observed_at_monotonic_ns": 1_670,
                        "usage": compaction_usage,
                        "provider_gate_call": crossing_call,
                    },
                ],
            }
        )
        gate_usage["provider_token_gate"].update(
            {
                "record_sha256": record["record_sha256"],
                "live": copy.deepcopy(record["state"]),
                "terminal": copy.deepcopy(record["state"]),
            }
        )
        gate_usage["adapter_teardown"].update(
            {
                "started_at_unix_ns": 11_000,
                "started_at_monotonic_ns": 2_000,
                "completed_at_unix_ns": 11_100,
                "completed_at_monotonic_ns": 2_100,
            }
        )
    call = copy.deepcopy(record["calls"][-1])
    normalized = {
        field: gate_usage[field]
        for field in runner_module.PROVIDER_GATE_USAGE_KEYS
    }
    zero = ultra_usage_breakdown(0, 0, 0, 0)
    thread = {
        "thread_id": "root-thread",
        "parent_thread_id": None,
        "agent_path": "root",
        "provisional": False,
        "spawn_call_id": None,
        "spawn_parent_turn_id": None,
        "spawn_parent_response_id": None,
        "spawn_fork_turns": None,
        "spawn_fork_semantics": None,
        "spawn_binding_status": "root_zero",
        "turn_seen": True,
        "active_turn_id": (
            "compaction-turn" if request_kind == "compaction" else "root-turn"
        ),
        "turn_status": "inProgress",
        "thread_status": "active",
        "response_count": gate_usage["response_count"],
        **normalized,
        "cumulative_baseline": zero,
        "expected_cumulative_baseline": zero,
        "last_cumulative": None,
        "cumulative_observation_count": 0,
        "expected_cumulative_projection": normalized,
        "full_cumulative_projection": normalized,
        "cumulative_projection_exempt_response_id": None,
        "cumulative_projection_exempt_response_usage": None,
        "observed_cumulative_baseline": None,
        "cumulative_baseline_matches_expected": False,
        "cumulative_projection_match": False,
        "cumulative_projection_status": "missing_cumulative",
        "accounting_complete": False,
    }
    response_ledger = copy.deepcopy(gate_usage["response_ledger"])
    return {
        "schema_version": 1,
        "accounting_projection_schema_version": (
            ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "measurement_source": ULTRA_USAGE_MEASUREMENT_SOURCE,
        "notification": ULTRA_USAGE_NOTIFICATION,
        "usage_scope": ULTRA_USAGE_SCOPE,
        "live_cumulative": True,
        "input_includes_cached": True,
        "root_thread_id": "root-thread",
        "root_turn_id": "root-turn",
        "thread_count": 1,
        "response_count": gate_usage["response_count"],
        **normalized,
        "notification_sequence": gate_usage["notification_sequence"],
        "observed_at_unix_ns": (
            10_670 if request_kind == "compaction" else 10_570
        ),
        "first_crossing": copy.deepcopy(gate_usage["first_crossing"]),
        "stop_reason": "token_limit",
        "interrupt_requested": False,
        "pending_interrupt_response_count": 0,
        "active_thread_ids": ["root-thread"],
        "unresolved_thread_ids": [],
        "drain_complete": False,
        "measurement_exact": True,
        "invalid_reasons": [],
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "raw_spawn_call_ids": [],
        "activity_spawn_call_ids": [],
        "collab_spawn_call_ids": [],
        "resolved_spawn_call_ids": [],
        "failed_spawn_call_ids": [],
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": [],
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": False,
        "accounting_complete": False,
        "threads": [thread],
        "response_ids": copy.deepcopy(gate_usage["response_ids"]),
        "response_ledger": response_ledger,
        "provider_token_gate": copy.deepcopy(gate_usage["provider_token_gate"]),
        "adapter_teardown": copy.deepcopy(gate_usage["adapter_teardown"]),
        **ultra_fork_policy_fields(),
    }


def ultra_fork_policy_fields(
    call_evidence: list[dict[str, object]] | None = None,
    *,
    observed: list[str] | None = None,
    allowed: list[str] | None = None,
    blocked: list[str] | None = None,
    invalid: list[str] | None = None,
    complete: bool = True,
) -> dict[str, object]:
    policy = codex_isolated.ultra_fork_policy_static_record("/u501/m2fetrat")
    policy.update(
        {
            "call_evidence": [] if call_evidence is None else call_evidence,
            "complete": complete,
        }
    )
    return {
        "fork_policy": policy,
        "hook_observed_spawn_call_ids": [] if observed is None else observed,
        "hook_allowed_spawn_call_ids": [] if allowed is None else allowed,
        "hook_blocked_spawn_call_ids": [] if blocked is None else blocked,
        "policy_blocked_spawn_call_ids": [] if blocked is None else blocked,
        "hook_invalid_spawn_call_ids": [] if invalid is None else invalid,
        "fork_policy_complete": complete,
    }


def ultra_usage_breakdown(
    input_tokens: int,
    cached_input_tokens: int,
    output_tokens: int,
    reasoning_output_tokens: int,
) -> dict[str, int]:
    return {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached_input_tokens,
        "cache_write_input_tokens": 0,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning_output_tokens,
        "total_tokens": input_tokens + output_tokens,
    }


def ultra_policy_call_evidence(
    call_id: str,
    *,
    response_id: str,
    fork_turns: str,
    fork_semantics: str,
    decision: str,
    resolution_status: str,
    child_activity: bool,
) -> dict[str, object]:
    source_path = codex_isolated.ultra_fork_policy_static_record(
        "/u501/m2fetrat"
    )["source_path"]
    blocked = decision == codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
    return {
        "call_id": call_id,
        "parent_thread_id": "root",
        "parent_turn_id": "root-turn",
        "parent_response_id": response_id,
        "fork_turns": fork_turns,
        "fork_semantics": fork_semantics,
        "hook_run_id": f"pre-tool-use:0:{source_path}:{call_id}",
        "hook_source_path": source_path,
        "hook_thread_id": "root",
        "hook_turn_id": "root-turn",
        "hook_started_observed": True,
        "hook_started_count": 1,
        "hook_completed_observed": True,
        "hook_completed_count": 1,
        "hook_status": (
            codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
            if blocked
            else codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
        ),
        "decision": decision,
        "feedback": (
            codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                call_id=call_id
            )
            if blocked
            else None
        ),
        "resolution_status": resolution_status,
        "child_activity_observed": child_activity,
    }


def blocked_positive_then_all_usage() -> dict[str, object]:
    """One exact tree with a denied positive fork followed by an all-history child."""

    zero = ultra_usage_breakdown(0, 0, 0, 0)
    first_root_response = ultra_usage_breakdown(12, 4, 3, 1)
    root_raw = ultra_usage_breakdown(30, 10, 7, 3)
    child_raw = ultra_usage_breakdown(11, 3, 4, 2)
    child_cumulative = {
        field: first_root_response[field] + child_raw[field]
        for field in first_root_response
    }
    totals = {
        field: root_raw[field] + child_raw[field] for field in root_raw
    }
    second_root_response = {
        field: root_raw[field] - first_root_response[field]
        for field in root_raw
    }
    root_thread = {
        "thread_id": "root",
        "parent_thread_id": None,
        "agent_path": "root",
        "provisional": False,
        "spawn_call_id": None,
        "spawn_parent_turn_id": None,
        "spawn_parent_response_id": None,
        "spawn_fork_turns": None,
        "spawn_fork_semantics": None,
        "spawn_binding_status": "root_zero",
        "turn_seen": True,
        "active_turn_id": None,
        "turn_status": "completed",
        "thread_status": "idle",
        "response_count": 2,
        **root_raw,
        "cumulative_baseline": zero,
        "expected_cumulative_baseline": zero,
        "last_cumulative": root_raw,
        "cumulative_observation_count": 1,
        "expected_cumulative_projection": root_raw,
        "full_cumulative_projection": root_raw,
        "cumulative_projection_exempt_response_id": None,
        "cumulative_projection_exempt_response_usage": None,
        "observed_cumulative_baseline": zero,
        "cumulative_baseline_matches_expected": True,
        "cumulative_projection_match": True,
        "cumulative_projection_status": "matched_full_projection",
        "accounting_complete": True,
    }
    child_thread = {
        "thread_id": "child-all",
        "parent_thread_id": "root",
        "agent_path": "root/child-all",
        "provisional": False,
        "spawn_call_id": "call_all",
        "spawn_parent_turn_id": "root-turn",
        "spawn_parent_response_id": "root-r2",
        "spawn_fork_turns": "all",
        "spawn_fork_semantics": "full_history_parent_pre_response",
        "spawn_binding_status": "resolved",
        "turn_seen": True,
        "active_turn_id": None,
        "turn_status": "completed",
        "thread_status": "idle",
        "response_count": 1,
        **child_raw,
        "cumulative_baseline": first_root_response,
        "expected_cumulative_baseline": first_root_response,
        "last_cumulative": child_cumulative,
        "cumulative_observation_count": 1,
        "expected_cumulative_projection": child_cumulative,
        "full_cumulative_projection": child_cumulative,
        "cumulative_projection_exempt_response_id": None,
        "cumulative_projection_exempt_response_usage": None,
        "observed_cumulative_baseline": first_root_response,
        "cumulative_baseline_matches_expected": True,
        "cumulative_projection_match": True,
        "cumulative_projection_status": "matched_full_projection",
        "accounting_complete": True,
    }
    call_all = ultra_policy_call_evidence(
        "call_all",
        response_id="root-r2",
        fork_turns="all",
        fork_semantics="full_history_parent_pre_response",
        decision=codex_isolated.ULTRA_FORK_POLICY_ALLOW_DECISION,
        resolution_status="resolved_child",
        child_activity=True,
    )
    call_positive = ultra_policy_call_evidence(
        "call_positive",
        response_id="root-r1",
        fork_turns="3",
        fork_semantics="unsupported_positive_turn_suffix",
        decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
        resolution_status=codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS,
        child_activity=False,
    )
    return {
        "schema_version": 1,
        "accounting_projection_schema_version": (
            ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "measurement_source": ULTRA_USAGE_MEASUREMENT_SOURCE,
        "notification": ULTRA_USAGE_NOTIFICATION,
        "usage_scope": ULTRA_USAGE_SCOPE,
        "live_cumulative": True,
        "input_includes_cached": True,
        "root_thread_id": "root",
        "root_turn_id": "root-turn",
        "thread_count": 2,
        "response_count": 3,
        **totals,
        "notification_sequence": 3,
        "observed_at_unix_ns": 123,
        "first_crossing": None,
        "stop_reason": None,
        "interrupt_requested": False,
        "pending_interrupt_response_count": 0,
        "active_thread_ids": [],
        "unresolved_thread_ids": [],
        "drain_complete": True,
        "measurement_exact": True,
        "invalid_reasons": [],
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "raw_spawn_call_ids": ["call_all", "call_positive"],
        "activity_spawn_call_ids": ["call_all"],
        "collab_spawn_call_ids": [],
        "resolved_spawn_call_ids": ["call_all"],
        "failed_spawn_call_ids": ["call_positive"],
        "policy_blocked_spawn_call_ids": ["call_positive"],
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": ["child-all"],
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "accounting_complete": True,
        "threads": [child_thread, root_thread],
        "response_ids": ["root-r1", "root-r2", "child-r1"],
        "response_ledger": [
            {
                "response_id": "root-r1",
                "thread_id": "root",
                "turn_id": "root-turn",
                "raw_response_notification_sequence": 1,
                "raw_response_observed_at_unix_ns": 101,
                "raw_response_observed_at_monotonic_ns": 201,
                "usage": first_root_response,
                "provider_gate_call": None,
            },
            {
                "response_id": "root-r2",
                "thread_id": "root",
                "turn_id": "root-turn",
                "raw_response_notification_sequence": 2,
                "raw_response_observed_at_unix_ns": 102,
                "raw_response_observed_at_monotonic_ns": 202,
                "usage": second_root_response,
                "provider_gate_call": None,
            },
            {
                "response_id": "child-r1",
                "thread_id": "child-all",
                "turn_id": "child-turn",
                "raw_response_notification_sequence": 3,
                "raw_response_observed_at_unix_ns": 103,
                "raw_response_observed_at_monotonic_ns": 203,
                "usage": child_raw,
                "provider_gate_call": None,
            },
        ],
        **ultra_fork_policy_fields(
            [call_all, call_positive],
            observed=["call_all", "call_positive"],
            allowed=["call_all"],
            blocked=["call_positive"],
        ),
    }


def job_1509778_reactivated_interrupt_usage() -> dict[str, object]:
    """An interrupted child discard retained after a follow-up starts a new turn."""

    value = blocked_positive_then_all_usage()
    fields = tuple(runner_module.PROVIDER_GATE_USAGE_KEYS)
    zero = {field: 0 for field in fields}
    discarded_usage = ultra_usage_breakdown(5, 0, 1, 0)
    appserver_usage = {field: int(value[field]) for field in fields}
    provider_usage = {
        field: appserver_usage[field] + discarded_usage[field]
        for field in fields
    }
    child = next(
        thread
        for thread in value["threads"]
        if thread["thread_id"] == "child-all"
    )
    child.update(
        {
            "agent_path": "/root/library_search",
            "turn_status": "inProgress",
            "active_turn_id": "child-followup-turn-1509778",
            "thread_status": "active",
        }
    )
    value.update(
        {
            "active_thread_ids": ["child-all"],
            "drain_complete": False,
            "measurement_exact": False,
        }
    )
    evidence = {
        "response_id": "discarded-child-response-1509778",
        "provider_call_id": "discarded-child-call-1509778",
        "thread_id": "child-all",
        "turn_id": "child-interrupted-turn-1509778",
        "interrupting_response_id": "root-r2",
        "interrupting_provider_call_id": "interrupting-call-1509778",
        "interrupt_function_item_id": "interrupt-item-1509778",
        "interrupt_function_call_id": "interrupt-tool-call-1509778",
        "interrupt_function_arguments_sha256": "a" * 64,
        "interrupt_parent_thread_id": "root",
        "interrupt_parent_turn_id": "root-turn",
        "interrupted_agent_path": "/root/library_search",
        "interrupt_activity_item_sha256": "b" * 64,
        "interrupt_output_item_id": "interrupt-output-1509778",
        "interrupt_output_item_sha256": "c" * 64,
        "interrupt_function_observed_at_unix_ns": 1,
        "interrupt_function_observed_at_monotonic_ns": 1,
        "interrupt_activity_observed_at_unix_ns": 2,
        "interrupt_activity_observed_at_monotonic_ns": 2,
        "interrupt_output_observed_at_unix_ns": 3,
        "interrupt_output_observed_at_monotonic_ns": 3,
        "interrupted_turn_observed_at_unix_ns": 4,
        "interrupted_turn_observed_at_monotonic_ns": 4,
    }
    value["provider_usage_reconciliation"] = {
        "schema_version": runner_module.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        "provider_response_count": 4,
        "appserver_response_count": 3,
        "suppressed_collaboration_wait_response_count": 0,
        "provider_usage": provider_usage,
        "appserver_usage": appserver_usage,
        "suppressed_collaboration_wait_usage": zero,
        "provider_response_ids": [
            "root-r1",
            "root-r2",
            "child-r1",
            "discarded-child-response-1509778",
        ],
        "appserver_response_ids": ["root-r1", "root-r2", "child-r1"],
        "suppressed_collaboration_wait_response_ids": [],
        "suppressed_collaboration_wait_evidence": [],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_usage": zero,
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 1,
        "discarded_after_explicit_child_interrupt_usage": discarded_usage,
        "discarded_after_explicit_child_interrupt_response_ids": [
            "discarded-child-response-1509778"
        ],
        "discarded_after_explicit_child_interrupt_evidence": [evidence],
    }
    return value


def job_1507844_positive_child_usage() -> dict[str, object]:
    """Preserve the measured positive-N child residual that halted job 1507844."""

    zero = ultra_usage_breakdown(0, 0, 0, 0)
    root_raw = ultra_usage_breakdown(24_604, 0, 259, 45)
    child_raw = ultra_usage_breakdown(723_093, 0, 6_682, 2_992)
    child_cumulative = ultra_usage_breakdown(747_697, 0, 6_941, 3_037)
    totals = {
        field: root_raw[field] + child_raw[field] for field in root_raw
    }
    root_thread = {
        "thread_id": "root",
        "parent_thread_id": None,
        "agent_path": "root",
        "provisional": False,
        "spawn_call_id": None,
        "spawn_parent_turn_id": None,
        "spawn_parent_response_id": None,
        "spawn_fork_turns": None,
        "spawn_fork_semantics": None,
        "spawn_binding_status": "root_zero",
        "turn_seen": True,
        "active_turn_id": None,
        "turn_status": "completed",
        "thread_status": "idle",
        "response_count": 2,
        **root_raw,
        "cumulative_baseline": zero,
        "expected_cumulative_baseline": zero,
        "last_cumulative": root_raw,
        "cumulative_observation_count": 1,
        "expected_cumulative_projection": root_raw,
        "full_cumulative_projection": root_raw,
        "cumulative_projection_exempt_response_id": None,
        "cumulative_projection_exempt_response_usage": None,
        "observed_cumulative_baseline": zero,
        "cumulative_baseline_matches_expected": True,
        "cumulative_projection_match": True,
        "cumulative_projection_status": "matched_full_projection",
        "accounting_complete": True,
    }
    child_thread = {
        "thread_id": "library-search-child",
        "parent_thread_id": "root",
        "agent_path": "root/library-search-child",
        "provisional": False,
        "spawn_call_id": None,
        "spawn_parent_turn_id": None,
        "spawn_parent_response_id": None,
        "spawn_fork_turns": None,
        "spawn_fork_semantics": None,
        "spawn_binding_status": "unresolved",
        "turn_seen": True,
        "active_turn_id": None,
        "turn_status": "completed",
        "thread_status": "idle",
        "response_count": 1,
        **child_raw,
        "cumulative_baseline": None,
        "expected_cumulative_baseline": None,
        "last_cumulative": child_cumulative,
        "cumulative_observation_count": 1,
        "expected_cumulative_projection": None,
        "full_cumulative_projection": None,
        "cumulative_projection_exempt_response_id": None,
        "cumulative_projection_exempt_response_usage": None,
        "observed_cumulative_baseline": None,
        "cumulative_baseline_matches_expected": False,
        "cumulative_projection_match": False,
        "cumulative_projection_status": "unresolved_expected_baseline",
        "accounting_complete": False,
    }
    positive = ultra_policy_call_evidence(
        "call_job1507844_positive",
        response_id="root-r2",
        fork_turns="3",
        fork_semantics="unsupported_positive_turn_suffix",
        decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
        resolution_status=codex_isolated.ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS,
        child_activity=True,
    )
    return {
        "schema_version": 1,
        "accounting_projection_schema_version": (
            ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "measurement_source": ULTRA_USAGE_MEASUREMENT_SOURCE,
        "notification": ULTRA_USAGE_NOTIFICATION,
        "usage_scope": ULTRA_USAGE_SCOPE,
        "live_cumulative": True,
        "input_includes_cached": True,
        "root_thread_id": "root",
        "root_turn_id": "root-turn",
        "thread_count": 2,
        "response_count": 3,
        **totals,
        "notification_sequence": 3,
        "observed_at_unix_ns": 123,
        "first_crossing": None,
        "stop_reason": None,
        "interrupt_requested": False,
        "pending_interrupt_response_count": 0,
        "active_thread_ids": [],
        "unresolved_thread_ids": [],
        "drain_complete": True,
        "measurement_exact": False,
        "invalid_reasons": [
            "spawn call call_job1507844_positive lacks exact fork-policy enforcement"
        ],
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "raw_spawn_call_ids": ["call_job1507844_positive"],
        "activity_spawn_call_ids": ["call_job1507844_positive"],
        "collab_spawn_call_ids": [],
        "resolved_spawn_call_ids": [],
        "failed_spawn_call_ids": [],
        "policy_blocked_spawn_call_ids": [],
        "unresolved_spawn_call_ids": ["call_job1507844_positive"],
        "unsupported_spawn_call_ids": ["call_job1507844_positive"],
        "inference_child_thread_ids": ["library-search-child"],
        "spawn_linkage_complete": False,
        "descendant_accounting_complete": False,
        "cumulative_projection_complete": False,
        "accounting_complete": False,
        "threads": [child_thread, root_thread],
        "response_ids": ["root-r1", "root-r2", "child-r1"],
        "response_ledger": [
            {
                "response_id": "root-r1",
                "thread_id": "root",
                "turn_id": "root-turn",
                "raw_response_notification_sequence": 1,
                "raw_response_observed_at_unix_ns": 101,
                "raw_response_observed_at_monotonic_ns": 201,
                "usage": ultra_usage_breakdown(0, 0, 0, 0),
                "provider_gate_call": None,
            },
            {
                "response_id": "root-r2",
                "thread_id": "root",
                "turn_id": "root-turn",
                "raw_response_notification_sequence": 2,
                "raw_response_observed_at_unix_ns": 102,
                "raw_response_observed_at_monotonic_ns": 202,
                "usage": root_raw,
                "provider_gate_call": None,
            },
            {
                "response_id": "child-r1",
                "thread_id": "library-search-child",
                "turn_id": "child-turn",
                "raw_response_notification_sequence": 3,
                "raw_response_observed_at_unix_ns": 103,
                "raw_response_observed_at_monotonic_ns": 203,
                "usage": child_raw,
                "provider_gate_call": None,
            },
        ],
        **ultra_fork_policy_fields(
            [positive],
            observed=["call_job1507844_positive"],
            invalid=["call_job1507844_positive"],
            complete=False,
        ),
    }


class RunnerTests(unittest.TestCase):
    def test_job_1508461_adapter_withholds_turn_result_before_started_event(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            usage_path = Path(directory) / "usage.json"

            class EmptyLiveGate:
                def snapshot(self) -> dict[str, object]:
                    return {
                        "phase": "CONCURRENT",
                        "close_reason": None,
                        "completed_tokens": 0,
                        "crossing": None,
                        "poisoned": False,
                    }

                def completed_response_usage_snapshot(
                    self,
                ) -> list[dict[str, object]]:
                    return []

            ledger = codex_isolated.AttemptUsageLedger(
                usage_path,
                5_000_000,
                "root-thread",
                fork_policy=codex_isolated.ultra_fork_policy_static_record(
                    "/u501/m2fetrat"
                ),
                provider_gate=EmptyLiveGate(),  # type: ignore[arg-type]
                provider_gate_artifact_path=(
                    Path(directory) / "usage.provider-token-gate.json"
                ),
            )
            ledger.publish(drain_complete=False)
            published_before_turn_result = usage_path.read_bytes()

            # Exact live order from job 1508461: the turn/start RPC result
            # supplies the ID, then thread/status/changed arrives before the
            # matching turn/started notification.
            ledger.root_turn_id = "root-turn"
            ledger.observe(
                {
                    "method": "thread/status/changed",
                    "params": {
                        "threadId": "root-thread",
                        "status": {"type": "active"},
                    },
                }
            )
            self.assertEqual(usage_path.read_bytes(), published_before_turn_result)

            transient_path = Path(directory) / "transient.json"
            write_json(transient_path, ledger.snapshot(drain_complete=False))

            with self.assertRaisesRegex(
                BenchmarkToolError,
                "root turn identity was never observed",
            ):
                read_token_usage(transient_path)

            ledger.observe(
                {
                    "method": "turn/started",
                    "params": {
                        "threadId": "root-thread",
                        "turn": {"id": "root-turn"},
                    },
                }
            )
            started = read_token_usage(usage_path)
            self.assertIsNotNone(started)
            assert started is not None
            self.assertEqual(started["root_turn_id"], "root-turn")
            self.assertEqual(started["model_tokens"], 0)

            # A final drain never receives the live-only deferral. If the
            # lifecycle notification never arrives, strict parsing still
            # rejects the final artifact.
            missing_started_path = Path(directory) / "missing-started.json"
            missing_started_ledger = codex_isolated.AttemptUsageLedger(
                missing_started_path,
                5_000_000,
                "root-thread",
                fork_policy=codex_isolated.ultra_fork_policy_static_record(
                    "/u501/m2fetrat"
                ),
                provider_gate=EmptyLiveGate(),  # type: ignore[arg-type]
                provider_gate_artifact_path=(
                    Path(directory) / "missing-started.provider-token-gate.json"
                ),
            )
            missing_started_ledger.root_turn_id = "root-turn"
            missing_started_ledger.publish(drain_complete=True)
            with self.assertRaisesRegex(
                BenchmarkToolError,
                "root turn identity was never observed",
            ):
                read_token_usage(missing_started_path)

    def test_job_1508245_provider_nine_appserver_eight_reconciles_exactly(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "job-1508245.provider-token-gate.json"
            record, usage, expected = synthetic_job_1508245_gate(path)
            authenticated = authenticate_provider_gate_artifact(
                path,
                usage=usage,
                **expected,
            )
            self.assertEqual(authenticated["derived"]["response_count"], 9)
            self.assertEqual(
                authenticated["derived"]["appserver_response_count"], 8
            )
            self.assertEqual(authenticated["derived"]["completed_tokens"], 106_502)
            self.assertEqual(
                authenticated["derived"][
                    "suppressed_collaboration_wait_response_count"
                ],
                1,
            )

            bad_usage = copy.deepcopy(usage)
            bad_usage["provider_usage_reconciliation"][
                "suppressed_collaboration_wait_evidence"
            ] = []
            with self.assertRaises(BenchmarkToolError):
                authenticate_provider_gate_artifact(
                    path,
                    usage=bad_usage,
                    **expected,
                )

            bad_usage = copy.deepcopy(usage)
            evidence = bad_usage["provider_usage_reconciliation"][
                "suppressed_collaboration_wait_evidence"
            ][0]
            evidence["agent_message_observed_at_unix_ns"] = record["calls"][
                6
            ]["commit_unix_ns"]
            with self.assertRaises(BenchmarkToolError):
                authenticate_provider_gate_artifact(
                    path,
                    usage=bad_usage,
                    **expected,
                )

            forged = copy.deepcopy(record)
            forged["calls"][6]["response_output_manifest"]["items"][0][
                "name"
            ] = "exec"
            _seal_synthetic_gate(path, forged)
            with self.assertRaises(BenchmarkToolError):
                authenticate_provider_gate_artifact(
                    path,
                    usage=usage,
                    **expected,
                )

    def test_job_1509232_child_exec_superseded_by_parent_message_replays(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "job-1509232.provider-token-gate.json"
            record, usage, expected = synthetic_job_1508245_gate(path)
            call = record["calls"][6]
            successor = record["calls"][7]
            for provider_call in (call, successor):
                provider_call["request_metadata"]["thread_id"] = "child-thread"
                provider_call["request_metadata"]["turn_id"] = "child-turn"
            successor["appserver_crossbind"]["thread_id"] = "child-thread"
            successor["appserver_crossbind"]["turn_id"] = "child-turn"
            for response in usage["appserver_response_ledger"]:
                if response["response_id"] == successor["response_id"]:
                    response["thread_id"] = "child-thread"
                    response["turn_id"] = "child-turn"
            manifest_item = call["response_output_manifest"]["items"][0]
            manifest_item.update(
                {
                    "type": "custom_tool_call",
                    "name": "exec",
                    "namespace": None,
                    "wait_timeout_ms": None,
                }
            )
            call["appserver_delivery"]["kind"] = (
                "superseded_by_collaboration_message"
            )
            reconciliation = usage["provider_usage_reconciliation"]
            old_evidence = reconciliation[
                "suppressed_collaboration_wait_evidence"
            ][0]
            message = {
                "item_id": old_evidence["agent_message_item_id"],
                "item_sha256": old_evidence["agent_message_sha256"],
                "author": "/root",
                "recipient": "/root/library_search",
                "observed_at_unix_ns": old_evidence[
                    "agent_message_observed_at_unix_ns"
                ],
                "observed_at_monotonic_ns": old_evidence[
                    "agent_message_observed_at_monotonic_ns"
                ],
            }
            evidence = {
                "response_id": call["response_id"],
                "provider_call_id": call["call_id"],
                "thread_id": "child-thread",
                "turn_id": "child-turn",
                "successor_response_id": successor["response_id"],
                "successor_call_id": successor["call_id"],
                "collaboration_messages": [message],
            }
            zero = {
                field: 0 for field in runner_module.PROVIDER_GATE_USAGE_KEYS
            }
            superseded_usage = copy.deepcopy(call["normalized_usage"])
            for target in (usage, reconciliation):
                target["suppressed_collaboration_wait_response_count"] = 0
                target["suppressed_collaboration_wait_response_ids"] = []
                target["suppressed_collaboration_wait_usage"] = copy.deepcopy(zero)
                target["suppressed_collaboration_wait_evidence"] = []
                target[
                    "superseded_by_collaboration_message_response_count"
                ] = 1
                target[
                    "superseded_by_collaboration_message_response_ids"
                ] = [call["response_id"]]
                target[
                    "superseded_by_collaboration_message_usage"
                ] = copy.deepcopy(superseded_usage)
                target[
                    "superseded_by_collaboration_message_evidence"
                ] = [copy.deepcopy(evidence)]
            usage["thread_accounting"] = [
                {
                    "thread_id": "root-thread",
                    "parent_thread_id": None,
                    "agent_path": "root",
                    "provisional": False,
                    "spawn_binding_status": "root_zero",
                },
                {
                    "thread_id": "child-thread",
                    "parent_thread_id": "root-thread",
                    "agent_path": "/root/library_search",
                    "provisional": False,
                    "spawn_binding_status": "resolved",
                },
            ]
            _seal_synthetic_gate(path, record)
            usage["provider_token_gate"]["record_sha256"] = record[
                "record_sha256"
            ]
            authenticated = authenticate_provider_gate_artifact(
                path,
                usage=usage,
                **expected,
            )
            self.assertEqual(
                authenticated["derived"][
                    "superseded_by_collaboration_message_response_ids"
                ],
                [call["response_id"]],
            )

    def test_job_1509369_complete_superseded_shapes_replay(self) -> None:
        def item(
            index: int,
            item_type: str,
            *,
            name: str | None = None,
            namespace: str | None = None,
        ) -> dict[str, object]:
            callable_item = item_type == "function_call" or item_type.endswith(
                "_call"
            )
            return {
                "index": index,
                "id": f"item-{index}-{item_type}",
                "type": item_type,
                "name": name,
                "namespace": namespace,
                "call_id": f"call-{index}-{item_type}" if callable_item else None,
                "payload_sha256": f"{index + 1:x}" * 64,
                "payload_bytes": 10 + index,
                "arguments_sha256": "a" * 64 if callable_item else None,
                "arguments_bytes": 2 if callable_item else None,
                "wait_timeout_ms": None,
            }

        shapes = {
            "message_only": [item(0, "reasoning"), item(1, "message")],
            "message_and_send_message": [
                item(0, "reasoning"),
                item(1, "message"),
                item(
                    2,
                    "function_call",
                    name="send_message",
                    namespace="collaboration",
                ),
            ],
            "job_1510008_message_superseded_wait": [
                item(0, "reasoning"),
                {
                    **item(
                        1,
                        "function_call",
                        name="wait_agent",
                        namespace="collaboration",
                    ),
                    "wait_timeout_ms": 30_000,
                },
            ],
        }
        with tempfile.TemporaryDirectory() as directory:
            for label, manifest_items in shapes.items():
                with self.subTest(shape=label):
                    path = Path(directory) / f"job-1509369-{label}.json"
                    record, usage, expected = synthetic_job_1508245_gate(path)
                    call = record["calls"][6]
                    successor = record["calls"][7]
                    call["response_output_manifest"] = {
                        "schema_version": 1,
                        "response_id": call["response_id"],
                        "output_item_count": len(manifest_items),
                        "action_capable_item_count": sum(
                            manifest_item["type"] == "function_call"
                            or str(manifest_item["type"]).endswith("_call")
                            for manifest_item in manifest_items
                        ),
                        "items": manifest_items,
                    }
                    call["appserver_delivery"]["kind"] = (
                        "superseded_by_collaboration_message"
                    )

                    reconciliation = usage["provider_usage_reconciliation"]
                    old_evidence = reconciliation[
                        "suppressed_collaboration_wait_evidence"
                    ][0]
                    evidence = {
                        "response_id": call["response_id"],
                        "provider_call_id": call["call_id"],
                        "thread_id": "root-thread",
                        "turn_id": "root-turn",
                        "successor_response_id": successor["response_id"],
                        "successor_call_id": successor["call_id"],
                        "collaboration_messages": [
                            {
                                "item_id": old_evidence[
                                    "agent_message_item_id"
                                ],
                                "item_sha256": old_evidence[
                                    "agent_message_sha256"
                                ],
                                "author": "/root/ultra_child",
                                "recipient": "/root",
                                "observed_at_unix_ns": old_evidence[
                                    "agent_message_observed_at_unix_ns"
                                ],
                                "observed_at_monotonic_ns": old_evidence[
                                    "agent_message_observed_at_monotonic_ns"
                                ],
                            }
                        ],
                    }
                    zero = {
                        field: 0
                        for field in runner_module.PROVIDER_GATE_USAGE_KEYS
                    }
                    superseded_usage = copy.deepcopy(call["normalized_usage"])
                    for target in (usage, reconciliation):
                        target[
                            "suppressed_collaboration_wait_response_count"
                        ] = 0
                        target["suppressed_collaboration_wait_response_ids"] = []
                        target["suppressed_collaboration_wait_usage"] = (
                            copy.deepcopy(zero)
                        )
                        target["suppressed_collaboration_wait_evidence"] = []
                        target[
                            "superseded_by_collaboration_message_response_count"
                        ] = 1
                        target[
                            "superseded_by_collaboration_message_response_ids"
                        ] = [call["response_id"]]
                        target[
                            "superseded_by_collaboration_message_usage"
                        ] = copy.deepcopy(superseded_usage)
                        target[
                            "superseded_by_collaboration_message_evidence"
                        ] = [copy.deepcopy(evidence)]
                    usage["thread_accounting"] = [
                        {
                            "thread_id": "root-thread",
                            "parent_thread_id": None,
                            "agent_path": "root",
                            "provisional": False,
                            "spawn_binding_status": "root_zero",
                        },
                        {
                            "thread_id": "child-thread",
                            "parent_thread_id": "root-thread",
                            "agent_path": "/root/ultra_child",
                            "provisional": False,
                            "spawn_binding_status": "resolved",
                        },
                    ]
                    _seal_synthetic_gate(path, record)
                    usage["provider_token_gate"]["record_sha256"] = record[
                        "record_sha256"
                    ]

                    authenticated = authenticate_provider_gate_artifact(
                        path,
                        usage=usage,
                        **expected,
                    )
                    self.assertEqual(
                        authenticated["derived"]
                        ["superseded_by_collaboration_message_response_ids"],
                        [call["response_id"]],
                    )

                    if label == "job_1510008_message_superseded_wait":
                        for mutation in ("timeout", "name"):
                            forged = copy.deepcopy(record)
                            forged_item = forged["calls"][6][
                                "response_output_manifest"
                            ]["items"][1]
                            if mutation == "timeout":
                                forged_item["wait_timeout_ms"] = 9_999
                            else:
                                forged_item["name"] = "send_message"
                            _seal_synthetic_gate(path, forged)
                            with self.subTest(malformed_wait=mutation), self.assertRaises(
                                BenchmarkToolError
                            ):
                                authenticate_provider_gate_artifact(
                                    path,
                                    usage=usage,
                                    **expected,
                                )

    def test_job_1509778_reactivated_explicit_child_interrupt_gate_replay(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "job-1509778.json"
            record, usage, expected = synthetic_job_1508245_gate(path)
            interrupting = record["calls"][6]
            discarded = record["calls"][7]
            arguments = '{"target":"/root/library_search"}'
            function_item = interrupting["response_output_manifest"]["items"][0]
            function_item.update(
                {
                    "type": "function_call",
                    "name": "interrupt_agent",
                    "namespace": "collaboration",
                    "arguments_sha256": hashlib.sha256(
                        arguments.encode("utf-8")
                    ).hexdigest(),
                    "arguments_bytes": len(arguments),
                    "wait_timeout_ms": None,
                }
            )
            interrupting["request_metadata"]["thread_id"] = "root-thread"
            interrupting["request_metadata"]["turn_id"] = "root-turn"
            interrupt_bind_mono = int(interrupting["commit_monotonic_ns"]) + 20
            interrupt_bind_wall = int(interrupting["commit_unix_ns"]) + 20
            interrupting["appserver_crossbind"] = {
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "event_sequence": 7,
                "normalized_usage": copy.deepcopy(interrupting["normalized_usage"]),
                "bind_unix_ns": interrupt_bind_wall,
                "bind_monotonic_ns": interrupt_bind_mono,
            }
            interrupting["appserver_delivery"] = {
                "kind": "direct_raw_response",
                "successor_call_id": None,
                "successor_response_id": None,
                "bind_unix_ns": interrupt_bind_wall,
                "bind_monotonic_ns": interrupt_bind_mono,
            }
            discarded["request_metadata"]["thread_id"] = "child-thread"
            discarded["request_metadata"]["turn_id"] = "child-turn"
            discarded["admitted_unix_ns"] = (
                int(interrupting["admitted_unix_ns"]) + 50
            )
            discarded["admitted_monotonic_ns"] = (
                int(interrupting["admitted_monotonic_ns"]) + 50
            )
            discarded["client_release_complete"] = False
            discarded["appserver_crossbind"] = None
            discarded["appserver_delivery"] = {
                "kind": "discarded_after_explicit_child_interrupt",
                "successor_call_id": interrupting["call_id"],
                "successor_response_id": interrupting["response_id"],
                "bind_unix_ns": int(discarded["commit_unix_ns"]) + 30,
                "bind_monotonic_ns": int(discarded["commit_monotonic_ns"]) + 30,
            }

            response_ledger = usage["appserver_response_ledger"]
            target_response = next(
                response
                for response in response_ledger
                if response["response_id"] == discarded["response_id"]
            )
            target_response.update(
                {
                    "response_id": interrupting["response_id"],
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "raw_response_notification_sequence": 7,
                    "raw_response_observed_at_unix_ns": interrupt_bind_wall + 10,
                    "raw_response_observed_at_monotonic_ns": interrupt_bind_mono + 10,
                    "usage": copy.deepcopy(interrupting["normalized_usage"]),
                    "provider_gate_call": interrupting,
                }
            )
            direct_calls = [
                call
                for call in record["calls"]
                if call["appserver_delivery"]["kind"] == "direct_raw_response"
            ]
            direct_calls.sort(
                key=lambda call: call["appserver_crossbind"]["event_sequence"]
            )
            fields = tuple(runner_module.PROVIDER_GATE_USAGE_KEYS)
            appserver_usage = {
                field: sum(call["normalized_usage"][field] for call in direct_calls)
                for field in fields
            }
            appserver_ids = [call["response_id"] for call in direct_calls]
            reconciliation = usage["provider_usage_reconciliation"]
            zero = {field: 0 for field in fields}
            evidence = {
                "response_id": discarded["response_id"],
                "provider_call_id": discarded["call_id"],
                "thread_id": "child-thread",
                "turn_id": "child-turn",
                "interrupting_response_id": interrupting["response_id"],
                "interrupting_provider_call_id": interrupting["call_id"],
                "interrupt_function_item_id": function_item["id"],
                "interrupt_function_call_id": function_item["call_id"],
                "interrupt_function_arguments_sha256": function_item[
                    "arguments_sha256"
                ],
                "interrupt_parent_thread_id": "root-thread",
                "interrupt_parent_turn_id": "root-turn",
                "interrupted_agent_path": "/root/library_search",
                "interrupt_activity_item_sha256": "b" * 64,
                "interrupt_output_item_id": "fco-job-1509778",
                "interrupt_output_item_sha256": "c" * 64,
                "interrupt_function_observed_at_unix_ns": 100_000,
                "interrupt_function_observed_at_monotonic_ns": 10_000,
                "interrupt_activity_observed_at_unix_ns": 200_000,
                "interrupt_activity_observed_at_monotonic_ns": 11_000,
                "interrupt_output_observed_at_unix_ns": 300_000,
                "interrupt_output_observed_at_monotonic_ns": 12_000,
                "interrupted_turn_observed_at_unix_ns": 400_000,
                "interrupted_turn_observed_at_monotonic_ns": 13_000,
            }
            for target in (usage, reconciliation):
                target["appserver_response_ids"] = copy.deepcopy(appserver_ids)
                target["appserver_usage"] = copy.deepcopy(appserver_usage)
                target["suppressed_collaboration_wait_response_count"] = 0
                target["suppressed_collaboration_wait_response_ids"] = []
                target["suppressed_collaboration_wait_usage"] = copy.deepcopy(zero)
                target["suppressed_collaboration_wait_evidence"] = []
                target[
                    "discarded_after_explicit_child_interrupt_response_count"
                ] = 1
                target[
                    "discarded_after_explicit_child_interrupt_response_ids"
                ] = [discarded["response_id"]]
                target[
                    "discarded_after_explicit_child_interrupt_usage"
                ] = copy.deepcopy(discarded["normalized_usage"])
                target[
                    "discarded_after_explicit_child_interrupt_evidence"
                ] = [copy.deepcopy(evidence)]
            usage["thread_accounting"] = [
                {
                    "thread_id": "root-thread", "parent_thread_id": None,
                    "agent_path": "root", "provisional": False,
                    "spawn_binding_status": "root_zero", "turn_status": "completed",
                    "active_turn_id": None,
                },
                {
                    "thread_id": "child-thread",
                    "parent_thread_id": "root-thread",
                    "agent_path": "/root/library_search", "provisional": False,
                    "spawn_binding_status": "resolved", "turn_status": "inProgress",
                    "active_turn_id": "child-followup-turn-1509778",
                },
            ]
            # Job 1509703 demonstrated the sound concurrent order: the parent
            # interrupt request may be admitted first while the child request
            # is admitted before that parent response commits.
            for sequence, call in enumerate(record["calls"], start=1):
                call["sequence"] = sequence
                call["call_id"] = f"provider-call-{sequence:08d}"
                call["admission_mode"] = "CONCURRENT"
            calls_by_response = {
                call["response_id"]: call for call in record["calls"]
            }
            for call in record["calls"]:
                delivery = call["appserver_delivery"]
                successor_id = delivery.get("successor_response_id")
                if successor_id is not None:
                    delivery["successor_call_id"] = calls_by_response[
                        successor_id
                    ]["call_id"]
                open_before = [
                    other
                    for other in record["calls"]
                    if other is not call
                    and other["admitted_monotonic_ns"]
                    < call["admitted_monotonic_ns"]
                    < other["commit_monotonic_ns"]
                ]
                completed_before = sum(
                    other["normalized_usage"]["total_tokens"]
                    for other in record["calls"]
                    if other["commit_monotonic_ns"]
                    < call["admitted_monotonic_ns"]
                )
                call["completed_before"] = completed_before
                call["open_before"] = len(open_before)
                call["reserved_before"] = completed_before + len(open_before) * 272_000
                call["reservation_after"] = (
                    completed_before + (len(open_before) + 1) * 272_000
                )
            evidence["provider_call_id"] = discarded["call_id"]
            evidence["interrupting_provider_call_id"] = interrupting["call_id"]
            for target in (usage, reconciliation):
                target["discarded_after_explicit_child_interrupt_evidence"] = [
                    copy.deepcopy(evidence)
                ]
            record["transitions"] = [
                {
                    "sequence": 10,
                    "from_phase": "CONCURRENT",
                    "to_phase": "CLOSED",
                    "reason": "terminal_close:natural_end",
                    "call_id": None,
                    "unix_ns": 3_013_900,
                    "monotonic_ns": 4_900,
                }
            ]
            record["state"]["sequence"] = 10
            _seal_synthetic_gate(path, record)
            usage["provider_token_gate"]["record_sha256"] = record[
                "record_sha256"
            ]
            authenticated = authenticate_provider_gate_artifact(
                path, usage=usage, **expected
            )
            self.assertEqual(
                authenticated["derived"][
                    "discarded_after_explicit_child_interrupt_response_ids"
                ],
                [discarded["response_id"]],
            )

            wrong_route = copy.deepcopy(usage)
            for target in (
                wrong_route,
                wrong_route["provider_usage_reconciliation"],
            ):
                target["discarded_after_explicit_child_interrupt_evidence"][0][
                    "interrupted_agent_path"
                ] = "/root/wrong-child"
            with self.assertRaises(BenchmarkToolError):
                authenticate_provider_gate_artifact(
                    path, usage=wrong_route, **expected
                )

            tampered_digest = copy.deepcopy(usage)
            for target in (
                tampered_digest,
                tampered_digest["provider_usage_reconciliation"],
            ):
                target["discarded_after_explicit_child_interrupt_evidence"][0][
                    "interrupt_function_arguments_sha256"
                ] = "d" * 64
            with self.assertRaises(BenchmarkToolError):
                authenticate_provider_gate_artifact(
                    path, usage=tampered_digest, **expected
                )

            bad_usage = copy.deepcopy(usage)
            bad_usage["provider_usage_reconciliation"][
                "discarded_after_explicit_child_interrupt_evidence"
            ][0]["interrupted_turn_observed_at_unix_ns"] = int(
                discarded["commit_unix_ns"]
            )
            with self.assertRaises(BenchmarkToolError):
                authenticate_provider_gate_artifact(
                    path, usage=bad_usage, **expected
                )

    def test_job_1509218_child_to_root_route_remains_authenticated(self) -> None:
        threads = {
            "root-thread": {
                "thread_id": "root-thread",
                "parent_thread_id": None,
                "agent_path": "root",
                "provisional": False,
                "spawn_binding_status": "root_zero",
            },
            "child-thread": {
                "thread_id": "child-thread",
                "parent_thread_id": "root-thread",
                "agent_path": "/root/worker",
                "provisional": False,
                "spawn_binding_status": "resolved",
            },
        }
        self.assertTrue(
            runner_module._rooted_collaboration_route_matches(
                thread_id="root-thread",
                author="/root/worker",
                recipient="/root",
                projected_threads=threads,
                root_thread_id="root-thread",
            )
        )

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.base = self.root / "base"
        self.base.mkdir()
        (self.base / "README.txt").write_text("minimal Lean workspace\n", encoding="utf-8")
        self.task = self.root / "task-source"
        self.task.mkdir()
        (self.task / "Canonical.lean").write_text(SIGNATURE, encoding="utf-8")
        self.manifest = self.root / "controlled.json"
        write_json(self.manifest, create_manifest(self.task))

        self.usage_helper = self.root / "trusted_usage.py"
        self.usage_helper.write_text(
            "from pathlib import Path\n"
            "import hashlib, json, os, time\n"
            "def _canonical_hash(value, field):\n"
            "  unsigned = {k:v for k,v in value.items() if k != field}\n"
            "  data = json.dumps(unsigned,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()\n"
            "  return hashlib.sha256(data).hexdigest()\n"
            "def _publish(path, value, field):\n"
            "  value = dict(value); value[field] = _canonical_hash(value, field)\n"
            "  payload = json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\\n'\n"
            "  path = Path(path); temporary = path.with_name('.'+path.name+'.test.tmp')\n"
            "  temporary.write_text(payload); os.replace(temporary,path); return value\n"
            "def prompt_handshake(prompt, root_thread_id='root', release_delay=0.0, release_shift_ns=0, omit_release=False, tamper_release=False):\n"
            "  expected = os.environ.get('HIGHAMBENCH_PROMPT_EFFECTIVE_SHA256','')\n"
            "  if not expected: return None\n"
            "  encoded = prompt.encode(); assert hashlib.sha256(encoded).hexdigest() == expected\n"
            "  common = {\n"
            "    'schema_version':1,'protocol_version':'highambench-prompt-release-v1',\n"
            "    'handshake_nonce':os.environ['HIGHAMBENCH_PROMPT_HANDSHAKE_NONCE'],\n"
            "    'run_id':os.environ['HIGHAMBENCH_PROMPT_RUN_ID'],\n"
            "    'condition':os.environ['HIGHAMBENCH_CONDITION'],\n"
            "    'model':os.environ['HIGHAMBENCH_MODEL'],\n"
            "    'reasoning_effort':os.environ['HIGHAMBENCH_REASONING_EFFORT'],\n"
            "    'root_thread_id':root_thread_id,'turn_start_request_id':3,\n"
            "    'effective_prompt_sha256':expected,'effective_prompt_bytes':len(encoded),\n"
            "    'adapter_name':'codex_isolated.py','adapter_version':'1',\n"
            "    'app_server_client_name':'highambench-isolated','app_server_client_version':'1',\n"
            "    'elapsed_clock':'CLOCK_MONOTONIC',\n"
            "  }\n"
            "  ready_mono=time.monotonic_ns(); ready_wall=time.time_ns()\n"
            "  ready=_publish(os.environ['HIGHAMBENCH_PROMPT_READY_OUTPUT'],{**common,\n"
            "    'kind':'highambench_prompt_ready','turn_start_write_state':'not_started',\n"
            "    'ready_at_monotonic_ns':ready_mono,'ready_at_unix_ns':ready_wall},'ready_sha256')\n"
            "  go_path=Path(os.environ['HIGHAMBENCH_PROMPT_GO_INPUT'])\n"
            "  deadline=time.monotonic()+2\n"
            "  while not go_path.exists():\n"
            "    if time.monotonic()>=deadline: raise RuntimeError('GO timeout')\n"
            "    time.sleep(.002)\n"
            "  go=json.loads(go_path.read_text())\n"
            "  assert _canonical_hash(go,'go_sha256') == go['go_sha256']\n"
            "  if omit_release: return None\n"
            "  if release_delay: time.sleep(release_delay)\n"
            "  request={'id':3,'method':'turn/start','params':{'approvalPolicy':'never','cwd':'/workspace',\n"
            "    'effort':common['reasoning_effort'],'input':[{'type':'text','text':prompt}],\n"
            "    'model':common['model'],'sandboxPolicy':{'type':'dangerFullAccess'},'threadId':root_thread_id}}\n"
            "  wire=(json.dumps(request,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\\n').encode()\n"
            "  released=time.monotonic_ns()+release_shift_ns; released_wall=time.time_ns()\n"
            "  flushed=max(time.monotonic_ns(),released); flushed_wall=max(time.time_ns(),released_wall)\n"
            "  result=_publish(os.environ['HIGHAMBENCH_PROMPT_RELEASE_OUTPUT'],{**common,\n"
            "    'kind':'highambench_prompt_released','ready_sha256':ready['ready_sha256'],\n"
            "    'go_sha256':go['go_sha256'],'turn_start_write_state':'flushed',\n"
            "    'timestamp_capture_point':'immediately_before_turn_start_write',\n"
            "    'turn_start_request_sha256':hashlib.sha256(wire).hexdigest(),\n"
            "    'turn_start_request_bytes':len(wire),'released_at_monotonic_ns':released,\n"
            "    'released_at_unix_ns':released_wall,'turn_start_flushed_at_monotonic_ns':flushed,\n"
            "    'turn_start_flushed_at_unix_ns':flushed_wall},'release_sha256')\n"
            "  if tamper_release:\n"
            "    damaged=dict(result); damaged['effective_prompt_bytes'] += 1\n"
            "    Path(os.environ['HIGHAMBENCH_PROMPT_RELEASE_OUTPUT']).write_text(json.dumps(damaged,sort_keys=True,separators=(',',':'))+'\\n')\n"
            "  return result\n"
            "def emit(path, sequence, input_tokens, cached_tokens, output_tokens):\n"
            "  value = {\n"
            f"    'measurement_source': {TOKEN_USAGE_MEASUREMENT_SOURCE!r},\n"
            "    'live_cumulative': True, 'input_includes_cached': True,\n"
            "    'notification_sequence': sequence,\n"
            "    'observed_at_unix_ns': time.time_ns(),\n"
            "    'input_tokens': input_tokens,\n"
            "    'cached_input_tokens': cached_tokens,\n"
            "    'output_tokens': output_tokens,\n"
            "  }\n"
            "  path = Path(path)\n"
            "  path.parent.mkdir(parents=True, exist_ok=True)\n"
            "  temporary = path.with_suffix(path.suffix + '.tmp')\n"
            "  temporary.write_text(json.dumps(value))\n"
            "  os.replace(temporary, path)\n"
            "def emit_ultra(path, sequence, input_tokens, cached_tokens, "
            "output_tokens, exact, crossing=None):\n"
            "  total = input_tokens + output_tokens\n"
            "  response_ids = [f'r{index}' for index in range(1, sequence + 1)]\n"
            "  zero = {'input_tokens':0,'cached_input_tokens':0,'cache_write_input_tokens':0,"
            "'output_tokens':0,'reasoning_output_tokens':0,'total_tokens':0}\n"
            "  projection = {'input_tokens':input_tokens,'cached_input_tokens':cached_tokens,"
            "'cache_write_input_tokens':0,'output_tokens':output_tokens,"
            "'reasoning_output_tokens':0,'total_tokens':total}\n"
            "  thread = {\n"
            "    'thread_id': 'root', 'parent_thread_id': None, 'provisional': False,\n"
            "    'spawn_call_id':None,'spawn_parent_turn_id':None,'spawn_parent_response_id':None,\n"
            "    'spawn_fork_turns':None,'spawn_fork_semantics':None,'spawn_binding_status':'root_zero',\n"
            "    'response_count': sequence, 'input_tokens': input_tokens,\n"
            "    'cached_input_tokens': cached_tokens, 'cache_write_input_tokens': 0,\n"
            "    'output_tokens': output_tokens, 'reasoning_output_tokens': 0,\n"
            "    'total_tokens': total,'cumulative_baseline':zero,\n"
            "    'expected_cumulative_baseline':zero,'last_cumulative':projection,\n"
            "    'cumulative_observation_count':1,'expected_cumulative_projection':projection,\n"
            "    'full_cumulative_projection':projection,\n"
            "    'cumulative_projection_exempt_response_id':None,\n"
            "    'cumulative_projection_exempt_response_usage':None,\n"
            "    'observed_cumulative_baseline':zero,'cumulative_baseline_matches_expected':True,\n"
            "    'cumulative_projection_match':True,'cumulative_projection_status':'matched_full_projection',\n"
            "    'accounting_complete':True,\n"
            "  }\n"
            "  value = {\n"
            "    'schema_version':1,'accounting_projection_schema_version':"
            f"{ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION},\n"
            f"    'measurement_source': {ULTRA_USAGE_MEASUREMENT_SOURCE!r},\n"
            f"    'notification': {ULTRA_USAGE_NOTIFICATION!r},\n"
            f"    'usage_scope': {ULTRA_USAGE_SCOPE!r},\n"
            "    'live_cumulative': True, 'input_includes_cached': True,\n"
            "    'root_thread_id': 'root', 'thread_count': 1,\n"
            "    'response_count': sequence, 'notification_sequence': sequence,\n"
            "    'observed_at_unix_ns': time.time_ns(),\n"
            "    'input_tokens': input_tokens, 'cached_input_tokens': cached_tokens,\n"
            "    'cache_write_input_tokens': 0, 'output_tokens': output_tokens,\n"
            "    'reasoning_output_tokens': 0, 'total_tokens': total,\n"
            "    'drain_complete': exact, 'measurement_exact': exact,\n"
            "    'first_crossing': ({'tokens': crossing} if crossing is not None else None),\n"
            "    'stop_reason': ('token_limit' if crossing is not None else None),\n"
            "    'interrupt_requested': False,\n"
            "    'active_thread_ids': ([] if exact else ['root']),\n"
            "    'unresolved_thread_ids': [], 'invalid_reasons': [],\n"
            "    'spawn_binding_source':'raw_function_call.call_id=subAgentActivity.id',\n"
            "    'raw_spawn_call_ids':[],'activity_spawn_call_ids':[],'collab_spawn_call_ids':[],\n"
            "    'resolved_spawn_call_ids':[],'failed_spawn_call_ids':[],\n"
            "    'unresolved_spawn_call_ids':[],'unsupported_spawn_call_ids':[],\n"
            "    'inference_child_thread_ids':[],'spawn_linkage_complete':True,\n"
            "    'descendant_accounting_complete':True,'cumulative_projection_complete':True,\n"
            "    'accounting_complete':True,\n"
            f"    **{ultra_fork_policy_fields()!r},\n"
            "    'threads': [thread], 'response_ids': response_ids,\n"
            "  }\n"
            "  path = Path(path)\n"
            "  path.parent.mkdir(parents=True, exist_ok=True)\n"
            "  temporary = path.with_suffix(path.suffix + '.tmp')\n"
            "  temporary.write_text(json.dumps(value))\n"
            "  os.replace(temporary, path)\n",
            encoding="utf-8",
        )

        self.agent = self.root / "agent.py"
        self.agent.write_text(
            "from pathlib import Path\n"
            "import os, sys, time\n"
            "from trusted_usage import emit, prompt_handshake\n"
            "if os.environ.get('HIGHAMBENCH_PROMPT_EFFECTIVE_SHA256'):\n"
            "  def option(name): return sys.argv[sys.argv.index(name)+1]\n"
            "  sections=[Path(option('--prompt-file')).read_text().rstrip()]\n"
            "  if '--condition-prompt-file' in sys.argv: sections.append(Path(option('--condition-prompt-file')).read_text().rstrip())\n"
            "  sections += ['## Task context\\n\\n'+Path(option('--context-file')).read_text().rstrip(),\n"
            "    '## Fixed Lean target\\n\\n```lean\\n'+Path(option('--target-file')).read_text().rstrip()+'\\n```']\n"
            "  prompt_handshake('\\n\\n'.join(sections)+'\\n')\n"
            "emit(sys.argv[2], 1, 20, 5, 5)\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(0.05)\n"
            "emit(sys.argv[2], 2, 30, 10, 12)\n",
            encoding="utf-8",
        )
        self.compiler = self.root / "compiler.py"
        self.compiler.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "source = Path(sys.argv[1])\n"
            "text = source.read_text()\n"
            "if source.name.startswith('HighamBenchChecked_'):\n"
            "  assert '#check target' in text\n"
            "Path(sys.argv[2]).write_bytes(b'fake olean')\n"
            "print('axioms: []')\n",
            encoding="utf-8",
        )
        self.probe = self.root / "probe.py"
        self.probe.write_text(
            "print(\"error: unknown module prefix 'NumStability'\")\n"
            "raise SystemExit(1)\n",
            encoding="utf-8",
        )
        self.audit = self.root / "audit.py"
        self.audit.write_text(
            "import sys\n"
            "candidate, expected, condition = sys.argv[1:]\n"
            "print('format\\t2')\n"
            "print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "print(f'target\\t{candidate}\\tHighamBenchChecked')\n"
            "if condition == 'L':\n"
            "  print('library\\tNumStability.reused\\tNumStability.Basic\\t1')\n"
            "print('visited\\t2')\n"
            "print(f'summary\\t{1 if condition == \"L\" else 0}\\t0')\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def assert_legacy_ungated_ultra_rejected(self, result: dict[str, object]) -> None:
        """Old fake Ultra agents are intentionally invalid under the gate contract."""

        self.assertFalse(result["pass"], result)
        self.assertFalse(result["scored"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR", result)
        self.assertIn("--codex", str(result["failure_note"]))
        gate = result["provider_token_gate"]
        self.assertTrue(gate["required"])
        self.assertFalse(gate["final"]["scoreable"])

    def test_provider_gate_exact_natural_token_limit_is_scoreable_evidence(self) -> None:
        gate_path = (self.root / "exact.provider-token-gate.json").resolve()
        record, usage, expected = synthetic_provider_gate(gate_path)
        authenticated = authenticate_provider_gate_artifact(
            gate_path, usage=usage, **expected
        )
        self.assertTrue(authenticated["authenticated"])
        self.assertEqual(authenticated["derived"]["completed_tokens"], 10_500)
        self.assertEqual(
            authenticated["record"]["calls"][0]["admission_mode"], "EXCLUSIVE"
        )
        self.assertGreaterEqual(
            authenticated["record"]["configuration"]["response_bound"],
            authenticated["record"]["configuration"]["token_limit"],
        )
        self.assertEqual(
            authenticated["derived"]["first_crossing"]["response_id"],
            "resp-fixture-1",
        )
        validate_provider_gate_outcome(
            authenticated,
            token_limited=True,
            accepted_request=None,
        )
        # The crossing body is a single minimal completion and carries no model
        # output or action-bearing record.
        sanitized = record["calls"][0]["released_sanitized_event"]
        self.assertEqual(sanitized["response"]["output"], [])
        self.assertEqual(
            set(sanitized["response"]), {"id", "usage", "end_turn", "output"}
        )

    def test_provider_gate_exact_compaction_crossing_is_scoreable_evidence(self) -> None:
        gate_path = (self.root / "compaction.provider-token-gate.json").resolve()
        record, usage, expected = synthetic_provider_gate(
            gate_path, request_kind="compaction"
        )
        authenticated = authenticate_provider_gate_artifact(
            gate_path, usage=usage, **expected
        )
        crossing = authenticated["derived"]["first_crossing"]
        self.assertEqual(crossing["request_kind"], "compaction")
        self.assertEqual(
            crossing["release_kind"],
            "sanitized_compaction_crossing_completion",
        )
        events = record["calls"][0]["released_sanitized_events"]
        self.assertEqual(
            [event["type"] for event in events],
            ["response.output_item.done", "response.completed"],
        )
        self.assertEqual(
            events[0]["item"],
            {
                "type": "compaction",
                "encrypted_content": "opaque-compaction-fixture",
            },
        )
        self.assertEqual(events[1]["response"]["output"], [])
        validate_provider_gate_outcome(
            authenticated,
            token_limited=True,
            accepted_request=None,
        )

    def test_provider_gate_exact_missing_response_headers_are_authenticated(self) -> None:
        for request_kind in ("turn", "compaction"):
            with self.subTest(request_kind=request_kind):
                gate_path = (
                    self.root
                    / f"missing-headers-{request_kind}.provider-token-gate.json"
                ).resolve()
                record, usage, expected = synthetic_provider_gate(
                    gate_path,
                    request_kind=request_kind,
                    content_type_present=False,
                    content_encoding_present=False,
                )
                authenticated = authenticate_provider_gate_artifact(
                    gate_path,
                    usage=usage,
                    **expected,
                )
                call = authenticated["record"]["calls"][0]
                self.assertIsNone(call["upstream_content_type"])
                self.assertEqual(call["upstream_content_type_occurrences"], 0)
                self.assertIsNone(call["upstream_content_encoding"])
                self.assertEqual(call["upstream_content_encoding_occurrences"], 0)
                receipt = call["upstream_sse_authentication"]
                self.assertEqual(
                    receipt["content_type_basis"],
                    "authenticated_stream_request_header_absent",
                )
                self.assertEqual(
                    receipt["content_encoding_basis"],
                    "implicit_identity_header_absent",
                )
                self.assertTrue(receipt["downstream_content_type_synthesized"])
                self.assertEqual(
                    receipt["completed_event_index"],
                    receipt["json_event_count"] - 1,
                )
                self.assertEqual(receipt["body_sha256"], call["upstream_body_sha256"])
                self.assertEqual(receipt["body_bytes"], call["upstream_body_bytes"])
                self.assertEqual(receipt["response_id"], call["response_id"])
                validate_provider_gate_outcome(
                    authenticated,
                    token_limited=True,
                    accepted_request=None,
                )

    def test_provider_gate_denied_model_catalog_allows_empty_metadata_only(self) -> None:
        def append_denial(
            record: dict[str, object], *, method: str, route: str
        ) -> None:
            record["denials"].append(
                {
                    "sequence": 6,
                    "denial_id": "deny-00000006",
                    "method": method,
                    "route": route,
                    "reason": "unknown_or_disallowed_route",
                    "phase": "CLOSED",
                    "upstream_started": False,
                    "unix_ns": 10_650,
                    "monotonic_ns": 1_650,
                    "request_metadata": {
                        name: None
                        for name in runner_module.PROVIDER_GATE_REQUEST_METADATA_KEYS
                    },
                }
            )
            record["state"]["sequence"] = 6

        catalog_path = (self.root / "denied-models.provider-token-gate.json").resolve()
        catalog_record, catalog_usage, catalog_expected = synthetic_provider_gate(
            catalog_path
        )
        append_denial(catalog_record, method="GET", route="/models")
        _seal_synthetic_gate(catalog_path, catalog_record)
        catalog_usage["provider_token_gate"]["record_sha256"] = catalog_record[
            "record_sha256"
        ]
        authenticated = authenticate_provider_gate_artifact(
            catalog_path,
            usage=catalog_usage,
            **catalog_expected,
        )
        self.assertEqual(
            authenticated["record"]["denials"][0]["request_metadata"],
            {
                name: None
                for name in runner_module.PROVIDER_GATE_REQUEST_METADATA_KEYS
            },
        )

        inference_path = (
            self.root / "denied-responses-empty-metadata.provider-token-gate.json"
        ).resolve()
        inference_record, inference_usage, inference_expected = synthetic_provider_gate(
            inference_path
        )
        append_denial(inference_record, method="POST", route="/responses")
        _seal_synthetic_gate(inference_path, inference_record)
        inference_usage["provider_token_gate"]["record_sha256"] = inference_record[
            "record_sha256"
        ]
        with self.assertRaisesRegex(
            BenchmarkToolError,
            r"denials\[0\]\.request_metadata\.thread_id must be a nonempty string",
        ):
            authenticate_provider_gate_artifact(
                inference_path,
                usage=inference_usage,
                **inference_expected,
            )

    def test_provider_gate_adversarial_artifacts_fail_closed(self) -> None:
        def reject(
            label: str,
            mutate: object,
            *,
            close_reason: str = "token_limit",
            request_kind: str = "turn",
        ) -> None:
            with self.subTest(label=label):
                gate_path = (self.root / f"{label}.provider-token-gate.json").resolve()
                record, _usage, expected = synthetic_provider_gate(
                    gate_path,
                    close_reason=close_reason,
                    request_kind=request_kind,
                )
                assert callable(mutate)
                mutate(record)
                _seal_synthetic_gate(gate_path, record)
                with self.assertRaises(BenchmarkToolError):
                    authenticate_provider_gate_artifact(
                        gate_path, usage=None, **expected
                    )

        missing = (self.root / "missing.provider-token-gate.json").resolve()
        with self.assertRaises(BenchmarkToolError):
            authenticate_provider_gate_artifact(
                missing,
                usage=None,
                token_limit=10_000,
                run_id="fixture-run",
                model="gpt-5.6-sol",
                reasoning_effort="ultra",
                root_thread_id="root-thread",
                prompt_release_sha256="4" * 64,
                prompt_release_protocol="highambench-prompt-release-v1",
                prompt_sha256="5" * 64,
                model_catalog_sha256="2" * 64,
                model_entry_sha256="3" * 64,
                expected_transport_provenance=synthetic_provider_transport(),
                expected_source_sha256="1" * 64,
            )

        mode_path = (self.root / "mode.provider-token-gate.json").resolve()
        _record, _usage, mode_expected = synthetic_provider_gate(mode_path)
        mode_path.chmod(0o600)
        with self.assertRaisesRegex(BenchmarkToolError, "0444"):
            authenticate_provider_gate_artifact(
                mode_path, usage=None, **mode_expected
            )

        tamper_path = (self.root / "tamper.provider-token-gate.json").resolve()
        _record, _usage, tamper_expected = synthetic_provider_gate(tamper_path)
        tamper_path.chmod(0o600)
        tamper_path.write_bytes(tamper_path.read_bytes() + b" ")
        tamper_path.chmod(0o444)
        with self.assertRaises(BenchmarkToolError):
            authenticate_provider_gate_artifact(
                tamper_path, usage=None, **tamper_expected
            )

        reject(
            "resealed-retry",
            lambda value: value["configuration"].__setitem__("request_retries", 1),
        )
        reject(
            "crossing-policy-reseal",
            lambda value: value["configuration"].__setitem__(
                "crossing_release_policy", "release_all_output"
            ),
        )
        reject(
            "counted-request-kind-reseal",
            lambda value: value["configuration"].__setitem__(
                "counted_request_kinds", ["turn", "summary"]
            ),
        )
        reject(
            "transport-test-override",
            lambda value: value["configuration"]["transport_provenance"].__setitem__(
                "connection_factory_mode", "test_override"
            ),
        )
        reject(
            "transport-dependency-reseal",
            lambda value: value["configuration"]["transport_provenance"]["tls"][
                "certificate_source"
            ].__setitem__("sha256", "9" * 64),
        )
        reject(
            "schema-bool",
            lambda value: value.__setitem__("schema_version", True),
        )
        reject(
            "legacy-schema-v2",
            lambda value: value.__setitem__("schema_version", 2),
        )
        reject(
            "legacy-protocol-v2",
            lambda value: value.__setitem__(
                "protocol", "highambench-provider-token-gate-v2"
            ),
        )
        reject(
            "legacy-implementation-v2",
            lambda value: value["implementation"].__setitem__("version", "2"),
        )
        reject(
            "sse-contract-parser",
            lambda value: value["configuration"][
                "upstream_response_contract"
            ].__setitem__("parser", "permissive-sse"),
        )
        reject(
            "stale-sse-contract-parser-v1",
            lambda value: value["configuration"][
                "upstream_response_contract"
            ].__setitem__("parser", "highambench-strict-responses-sse-v1"),
        )
        reject(
            "sse-contract-extra",
            lambda value: value["configuration"][
                "upstream_response_contract"
            ].__setitem__("fallback", True),
        )
        reject(
            "content-type-occurrences-bool",
            lambda value: value["calls"][0].__setitem__(
                "upstream_content_type_occurrences", True
            ),
        )
        reject(
            "content-type-duplicate",
            lambda value: value["calls"][0].__setitem__(
                "upstream_content_type_occurrences", 2
            ),
        )
        reject(
            "content-type-empty",
            lambda value: value["calls"][0].__setitem__(
                "upstream_content_type", ""
            ),
        )
        reject(
            "content-type-wrong",
            lambda value: value["calls"][0].__setitem__(
                "upstream_content_type", "application/json"
            ),
        )
        reject(
            "content-encoding-duplicate",
            lambda value: value["calls"][0].__setitem__(
                "upstream_content_encoding_occurrences", 2
            ),
        )
        reject(
            "content-encoding-wrong",
            lambda value: value["calls"][0].__setitem__(
                "upstream_content_encoding", "gzip"
            ),
        )
        reject(
            "missing-sse-authentication",
            lambda value: value["calls"][0].__setitem__(
                "upstream_sse_authentication", None
            ),
        )
        reject(
            "sse-authentication-extra",
            lambda value: value["calls"][0][
                "upstream_sse_authentication"
            ].__setitem__("fallback", True),
        )
        reject(
            "sse-authentication-parser",
            lambda value: value["calls"][0][
                "upstream_sse_authentication"
            ].__setitem__("parser", "permissive-sse"),
        )
        reject(
            "stale-sse-authentication-parser-v1",
            lambda value: value["calls"][0][
                "upstream_sse_authentication"
            ].__setitem__("parser", "highambench-strict-responses-sse-v1"),
        )
        reject(
            "sse-authentication-body",
            lambda value: value["calls"][0][
                "upstream_sse_authentication"
            ].__setitem__("body_sha256", "9" * 64),
        )
        reject(
            "sse-authentication-post-terminal-event",
            lambda value: value["calls"][0][
                "upstream_sse_authentication"
            ].__setitem__("json_event_count", 2),
        )
        reject(
            "retry-bool",
            lambda value: value["configuration"].__setitem__(
                "request_retries", False
            ),
        )
        reject(
            "bound-float",
            lambda value: value["configuration"].__setitem__(
                "response_bound", 272_000.0
            ),
        )
        reject(
            "handler-bool",
            lambda value: value["state"].__setitem__(
                "active_handler_count", False
            ),
        )
        reject(
            "upstream-int-bool",
            lambda value: value["calls"][0].__setitem__("upstream_started", 1),
        )
        reject(
            "crossing-total-float",
            lambda value: value["state"]["crossing"].__setitem__(
                "completed_tokens", 10_500.0
            ),
        )
        reject(
            "bool-as-int",
            lambda value: value["calls"][0].__setitem__("request_bytes", True),
        )
        reject(
            "duplicate-response-id",
            lambda value: value["calls"].append(copy.deepcopy(value["calls"][0])),
        )
        reject(
            "unknown-route",
            lambda value: value["calls"][0].__setitem__("route", "/responses/compact"),
        )
        reject(
            "disconnect",
            lambda value: value["calls"][0].__setitem__("upstream_started", False),
        )
        reject(
            "unknown-request-kind",
            lambda value: value["calls"][0]["request_metadata"].__setitem__(
                "request_kind", "summary"
            ),
        )
        reject(
            "empty-request-metadata",
            lambda value: value["calls"][0]["request_metadata"].__setitem__(
                "installation_id", ""
            ),
        )
        reject(
            "illegal-phase-edge",
            lambda value: value["transitions"][0].update(
                {
                    "to_phase": "EXCLUSIVE",
                    "reason": "concurrent_requests_drained",
                }
            ),
        )

        def exceed_bound(value: dict[str, object]) -> None:
            call = value["calls"][0]
            normalized = call["normalized_usage"]
            normalized.update(
                {
                    "input_tokens": 272_001,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 0,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 272_001,
                }
            )
            call["usage"] = {
                "input_tokens": 272_001,
                "output_tokens": 0,
                "total_tokens": 272_001,
            }

        reject("response-bound", exceed_bound)

        def add_action(value: dict[str, object]) -> None:
            call = value["calls"][0]
            event = call["released_sanitized_event"]
            event["response"]["output"] = [
                {"type": "function_call", "name": "submit_proof"}
            ]
            body = (
                "event: response.completed\n"
                "data: "
                + json.dumps(
                    event,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                + "\n\n"
            )
            call["released_sanitized_body_utf8"] = body
            call["released_body_sha256"] = hashlib.sha256(body.encode()).hexdigest()
            call["released_body_bytes"] = len(body.encode())

        reject("crossing-tool-release", add_action)

        reject(
            "ordinary-sanitized-events-missing",
            lambda value: value["calls"][0].__setitem__(
                "released_sanitized_events", None
            ),
        )

        def reseal_sanitized_wire(value: dict[str, object]) -> None:
            call = value["calls"][0]
            events = call["released_sanitized_events"]
            body = "".join(
                "event: "
                + event["type"]
                + "\ndata: "
                + json.dumps(
                    event,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                + "\n\n"
                for event in events
            )
            call["released_sanitized_body_utf8"] = body
            call["released_body_sha256"] = hashlib.sha256(body.encode()).hexdigest()
            call["released_body_bytes"] = len(body.encode())

        def add_compaction_frame(value: dict[str, object]) -> None:
            events = value["calls"][0]["released_sanitized_events"]
            events.insert(1, copy.deepcopy(events[0]))
            reseal_sanitized_wire(value)

        reject(
            "compaction-extra-output-frame",
            add_compaction_frame,
            request_kind="compaction",
        )

        def add_compaction_action_field(value: dict[str, object]) -> None:
            event = value["calls"][0]["released_sanitized_events"][0]
            event["item"]["name"] = "exec"
            reseal_sanitized_wire(value)

        reject(
            "compaction-action-field",
            add_compaction_action_field,
            request_kind="compaction",
        )
        reject(
            "compaction-release-kind-mismatch",
            lambda value: value["calls"][0].__setitem__(
                "release_kind", "sanitized_crossing_completion"
            ),
            request_kind="compaction",
        )
        reject(
            "compaction-crossing-kind-bool",
            lambda value: value["state"]["crossing"].__setitem__(
                "request_kind", True
            ),
            request_kind="compaction",
        )

        def add_setup(value: dict[str, object]) -> None:
            value["setup_requests"].append(
                {
                    "sequence": 6,
                    "method": "GET",
                    "route": "/models",
                    "unix_ns": 10_650,
                    "monotonic_ns": 1_650,
                    "upstream_started": True,
                    "upstream_status": 200,
                    "response_sha256": "6" * 64,
                    "response_bytes": 10,
                    "error": None,
                }
            )
            value["state"]["sequence"] = 6

        reject("setup-forward", add_setup)

        def add_bad_denial(value: dict[str, object]) -> None:
            value["denials"].append(
                {
                    "sequence": 6,
                    "denial_id": "deny-00000006",
                    "method": "POST",
                    "route": "/responses",
                    "reason": "provider_gate_closed",
                    "phase": "CLOSED",
                    "upstream_started": True,
                    "unix_ns": 10_650,
                    "monotonic_ns": 1_650,
                    "request_metadata": copy.deepcopy(
                        value["calls"][0]["request_metadata"]
                    ),
                }
            )
            value["state"]["sequence"] = 6

        reject("denial-upstream-started", add_bad_denial)

        def add_postcap_admission(value: dict[str, object]) -> None:
            postcap = copy.deepcopy(value["calls"][0])
            postcap.update(
                {
                    "sequence": 6,
                    "call_id": "provider-call-00000006",
                    "response_id": "resp-postcap",
                    "admitted_unix_ns": 10_650,
                    "admitted_monotonic_ns": 1_650,
                    "upstream_start_unix_ns": 10_660,
                    "upstream_start_monotonic_ns": 1_660,
                    "commit_unix_ns": 10_670,
                    "commit_monotonic_ns": 1_670,
                    "previous_total": 10_500,
                    "committed_total": 10_501,
                    "completed_before": 10_500,
                    "crossed_cap": False,
                    "release_kind": "byte_identity",
                    "released_sanitized_event": None,
                    "released_sanitized_events": None,
                    "released_sanitized_body_utf8": None,
                }
            )
            postcap["normalized_usage"] = {
                "input_tokens": 1,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 1,
            }
            postcap["usage"] = {
                "input_tokens": 1,
                "output_tokens": 0,
                "total_tokens": 1,
            }
            postcap["released_body_sha256"] = postcap["upstream_body_sha256"]
            postcap["released_body_bytes"] = postcap["upstream_body_bytes"]
            postcap["appserver_crossbind"].update(
                {
                    "event_sequence": 2,
                    "normalized_usage": copy.deepcopy(postcap["normalized_usage"]),
                    "bind_unix_ns": 10_680,
                    "bind_monotonic_ns": 1_680,
                }
            )
            value["calls"].append(postcap)
            value["state"]["sequence"] = 6
            value["state"]["completed_tokens"] = 10_501

        reject("postcap-admission", add_postcap_admission)

        reject(
            "post-close-upstream",
            lambda value: (
                value["calls"][0].__setitem__("upstream_start_monotonic_ns", 1_600),
                value["calls"][0].__setitem__("upstream_start_unix_ns", 10_600),
                value["calls"][0].__setitem__("commit_monotonic_ns", 1_650),
                value["calls"][0].__setitem__("commit_unix_ns", 10_650),
                value["calls"][0]["appserver_crossbind"].__setitem__(
                    "bind_monotonic_ns", 1_660
                ),
                value["calls"][0]["appserver_crossbind"].__setitem__(
                    "bind_unix_ns", 10_660
                ),
            ),
            close_reason="natural_end",
        )

    def test_provider_gate_proof_and_crossing_race_order_is_exact(self) -> None:
        accepted_path = (self.root / "accepted.provider-token-gate.json").resolve()
        _record, accepted_usage, accepted_expected = synthetic_provider_gate(
            accepted_path, close_reason="accepted_submission"
        )
        accepted = authenticate_provider_gate_artifact(
            accepted_path, usage=accepted_usage, **accepted_expected
        )
        boundary = {
            "response_id": "resp-fixture-1",
            "request_published_at_monotonic_ns": 1_580,
            "request_published_at_unix_ns": 10_580,
            "raw_response_notification_sequence": 1,
            "provider_gate_close": {
                "won": True,
                "requested_reason": "accepted_submission",
                "effective_reason": "accepted_submission",
                "phase": "CLOSED",
                "sequence": 4,
            },
        }
        validate_provider_gate_outcome(
            accepted,
            token_limited=False,
            accepted_request=boundary,
        )
        too_late = copy.deepcopy(boundary)
        too_late["request_published_at_monotonic_ns"] = 1_600
        with self.assertRaises(BenchmarkToolError):
            validate_provider_gate_outcome(
                accepted,
                token_limited=False,
                accepted_request=too_late,
            )
        before_commit = copy.deepcopy(boundary)
        before_commit["request_published_at_monotonic_ns"] = 1_450
        with self.assertRaises(BenchmarkToolError):
            validate_provider_gate_outcome(
                accepted,
                token_limited=False,
                accepted_request=before_commit,
            )
        unix_before_commit = copy.deepcopy(boundary)
        unix_before_commit["request_published_at_unix_ns"] = 10_450
        with self.assertRaises(BenchmarkToolError):
            validate_provider_gate_outcome(
                accepted,
                token_limited=False,
                accepted_request=unix_before_commit,
            )

        crossing_path = (self.root / "crossing-race.provider-token-gate.json").resolve()
        _record, crossing_usage, crossing_expected = synthetic_provider_gate(
            crossing_path
        )
        crossing = authenticate_provider_gate_artifact(
            crossing_path, usage=crossing_usage, **crossing_expected
        )
        with self.assertRaises(BenchmarkToolError):
            validate_provider_gate_outcome(
                crossing,
                token_limited=True,
                accepted_request=boundary,
            )

        natural_path = (self.root / "natural.provider-token-gate.json").resolve()
        _record, natural_usage, natural_expected = synthetic_provider_gate(
            natural_path, close_reason="natural_end"
        )
        natural = authenticate_provider_gate_artifact(
            natural_path, usage=natural_usage, **natural_expected
        )
        validate_provider_gate_outcome(
            natural,
            token_limited=False,
            accepted_request=None,
            natural_end=True,
        )

    def test_provider_gate_crossing_is_exact_with_active_incomplete_tree(self) -> None:
        for request_kind in ("turn", "compaction"):
            with self.subTest(request_kind=request_kind):
                gate_path = (
                    self.root
                    / f"active-{request_kind}.provider-token-gate.json"
                ).resolve()
                raw = active_tree_provider_crossing_usage(
                    gate_path, request_kind=request_kind
                )
                usage_path = self.root / f"active-{request_kind}.usage.json"
                write_json(usage_path, raw)

                usage = read_token_usage(usage_path)
                assert usage is not None
                self.assertTrue(usage["measurement_exact"])
                self.assertFalse(usage["drain_complete"])
                self.assertFalse(usage["tree_quiescent"])
                self.assertFalse(usage["accounting_complete"])
                self.assertEqual(usage["active_thread_ids"], ["root-thread"])
                self.assertEqual(usage["root_turn_id"], "root-turn")
                first_crossing = usage["first_crossing"]
                assert isinstance(first_crossing, Mapping)
                if request_kind == "compaction":
                    self.assertEqual(usage["response_count"], 2)
                    self.assertEqual(
                        [
                            response["turn_id"]
                            for response in usage["response_ledger"]
                        ],
                        ["root-turn", "compaction-turn"],
                    )
                    root_projection = usage["thread_accounting"][0]
                    self.assertEqual(
                        root_projection["active_turn_id"], "compaction-turn"
                    )
                    self.assertEqual(root_projection["turn_status"], "inProgress")
                self.assertIsNone(
                    exact_ultra_token_drain_error(
                        usage,
                        token_limit=10_000,
                        first_crossing=first_crossing,
                    )
                )

                dirty = copy.deepcopy(raw)
                dirty["adapter_teardown"]["immediate"] = False
                write_json(usage_path, dirty)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

                if request_kind == "compaction":
                    wrong_root = copy.deepcopy(raw)
                    wrong_root["root_turn_id"] = "compaction-turn"
                    write_json(usage_path, wrong_root)
                    with self.assertRaisesRegex(
                        BenchmarkToolError, "compaction-canary shape"
                    ):
                        read_token_usage(usage_path)

                    wrong_active = copy.deepcopy(raw)
                    wrong_active["threads"][0]["active_turn_id"] = "root-turn"
                    write_json(usage_path, wrong_active)
                    with self.assertRaisesRegex(
                        BenchmarkToolError, "compaction-canary shape"
                    ):
                        read_token_usage(usage_path)

                parsed_dirty = copy.deepcopy(usage)
                parsed_dirty["adapter_teardown"]["completed"] = False
                self.assertIsNotNone(
                    exact_ultra_token_drain_error(
                        parsed_dirty,
                        token_limit=10_000,
                        first_crossing=first_crossing,
                    )
                )
        self.assertGreaterEqual(PROVIDER_GATE_CLEANUP_GRACE_SECONDS, 40.0)

    def args(self, condition: str) -> argparse.Namespace:
        return argparse.Namespace(
            condition=condition,
            task_id="paper-1-t1",
            paper_id="paper-1",
            paper_sha256="a" * 64,
            tier="T1",
            repetition_id="rep-01",
            seed=17,
            pair_id="paper-1-t1-seed-17",
            pair_order="N-first",
            order_index=1 if condition == "N" else 2,
            run_id=f"integration-{condition}",
            agent_id="fake-agent",
            agent_version="1",
            model="fake-model",
            reasoning_effort="medium",
            environment_id="test-environment",
            freeze_check_json=json.dumps(
                {
                    "schema_version": 1,
                    "kind": "highambench-frozen-run-verification",
                    "ok": True,
                    "environment_id": "test-environment",
                    "limits": {
                        "wall_clock_seconds": 1800,
                        "post_submission_validation_reserve_seconds": 369,
                    },
                    "synthetic_canary": {
                        "matrix_assignment": False,
                        "scored": False,
                    },
                },
                sort_keys=True,
                separators=(",", ":"),
            ),
            base_workspace=self.base,
            task_root=self.task,
            controlled_manifest=self.manifest,
            task_dest="task",
            workspace_parent=self.root / "workspaces",
            logs_dir=self.root / "logs",
            raw_jsonl=self.root / "runs.jsonl",
            keep_workspace=False,
            submission_relative="Submission.lean",
            canonical_relative="task/Canonical.lean",
            target_theorem="target",
            local_source_relative=[],
            forbidden_import_prefix=[],
            submission_module="Submission",
            audit_helper=None,
            reject_workspace_local_module_imports=True,
            prompt_relative=None,
            usage_relative="usage.json",
            usage_output=(
                self.root / "logs" / f"integration-{condition}.usage.json"
            ).resolve(),
            agent_command_json=json.dumps(
                [
                    sys.executable,
                    str(self.agent),
                    "{submission}",
                    "{usage_output}",
                ]
            ),
            compile_command_json=json.dumps(
                [
                    sys.executable,
                    str(self.compiler),
                    "{checked_submission}",
                    "{checked_olean}",
                ]
            ),
            audit_command_json=(
                json.dumps(
                    [
                        sys.executable,
                        str(self.audit),
                        "{target_theorem}",
                        "{expected_theorem}",
                        condition,
                    ]
                )
                if condition == "L"
                else json.dumps(
                    [
                        sys.executable,
                        str(self.audit),
                        "{target_theorem}",
                        "{expected_theorem}",
                        condition,
                    ]
                )
            ),
            n_probe_command_json=(
                json.dumps([sys.executable, str(self.probe)]) if condition == "N" else None
            ),
            n_marker=[],
            n_probe_timeout_seconds=2.0,
            hidden_parent=None,
            validation_timeout_seconds=2.0,
            audit_timeout_seconds=2.0,
            poll_seconds=0.01,
            usage_grace_seconds=0.5,
            prompt_startup_timeout_seconds=120.0,
            time_limit_seconds=5.0,
            token_limit=1_000,
            fresh_conversation=True,
            filesystem_isolated=True,
            network_disabled=True,
            seed_enforced=True,
            token_enforced=True,
            library_available=condition == "L",
            strict_protocol=True,
        )

    def configure_signposted_n(
        self, args: argparse.Namespace, command: list[str]
    ) -> str:
        common = self.task / "agent_prompt.md"
        context = self.task / "context.md"
        supplement = self.task / "condition_prompts" / "L.md"
        common.write_text("Solve the fixed target.\n", encoding="utf-8")
        context.write_text("A neutral task context.\n", encoding="utf-8")
        # Only the N-visible common/context/target files enter the controlled
        # staged tree.  The frozen L supplement remains an outer trusted input.
        write_json(self.manifest, create_manifest(self.task))
        supplement.parent.mkdir(exist_ok=True)
        supplement.write_text(
            "The frozen NumStability library is available.\n", encoding="utf-8"
        )
        protocol = {
            "version": "signposted-library-v1",
            "composition_order": [
                "common_prompt",
                "condition_L_supplement_if_condition_L",
                "task_context",
                "fixed_target",
            ],
            "common_prompt": {
                "path": "agent_prompt.md",
                "sha256": hashlib.sha256(common.read_bytes()).hexdigest(),
                "bytes": common.stat().st_size,
            },
            "condition_supplements": {
                "L": {
                    "path": "condition_prompts/L.md",
                    "sha256": hashlib.sha256(supplement.read_bytes()).hexdigest(),
                    "bytes": supplement.stat().st_size,
                }
            },
            "N_receives_condition_supplement": False,
            "relevant_theorem_or_module_hints_supplied": False,
        }
        freeze = json.loads(args.freeze_check_json)
        freeze["prompt_protocol"] = protocol
        args.freeze_check_json = json.dumps(freeze)
        args.prompt_relative = "task/agent_prompt.md"
        command.extend(
            [
                "--condition",
                "N",
                "--prompt-file",
                "{prompt_file}",
                "--context-file",
                "{workspace}/task/context.md",
                "--target-file",
                "{workspace}/task/Canonical.lean",
                "--prompt-ready-output",
                "{prompt_ready_output}",
                "--prompt-go-input",
                "{prompt_go_input}",
                "--prompt-release-output",
                "{prompt_release_output}",
                "--prompt-handshake-nonce",
                "{prompt_handshake_nonce}",
                "--prompt-run-id",
                "{run_id}",
            ]
        )
        args.agent_command_json = json.dumps(command)
        return (
            common.read_text().rstrip()
            + "\n\n## Task context\n\n"
            + context.read_text().rstrip()
            + "\n\n## Fixed Lean target\n\n```lean\n"
            + (self.task / "Canonical.lean").read_text().rstrip()
            + "\n```\n"
        )

    @staticmethod
    def handshake_agent_source(
        *,
        handshake_arguments: str = "",
        before_handshake: str = "",
        after_handshake: str = "",
    ) -> str:
        return (
            "from pathlib import Path\n"
            "import os, sys, time\n"
            "from trusted_usage import emit, prompt_handshake\n"
            "def option(name): return sys.argv[sys.argv.index(name)+1]\n"
            "sections=[Path(option('--prompt-file')).read_text().rstrip()]\n"
            "if '--condition-prompt-file' in sys.argv: sections.append(Path(option('--condition-prompt-file')).read_text().rstrip())\n"
            "sections += ['## Task context\\n\\n'+Path(option('--context-file')).read_text().rstrip(),\n"
            "  '## Fixed Lean target\\n\\n```lean\\n'+Path(option('--target-file')).read_text().rstrip()+'\\n```']\n"
            "prompt='\\n\\n'.join(sections)+'\\n'\n"
            + before_handshake
            + f"prompt_handshake(prompt{handshake_arguments})\n"
            + after_handshake
        )

    def test_runs_fresh_n_and_l_conditions(self) -> None:
        n_result = run_one(self.args("N"))
        l_result = run_one(self.args("L"))
        self.assertTrue(n_result["pass"], n_result)
        self.assertTrue(l_result["pass"], l_result)
        self.assertTrue(n_result["scored"], n_result)
        self.assertTrue(l_result["scored"], l_result)
        self.assertTrue(n_result["useful_work_started"])
        self.assertTrue(l_result["useful_work_started"])
        self.assertTrue(n_result["n_preflight"]["ok"])
        staging = n_result["n_preflight"]["controlled_task_staging"]
        self.assertTrue(staging["complete"])
        self.assertEqual(staging["verified_files"], len(create_manifest(self.task)["files"]))
        self.assertEqual(staging["verified_files"], staging["expected_files"])
        self.assertGreaterEqual(
            n_result["n_preflight"]["filesystem_scan"]["regular_file_count"],
            staging["expected_files"],
        )
        self.assertFalse(n_result["library_use"])
        self.assertTrue(l_result["library_use"])
        self.assertEqual(
            l_result["library_declarations"], ["NumStability.reused"]
        )
        self.assertEqual(n_result["token_usage"]["model_tokens"], 42)
        self.assertIsNone(n_result["workspace"])
        self.assertEqual(list((self.root / "workspaces").iterdir()), [])

    def test_frozen_unseeded_protocol_and_factual_validator_contract(self) -> None:
        args = self.args("L")
        args.seed = None
        args.seed_enforced = False
        protocol = protocol_status(args, n_preflight=None)
        self.assertTrue(protocol["complete"], protocol)
        self.assertFalse(protocol["claims"]["backend_seed_supplied"])
        self.assertFalse(protocol["claims"]["seed_enforced_by_agent"])

        args.reject_workspace_local_module_imports = False
        contract = _validator_contract(
            args,
            compile_command=["lean", "Submission.lean"],
            audit_command=None,
        )
        self.assertFalse(contract["reject_workspace_local_module_imports"])

    def test_validation_authentication_has_exact_schema_and_self_hash(self) -> None:
        result = _authenticate_validation_result(
            {"pass": False, "failure_code": "PROOF_ERROR"},
            run_id="run-1",
            task_id="task-1",
            candidate_sha256="a" * 64,
            target_theorem="target",
            controlled_manifest_sha256="b" * 64,
            validator_contract_sha256="c" * 64,
            submission_request_sha256="d" * 64,
            submission_sequence=2,
        )
        self.assertEqual(
            set(result["authentication"]),
            {
                "schema_version",
                "run_id",
                "task_id",
                "candidate_sha256",
                "target_theorem",
                "controlled_manifest_sha256",
                "validator_contract_sha256",
                "submission_request_sha256",
                "submission_sequence",
            },
        )
        unsigned = {key: value for key, value in result.items() if key != "record_sha256"}
        expected = hashlib.sha256(
            json.dumps(unsigned, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        self.assertEqual(result["record_sha256"], expected)

    def test_final_outcome_uses_global_failure_precedence(self) -> None:
        clean_network = {"detected": False, "note": ""}

        def classify(**changes):
            values = {
                "timed_out": False,
                "token_limited": False,
                "submission_present": True,
                "ultra_submission_attempted": False,
                "direct_submission_violation": False,
                "startup_agent_failure": False,
                "useful_work_started": True,
                "network_violation": clean_network,
                "first_valid_seconds": None,
                "validation_result": {
                    "pass": False,
                    "failure_code": "PROOF_ERROR",
                    "note": "proof rejected",
                },
                "agent_system_error": "adapter tail failed",
                "usage": None,
            }
            values.update(changes)
            return classify_final_outcome(**values)

        self.assertEqual(
            classify(timed_out=True, token_limited=True)[1], "TIME_LIMIT"
        )
        self.assertEqual(
            classify(token_limited=True, submission_present=False)[1],
            "TOKEN_LIMIT",
        )
        no_submission = classify(
            submission_present=False,
            ultra_submission_attempted=False,
            validation_result=None,
            network_violation={"detected": True, "note": "blocked socket"},
        )
        self.assertEqual(no_submission[1], "NO_SUBMISSION")
        self.assertIn("without a proof submission", no_submission[2])

        rule = classify(
            network_violation={"detected": True, "note": "blocked socket"}
        )
        self.assertEqual(rule[1], "RULE_VIOLATION")
        self.assertIn("blocked socket", rule[2])

        syntax = classify(
            validation_result={
                "pass": False,
                "failure_code": "SYNTAX_OR_ELAB",
                "note": "invalid syntax",
            }
        )
        self.assertEqual(syntax[1], "SYNTAX_OR_ELAB")
        self.assertIn("invalid syntax", syntax[2])

        proof = classify()
        self.assertEqual(proof[1], "PROOF_ERROR")
        self.assertEqual(proof[2], "proof rejected")

        rejected_ultra = classify(
            submission_present=False,
            ultra_submission_attempted=True,
        )
        self.assertEqual(rejected_ultra[1], "PROOF_ERROR")

        infrastructure = classify(
            submission_present=False,
            validation_result=None,
            useful_work_started=False,
            startup_agent_failure=True,
            network_violation={"detected": True, "note": "blocked socket"},
        )
        self.assertEqual(infrastructure[1], "SYSTEM_ERROR")
        self.assertIn("adapter tail failed", infrastructure[2])

    def test_records_exact_n_and_l_effective_prompt_provenance(self) -> None:
        common = self.task / "agent_prompt.md"
        context = self.task / "context.md"
        common.write_text("Solve the fixed target.\n", encoding="utf-8")
        context.write_text("A neutral task context.\n", encoding="utf-8")
        write_json(self.manifest, create_manifest(self.task))
        supplement = self.task / "condition_prompts" / "L.md"
        supplement.parent.mkdir()
        supplement.write_text(
            "The frozen NumStability library is available at /library/NumStability.\n",
            encoding="utf-8",
        )
        protocol = {
            "version": "signposted-library-v1",
            "composition_order": [
                "common_prompt",
                "condition_L_supplement_if_condition_L",
                "task_context",
                "fixed_target",
            ],
            "common_prompt": {
                "path": "agent_prompt.md",
                "sha256": hashlib.sha256(common.read_bytes()).hexdigest(),
                "bytes": common.stat().st_size,
            },
            "condition_supplements": {
                "L": {
                    "path": "condition_prompts/L.md",
                    "sha256": hashlib.sha256(supplement.read_bytes()).hexdigest(),
                    "bytes": supplement.stat().st_size,
                }
            },
            "N_receives_condition_supplement": False,
            "relevant_theorem_or_module_hints_supplied": False,
        }

        results = {}
        for condition in ("N", "L"):
            args = self.args(condition)
            freeze = json.loads(args.freeze_check_json)
            freeze["prompt_protocol"] = protocol
            args.freeze_check_json = json.dumps(freeze)
            args.prompt_relative = "task/agent_prompt.md"
            command = json.loads(args.agent_command_json) + [
                "--condition",
                condition,
                "--prompt-file",
                "{prompt_file}",
                "--context-file",
                "{workspace}/task/context.md",
                "--target-file",
                "{workspace}/task/Canonical.lean",
                "--prompt-ready-output",
                "{prompt_ready_output}",
                "--prompt-go-input",
                "{prompt_go_input}",
                "--prompt-release-output",
                "{prompt_release_output}",
                "--prompt-handshake-nonce",
                "{prompt_handshake_nonce}",
                "--prompt-run-id",
                "{run_id}",
            ]
            if condition == "L":
                command.extend(
                    [
                        "--condition-prompt-file",
                        str(supplement.resolve()),
                        "--condition-prompt-sha256",
                        protocol["condition_supplements"]["L"]["sha256"],
                    ]
                )
            args.agent_command_json = json.dumps(command)
            results[condition] = run_one(args)

        n_prompt = results["N"]["prompt_provenance"]
        l_prompt = results["L"]["prompt_provenance"]
        self.assertIsNotNone(n_prompt)
        self.assertIsNotNone(l_prompt)
        self.assertIsNone(n_prompt["condition_supplement"])
        self.assertEqual(
            l_prompt["condition_supplement"], protocol["condition_supplements"]["L"]
        )
        self.assertNotEqual(
            n_prompt["effective_prompt"]["sha256"],
            l_prompt["effective_prompt"]["sha256"],
        )
        self.assertTrue(all(n_prompt["authentication"].values()))
        self.assertTrue(all(l_prompt["authentication"].values()))

    def test_authenticated_release_excludes_startup_and_handles_fast_submission(self) -> None:
        agent = self.root / "handshake-fast-agent.py"
        agent.write_text(
            self.handshake_agent_source(
                before_handshake="time.sleep(0.20)\n",
                after_handshake=(
                    "emit(sys.argv[2],1,30,10,8)\n"
                    f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
                    "time.sleep(0.03)\n"
                    "emit(sys.argv[2],2,35,12,10)\n"
                ),
            ),
            encoding="utf-8",
        )
        args = self.args("N")
        self.configure_signposted_n(
            args,
            [sys.executable, str(agent), "{submission}", "{usage_output}"],
        )
        paths = codex_isolated.prompt_handshake_paths(args.usage_output)
        paths["ready"].parent.mkdir(parents=True, exist_ok=True)
        paths["ready"].symlink_to(self.root / "stale-ready-target")
        paths["go"].write_text("stale go", encoding="utf-8")
        wall_started = time.monotonic()
        result = run_one(args)
        wall_total = time.monotonic() - wall_started

        self.assertTrue(result["pass"], result)
        self.assertGreaterEqual(wall_total, 0.20)
        self.assertLess(result["first_valid_seconds"], 0.15)
        self.assertGreaterEqual(
            result["actual_stop_seconds"], result["first_valid_seconds"]
        )
        prompt_release = result["prompt_release"]
        self.assertTrue(prompt_release["required"])
        self.assertTrue(prompt_release["authenticated"])
        self.assertTrue(prompt_release["timing_exact"])
        self.assertEqual(prompt_release["status"], "released_authenticated")
        self.assertEqual(prompt_release["elapsed_clock"], "CLOCK_MONOTONIC")
        self.assertEqual(len(prompt_release["stale_artifacts_removed"]), 2)
        for name in ("ready", "go", "released"):
            descriptor = prompt_release[name]
            self.assertIsInstance(descriptor, dict)
            artifact = Path(descriptor["path"])
            self.assertTrue(artifact.is_file())
            self.assertEqual(stat.S_IMODE(artifact.lstat().st_mode), 0o444)
            self.assertEqual(
                descriptor["file_sha256"],
                hashlib.sha256(artifact.read_bytes()).hexdigest(),
            )
            self.assertEqual(
                descriptor["record_sha256"],
                descriptor["record"][
                    {"ready": "ready_sha256", "go": "go_sha256", "released": "release_sha256"}[name]
                ],
            )
        released = prompt_release["released"]["record"]
        self.assertLessEqual(
            released["released_at_monotonic_ns"],
            released["turn_start_flushed_at_monotonic_ns"],
        )
        self.assertIn("CLOCK_MONOTONIC", result["time_measurement"])

    def test_prompt_startup_timeout_before_go_is_pre_useful(self) -> None:
        agent = self.root / "never-ready-agent.py"
        agent.write_text("import time\ntime.sleep(2)\n", encoding="utf-8")
        args = self.args("N")
        args.prompt_startup_timeout_seconds = 0.06
        self.configure_signposted_n(
            args,
            [sys.executable, str(agent), "{submission}", "{usage_output}"],
        )
        result = run_one(args)
        self.assertFalse(result["pass"])
        self.assertFalse(result["useful_work_started"])
        self.assertFalse(result["scored"])
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(
            result["prompt_release"]["status"], "startup_timeout_before_go"
        )
        self.assertTrue(result["prompt_release"]["startup_timeout_triggered"])
        self.assertIsNone(result["prompt_release"]["go"])
        self.assertIsNone(result["prompt_release"]["released"])
        self.assertEqual(result["actual_stop_seconds"], 0.0)

    def test_missing_release_after_go_is_useful_unscored_incident(self) -> None:
        agent = self.root / "missing-release-agent.py"
        agent.write_text(
            self.handshake_agent_source(handshake_arguments=", omit_release=True"),
            encoding="utf-8",
        )
        args = self.args("N")
        args.prompt_startup_timeout_seconds = 6.0
        self.configure_signposted_n(
            args,
            [sys.executable, str(agent), "{submission}", "{usage_output}"],
        )
        result = run_one(args)
        self.assertFalse(result["pass"])
        self.assertTrue(result["useful_work_started"], result)
        self.assertFalse(result["scored"])
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(
            result["prompt_release"]["status"], "release_unknown_after_go"
        )
        self.assertIsNotNone(result["prompt_release"]["ready"])
        self.assertIsNotNone(result["prompt_release"]["go"])
        self.assertIsNone(result["prompt_release"]["released"])

    def test_tampered_release_after_go_fails_closed_and_is_useful(self) -> None:
        agent = self.root / "tampered-release-agent.py"
        agent.write_text(
            self.handshake_agent_source(
                handshake_arguments=", tamper_release=True",
                after_handshake="time.sleep(0.10)\n",
            ),
            encoding="utf-8",
        )
        args = self.args("N")
        args.prompt_startup_timeout_seconds = 6.0
        self.configure_signposted_n(
            args,
            [sys.executable, str(agent), "{submission}", "{usage_output}"],
        )
        result = run_one(args)
        self.assertFalse(result["pass"])
        self.assertTrue(result["useful_work_started"], result)
        self.assertFalse(result["scored"])
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(
            result["prompt_release"]["status"], "invalid_release_after_go"
        )
        self.assertIn("self-hash mismatch", result["prompt_release"]["error"])

    def test_ready_symlink_race_fails_before_go_without_useful_work(self) -> None:
        agent = self.root / "ready-symlink-agent.py"
        agent.write_text(
            "from pathlib import Path\n"
            "import os, time\n"
            "Path(os.environ['HIGHAMBENCH_PROMPT_READY_OUTPUT']).symlink_to('/dev/null')\n"
            "time.sleep(1)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.prompt_startup_timeout_seconds = 1.0
        self.configure_signposted_n(
            args,
            [sys.executable, str(agent), "{submission}", "{usage_output}"],
        )
        result = run_one(args)
        self.assertFalse(result["useful_work_started"])
        self.assertFalse(result["scored"])
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(
            result["prompt_release"]["status"], "invalid_ready_before_go"
        )
        self.assertIsNone(result["prompt_release"]["go"])

    def test_token_accounting_does_not_double_count_cached_input(self) -> None:
        usage_path = self.root / "usage.json"
        usage_path.write_text(
            json.dumps(
                {
                    "measurement_source": TOKEN_USAGE_MEASUREMENT_SOURCE,
                    "live_cumulative": True,
                    "input_includes_cached": True,
                    "notification_sequence": 7,
                    "observed_at_unix_ns": 123456789,
                    "input_tokens": 27,
                    "cached_input_tokens": 8,
                    "output_tokens": 8,
                }
            ),
            encoding="utf-8",
        )
        usage = read_token_usage(usage_path)
        self.assertEqual(usage["input_tokens"], 27)
        self.assertEqual(usage["cached_input_tokens"], 8)
        self.assertEqual(usage["model_tokens"], 35)
        self.assertEqual(usage["notification_sequence"], 7)
        self.assertEqual(usage["measurement_source"], TOKEN_USAGE_MEASUREMENT_SOURCE)

        usage_path.write_text(json.dumps({"calls": [usage]}), encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "one atomic top-level object"):
            read_token_usage(usage_path)

        usage_path.write_text(
            json.dumps(
                {
                    "measurement_source": TOKEN_USAGE_MEASUREMENT_SOURCE,
                    "live_cumulative": True,
                    "input_includes_cached": True,
                    "notification_sequence": 8,
                    "observed_at_unix_ns": 123456790,
                    "input_tokens": 2,
                    "cached_input_tokens": 3,
                    "output_tokens": 0,
                }
            ),
            encoding="utf-8",
        )
        with self.assertRaises(BenchmarkToolError):
            read_token_usage(usage_path)

    def test_usage_output_must_be_absolute_and_below_trusted_logs(self) -> None:
        args = self.args("N")
        logs_dir = args.logs_dir.resolve()
        self.assertEqual(trusted_usage_output(args, logs_dir), args.usage_output)

        args.usage_output = Path("relative-usage.json")
        with self.assertRaisesRegex(BenchmarkToolError, "absolute"):
            trusted_usage_output(args, logs_dir)

        args.usage_output = (self.root / "outside-logs.json").resolve()
        with self.assertRaisesRegex(BenchmarkToolError, "below --logs-dir"):
            trusted_usage_output(args, logs_dir)

    def test_nested_submission_wire_revalidation_is_fail_closed(self) -> None:
        source = codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE
        value = {
            "submission_transport": codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
            "call_id": "inner-dynamic-call",
            "inner_dynamic_call_id": "inner-dynamic-call",
            "inner_dynamic_tool_name": "submit_proof",
            "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
            "outer_raw_item_id": "outer-raw-item",
            "outer_raw_item_type": "custom_tool_call",
            "outer_exec_name": "exec",
            "outer_exec_call_id": "outer-provider-call",
            "outer_exec_program": source,
            "outer_exec_program_bytes": codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
            "outer_exec_program_sha256": hashlib.sha256(
                source.encode("utf-8")
            ).hexdigest(),
            **codex_isolated.nested_submission_exec_yield_record(),
            "outer_raw_item_observed_at_monotonic_ns": 10,
            "inner_dynamic_item_started_at_monotonic_ns": 11,
            "outer_raw_item_observed_before_inner_dynamic_call": True,
        }
        _validate_submission_wire(
            value, candidate_path="Candidate.lean", label="test submission"
        )

        adversarial = []
        same_ids = dict(value)
        same_ids["outer_exec_call_id"] = same_ids["call_id"]
        adversarial.append(same_ids)
        wrong_digest = dict(value)
        wrong_digest["outer_exec_program_sha256"] = "0" * 64
        adversarial.append(wrong_digest)
        extra_js = dict(value)
        extra_js["outer_exec_program"] = source + "text('extra');"
        extra_js["outer_exec_program_bytes"] = len(
            extra_js["outer_exec_program"].encode("utf-8")
        )
        extra_js["outer_exec_program_sha256"] = hashlib.sha256(
            extra_js["outer_exec_program"].encode("utf-8")
        ).hexdigest()
        adversarial.append(extra_js)
        for field, expected in codex_isolated.nested_submission_exec_yield_record().items():
            changed = dict(value)
            changed[field] = (
                not expected if isinstance(expected, bool) else expected + 1
                if isinstance(expected, int)
                else str(expected) + "-forged"
            )
            adversarial.append(changed)
        for invalid in adversarial:
            with self.subTest(invalid=invalid):
                with self.assertRaises(BenchmarkToolError):
                    _validate_submission_wire(
                        invalid,
                        candidate_path="Candidate.lean",
                        label="test submission",
                    )

    def test_submission_event_order_accepts_both_exact_orders_and_rejects_tamper(
        self,
    ) -> None:
        inner_first = {
            "submission_event_order": (
                codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
            "inner_dynamic_item_started_at_monotonic_ns": 10,
            "captured_at_monotonic_ns": 11,
            "raw_response_observed_at_monotonic_ns": 12,
        }
        response_first = {
            "submission_event_order": (
                codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
            ),
            "dynamic_call_observed_before_raw_response_completed": False,
            "raw_response_completed_before_dynamic_call_observed": True,
            "raw_response_observed_at_monotonic_ns": 10,
            "inner_dynamic_item_started_at_monotonic_ns": 11,
            "captured_at_monotonic_ns": 12,
        }
        for value in (inner_first, response_first):
            _validate_submission_event_order(
                value, label="test order", derive_from_timestamps=True
            )

        adversarial = []
        both_true = dict(inner_first)
        both_true["raw_response_completed_before_dynamic_call_observed"] = True
        adversarial.append(both_true)
        wrong_enum = dict(inner_first)
        wrong_enum["submission_event_order"] = (
            codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
        )
        adversarial.append(wrong_enum)
        interleaved = dict(response_first)
        interleaved["inner_dynamic_item_started_at_monotonic_ns"] = 9
        adversarial.append(interleaved)
        timestamp_lie = dict(response_first)
        timestamp_lie["captured_at_monotonic_ns"] = 9
        adversarial.append(timestamp_lie)
        for value in adversarial:
            with self.subTest(value=value):
                with self.assertRaises(BenchmarkToolError):
                    _validate_submission_event_order(
                        value,
                        label="test order",
                        derive_from_timestamps=True,
                    )

    def test_final_boundary_binds_outer_inner_and_response_ids(self) -> None:
        source = codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE
        request = {
            "sequence": 1,
            "challenge_sha256": "a" * 64,
            "call_sha256": "b" * 64,
            "attempt_nonce": "nonce",
            "run_id": "run",
            "validator_contract_sha256": "c" * 64,
            "request_sha256": "d" * 64,
            "jsonrpc_request_id": 7,
            "call_id": "inner-dynamic-call",
            "inner_dynamic_call_id": "inner-dynamic-call",
            "inner_dynamic_tool_name": "submit_proof",
            "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
            "submission_transport": codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
            "outer_raw_item_id": "outer-raw-item",
            "outer_raw_item_type": "custom_tool_call",
            "outer_exec_name": "exec",
            "outer_exec_call_id": "outer-provider-call",
            "outer_exec_program": source,
            "outer_exec_program_bytes": codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
            "outer_exec_program_sha256": hashlib.sha256(
                source.encode("utf-8")
            ).hexdigest(),
            **codex_isolated.nested_submission_exec_yield_record(),
            "outer_raw_item_observed_at_monotonic_ns": 10,
            "inner_dynamic_item_started_at_monotonic_ns": 11,
            "outer_raw_item_observed_before_inner_dynamic_call": True,
            "thread_id": "root",
            "turn_id": "turn",
            "response_id": "response",
            "raw_response_notification_sequence": 1,
            "submission_event_order": (
                codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
            "candidate_path": "Candidate.lean",
            "candidate_sha256": "e" * 64,
            "candidate_size_bytes": 10,
        }
        boundary_usage = {
            "input_tokens": 8,
            "cached_input_tokens": 2,
            "cache_write_input_tokens": 0,
            "output_tokens": 2,
            "reasoning_output_tokens": 1,
            "total_tokens": 10,
            "response_count": 1,
            "thread_count": 1,
            "notification_sequence": 1,
            "response_ids": ["response"],
        }
        request["boundary_usage"] = boundary_usage
        ack = {"ack_sha256": "f" * 64}
        bindings = {
            key: value
            for key, value in request.items()
            if key not in {"boundary_usage"}
        }
        bindings["ack_sha256"] = ack["ack_sha256"]
        usage = {
            "submission_boundary_exact": True,
            "submission_boundary": bindings,
            "input_tokens": 8,
            "cached_input_tokens": 2,
            "cache_write_input_tokens": 0,
            "output_tokens": 2,
            "reasoning_output_tokens": 1,
            "model_tokens": 10,
            "response_count": 1,
            "thread_count": 1,
            "notification_sequence": 1,
            "response_ids": ["response"],
        }
        _bind_final_submission_boundary(usage, request, ack)
        for field, forged in (
            ("call_id", "other-inner"),
            ("outer_exec_call_id", "other-outer"),
            ("response_id", "other-response"),
            (
                "submission_event_order",
                codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER,
            ),
            ("outer_exec_yield_time_ms", 2_399_999),
            ("outer_exec_yield_envelope_basis", "forged"),
            ("outer_exec_yield_attempt_wall_seconds", 1_799),
            (
                "outer_exec_yield_post_submission_validation_reserve_seconds",
                368,
            ),
            ("outer_exec_yield_envelope_ms", 2_168_999),
            ("outer_exec_yield_margin_ms", 230_999),
            ("outer_exec_timer_starts_at_or_after_prompt_release", False),
            ("outer_exec_yield_exceeds_envelope", False),
        ):
            with self.subTest(field=field):
                changed = json.loads(json.dumps(usage))
                changed["submission_boundary"][field] = forged
                with self.assertRaisesRegex(BenchmarkToolError, "does not bind"):
                    _bind_final_submission_boundary(changed, request, ack)

    def test_ultra_outer_exec_yield_binds_frozen_and_actual_tail(self) -> None:
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.time_limit_seconds = 1800
        args.validation_timeout_seconds = 120
        args.audit_timeout_seconds = 120
        freeze = {
            "limits": {
                "wall_clock_seconds": 1800,
                "post_submission_validation_reserve_seconds": 369,
            }
        }
        _validate_ultra_submission_yield_envelope(args, freeze)

        for field, value, message in (
            ("wall_clock_seconds", 1799, "1800"),
            (
                "post_submission_validation_reserve_seconds",
                368,
                "369",
            ),
        ):
            with self.subTest(field=field):
                changed = json.loads(json.dumps(freeze))
                changed["limits"][field] = value
                with self.assertRaisesRegex(BenchmarkToolError, message):
                    _validate_ultra_submission_yield_envelope(args, changed)

        wrong_runner_limit = argparse.Namespace(**vars(args))
        wrong_runner_limit.time_limit_seconds = 1799
        with self.assertRaisesRegex(BenchmarkToolError, "equal the frozen"):
            _validate_ultra_submission_yield_envelope(
                wrong_runner_limit, freeze
            )

        oversized_tail = argparse.Namespace(**vars(args))
        oversized_tail.audit_timeout_seconds = 121
        with self.assertRaisesRegex(BenchmarkToolError, "exceeds"):
            _validate_ultra_submission_yield_envelope(oversized_tail, freeze)

        underspecified_production = argparse.Namespace(**vars(args))
        underspecified_production.audit_timeout_seconds = 119
        with self.assertRaisesRegex(BenchmarkToolError, "exactly realize"):
            _validate_ultra_submission_yield_envelope(
                underspecified_production, freeze
            )

        synthetic = json.loads(json.dumps(freeze))
        synthetic["synthetic_canary"] = {
            "matrix_assignment": False,
            "scored": False,
        }
        canary_args = argparse.Namespace(**vars(args))
        canary_args.time_limit_seconds = 60
        canary_args.validation_timeout_seconds = 2
        canary_args.audit_timeout_seconds = 2
        _validate_ultra_submission_yield_envelope(canary_args, synthetic)

    def test_resealed_request_cannot_change_any_call_yield_field(self) -> None:
        for field, expected in codex_isolated.nested_submission_exec_yield_record().items():
            with self.subTest(field=field):
                usage_path = self.root / f"cross-{field}" / "usage.json"
                paths = codex_isolated.submission_barrier_paths(usage_path, 1)
                paths["challenge"].parent.mkdir(parents=True)
                challenge = codex_isolated.authenticated_record(
                    {
                        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                        "kind": "highambench_submission_challenge",
                        "attempt_nonce": "nonce",
                        "run_id": "run",
                        "validator_contract_sha256": "a" * 64,
                        **codex_isolated.nested_submission_exec_yield_record(),
                    },
                    "challenge_sha256",
                )
                call = codex_isolated.authenticated_record(
                    {
                        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                        "kind": "highambench_submission_call",
                        "sequence": 1,
                        "challenge_sha256": challenge["challenge_sha256"],
                        "attempt_nonce": "nonce",
                        "run_id": "run",
                        "validator_contract_sha256": "a" * 64,
                        **codex_isolated.nested_submission_exec_yield_record(),
                    },
                    "call_sha256",
                )
                forged = (
                    not expected if isinstance(expected, bool) else expected + 1
                    if isinstance(expected, int)
                    else str(expected) + "-forged"
                )
                request = codex_isolated.authenticated_record(
                    {
                        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                        "kind": "highambench_submission_request",
                        "sequence": 1,
                        "challenge_sha256": challenge["challenge_sha256"],
                        "call_sha256": call["call_sha256"],
                        "attempt_nonce": "nonce",
                        "run_id": "run",
                        "validator_contract_sha256": "a" * 64,
                        **codex_isolated.nested_submission_exec_yield_record(),
                        field: forged,
                    },
                    "request_sha256",
                )
                write_json(paths["challenge"], challenge)
                write_json(paths["call"], call)
                write_json(paths["request"], request)
                with self.assertRaisesRegex(BenchmarkToolError, "binding mismatch"):
                    _read_submission_request(
                        usage_path,
                        expected_sequence=1,
                        prompt_released_monotonic_ns=1,
                        usage=None,
                    )

    def test_reads_exact_ultra_tree_ledger_and_rejects_bad_sum(self) -> None:
        usage_path = self.root / "ultra-usage.json"
        thread = {
            "thread_id": "root",
            "parent_thread_id": None,
            "agent_path": "root",
            "provisional": False,
            "spawn_call_id": None,
            "spawn_parent_turn_id": None,
            "spawn_parent_response_id": None,
            "spawn_fork_turns": None,
            "spawn_fork_semantics": None,
            "spawn_binding_status": "root_zero",
            "turn_seen": True,
            "active_turn_id": None,
            "turn_status": "completed",
            "thread_status": "idle",
            "response_count": 2,
            "input_tokens": 30,
            "cached_input_tokens": 10,
            "cache_write_input_tokens": 0,
            "output_tokens": 7,
            "reasoning_output_tokens": 3,
            "total_tokens": 37,
            "cumulative_baseline": {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 0,
            },
            "expected_cumulative_baseline": {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 0,
            },
            "last_cumulative": {
                "input_tokens": 30,
                "cached_input_tokens": 10,
                "cache_write_input_tokens": 0,
                "output_tokens": 7,
                "reasoning_output_tokens": 3,
                "total_tokens": 37,
            },
            "cumulative_observation_count": 1,
            "expected_cumulative_projection": {
                "input_tokens": 30,
                "cached_input_tokens": 10,
                "cache_write_input_tokens": 0,
                "output_tokens": 7,
                "reasoning_output_tokens": 3,
                "total_tokens": 37,
            },
            "full_cumulative_projection": {
                "input_tokens": 30,
                "cached_input_tokens": 10,
                "cache_write_input_tokens": 0,
                "output_tokens": 7,
                "reasoning_output_tokens": 3,
                "total_tokens": 37,
            },
            "cumulative_projection_exempt_response_id": None,
            "cumulative_projection_exempt_response_usage": None,
            "observed_cumulative_baseline": {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 0,
            },
            "cumulative_baseline_matches_expected": True,
            "cumulative_projection_match": True,
            "cumulative_projection_status": "matched_full_projection",
            "accounting_complete": True,
        }
        value = {
            "schema_version": 1,
            "accounting_projection_schema_version": (
                ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
            ),
            "measurement_source": ULTRA_USAGE_MEASUREMENT_SOURCE,
            "notification": ULTRA_USAGE_NOTIFICATION,
            "usage_scope": ULTRA_USAGE_SCOPE,
            "live_cumulative": True,
            "input_includes_cached": True,
            "root_thread_id": "root",
            "root_turn_id": "root-turn",
            "thread_count": 1,
            "response_count": 2,
            "notification_sequence": 2,
            "observed_at_unix_ns": 123,
            "input_tokens": 30,
            "cached_input_tokens": 10,
            "cache_write_input_tokens": 0,
            "output_tokens": 7,
            "reasoning_output_tokens": 3,
            "total_tokens": 37,
            "drain_complete": True,
            "measurement_exact": True,
            "first_crossing": None,
            "stop_reason": None,
            "interrupt_requested": False,
            "pending_interrupt_response_count": 0,
            "active_thread_ids": [],
            "unresolved_thread_ids": [],
            "invalid_reasons": [],
            "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
            "raw_spawn_call_ids": [],
            "activity_spawn_call_ids": [],
            "collab_spawn_call_ids": [],
            "resolved_spawn_call_ids": [],
            "failed_spawn_call_ids": [],
            "unresolved_spawn_call_ids": [],
            "unsupported_spawn_call_ids": [],
            "inference_child_thread_ids": [],
            "spawn_linkage_complete": True,
            "descendant_accounting_complete": True,
            "cumulative_projection_complete": True,
            "accounting_complete": True,
            "threads": [thread],
            "response_ids": ["r1", "r2"],
            "response_ledger": [
                {
                    "response_id": "r1",
                    "thread_id": "root",
                    "turn_id": "root-turn",
                    "raw_response_notification_sequence": 1,
                    "raw_response_observed_at_unix_ns": 121,
                    "raw_response_observed_at_monotonic_ns": 221,
                    "usage": ultra_usage_breakdown(10, 3, 2, 1),
                    "provider_gate_call": None,
                },
                {
                    "response_id": "r2",
                    "thread_id": "root",
                    "turn_id": "root-turn",
                    "raw_response_notification_sequence": 2,
                    "raw_response_observed_at_unix_ns": 122,
                    "raw_response_observed_at_monotonic_ns": 222,
                    "usage": ultra_usage_breakdown(20, 7, 5, 2),
                    "provider_gate_call": None,
                },
            ],
            **ultra_fork_policy_fields(),
        }
        write_json(usage_path, value)
        usage = read_token_usage(usage_path)
        assert usage is not None
        self.assertEqual(usage["model_tokens"], 37)
        self.assertEqual(usage["call_count"], 2)
        self.assertEqual(usage["thread_count"], 1)
        self.assertTrue(usage["measurement_exact"])
        self.assertTrue(usage["accounting_complete"])
        self.assertEqual(
            usage["spawn_binding_source"],
            "raw_function_call.call_id=subAgentActivity.id",
        )
        self.assertEqual(
            usage["thread_accounting"][0]["spawn_binding_status"], "root_zero"
        )

        missing_projection = json.loads(json.dumps(value))
        del missing_projection["threads"][0]["cumulative_observation_count"]
        write_json(usage_path, missing_projection)
        with self.assertRaisesRegex(
            BenchmarkToolError, "wrong schema|cumulative_observation_count"
        ):
            read_token_usage(usage_path)

        forged_baseline = json.loads(json.dumps(value))
        forged_baseline["threads"][0]["expected_cumulative_baseline"][
            "input_tokens"
        ] = 1
        forged_baseline["threads"][0]["cumulative_baseline"]["input_tokens"] = 1
        write_json(usage_path, forged_baseline)
        with self.assertRaises(BenchmarkToolError):
            read_token_usage(usage_path)

        reordered_ids = json.loads(json.dumps(value))
        reordered_ids["response_ids"] = ["r2", "r1"]
        write_json(usage_path, reordered_ids)
        with self.assertRaisesRegex(BenchmarkToolError, "reproduce its aggregate"):
            read_token_usage(usage_path)

        value["threads"][0]["output_tokens"] = 8
        write_json(usage_path, value)
        with self.assertRaises(BenchmarkToolError):
            read_token_usage(usage_path)

    def test_job_1509324_lagging_cumulative_is_safe_incomplete_usage(self) -> None:
        usage_path = self.root / "job-1509324-lagging-cumulative.json"
        value = blocked_positive_then_all_usage()
        child = next(
            thread
            for thread in value["threads"]
            if thread["thread_id"] == "child-all"
        )
        lagging_response = ultra_usage_breakdown(10, 1, 1, 0)
        for field in lagging_response:
            value[field] += lagging_response[field]
            child[field] += lagging_response[field]
        child["response_count"] += 1
        child["expected_cumulative_projection"] = {
            field: child["expected_cumulative_baseline"][field] + child[field]
            for field in lagging_response
        }
        child["full_cumulative_projection"] = dict(
            child["expected_cumulative_projection"]
        )
        # The stale cumulative minus both child responses leaves input=2 and
        # cached=3.  This is nonnegative but not a valid usage breakdown.
        child["observed_cumulative_baseline"] = None
        child["cumulative_baseline_matches_expected"] = False
        child["cumulative_projection_match"] = False
        child["cumulative_projection_status"] = "cumulative_projection_mismatch"
        child["accounting_complete"] = False
        value["response_count"] += 1
        value["notification_sequence"] += 1
        value["response_ids"].append("child-r2")
        value["response_ledger"].append(
            {
                "response_id": "child-r2",
                "thread_id": "child-all",
                "turn_id": "child-turn",
                "raw_response_notification_sequence": 4,
                "raw_response_observed_at_unix_ns": 104,
                "raw_response_observed_at_monotonic_ns": 204,
                "usage": lagging_response,
                "provider_gate_call": None,
            }
        )
        value["descendant_accounting_complete"] = False
        value["cumulative_projection_complete"] = False
        value["accounting_complete"] = False
        value["measurement_exact"] = False
        write_json(usage_path, value)

        usage = read_token_usage(usage_path)
        assert usage is not None
        projected_child = next(
            thread
            for thread in usage["thread_accounting"]
            if thread["thread_id"] == "child-all"
        )
        self.assertIsNone(projected_child["observed_cumulative_baseline"])
        self.assertFalse(projected_child["cumulative_projection_match"])
        self.assertFalse(projected_child["accounting_complete"])
        self.assertFalse(usage["measurement_exact"])

    def test_job_1509778_reactivated_interrupt_live_usage_is_valid(self) -> None:
        usage_path = self.root / "job-1509778-reactivated-interrupt.json"
        value = job_1509778_reactivated_interrupt_usage()
        write_json(usage_path, value)

        usage = read_token_usage(usage_path)
        assert usage is not None
        child = next(
            thread
            for thread in usage["thread_accounting"]
            if thread["thread_id"] == "child-all"
        )
        evidence = usage[
            "discarded_after_explicit_child_interrupt_evidence"
        ][0]
        self.assertEqual(child["turn_status"], "inProgress")
        self.assertEqual(
            child["active_turn_id"], "child-followup-turn-1509778"
        )
        self.assertEqual(
            evidence["turn_id"], "child-interrupted-turn-1509778"
        )
        self.assertEqual(
            usage["discarded_after_explicit_child_interrupt_response_count"],
            1,
        )

        wrong_parent = copy.deepcopy(value)
        wrong_parent["provider_usage_reconciliation"][
            "discarded_after_explicit_child_interrupt_evidence"
        ][0]["interrupt_parent_thread_id"] = "child-all"
        write_json(usage_path, wrong_parent)
        with self.assertRaisesRegex(BenchmarkToolError, "direct-child route"):
            read_token_usage(usage_path)

        wrong_path = copy.deepcopy(value)
        wrong_path["provider_usage_reconciliation"][
            "discarded_after_explicit_child_interrupt_evidence"
        ][0]["interrupted_agent_path"] = "/root/wrong-child"
        write_json(usage_path, wrong_path)
        with self.assertRaisesRegex(BenchmarkToolError, "direct-child route"):
            read_token_usage(usage_path)

        malformed_digest = copy.deepcopy(value)
        malformed_digest["provider_usage_reconciliation"][
            "discarded_after_explicit_child_interrupt_evidence"
        ][0]["interrupt_activity_item_sha256"] = "tampered"
        write_json(usage_path, malformed_digest)
        with self.assertRaisesRegex(BenchmarkToolError, "invalid interrupt_activity"):
            read_token_usage(usage_path)

    def test_ultra_fork_policy_blocks_positive_then_all_tree_is_exact(self) -> None:
        usage_path = self.root / "blocked-positive-then-all.json"
        value = blocked_positive_then_all_usage()
        write_json(usage_path, value)

        usage = read_token_usage(usage_path)
        assert usage is not None
        self.assertTrue(usage["measurement_exact"])
        self.assertTrue(usage["accounting_complete"])
        self.assertTrue(usage["fork_policy_complete"])
        self.assertEqual(usage["model_tokens"], 52)
        self.assertEqual(usage["thread_count"], 2)
        self.assertEqual(usage["hook_allowed_spawn_call_ids"], ["call_all"])
        self.assertEqual(
            usage["hook_blocked_spawn_call_ids"], ["call_positive"]
        )
        self.assertEqual(
            usage["policy_blocked_spawn_call_ids"], ["call_positive"]
        )
        self.assertEqual(usage["activity_spawn_call_ids"], ["call_all"])
        self.assertEqual(usage["inference_child_thread_ids"], ["child-all"])
        child = next(
            item
            for item in usage["thread_accounting"]
            if item["thread_id"] == "child-all"
        )
        self.assertEqual(child["spawn_fork_turns"], "all")
        self.assertEqual(child["spawn_binding_status"], "resolved")
        self.assertEqual(
            child["expected_cumulative_baseline"]["total_tokens"], 15
        )

    def test_ultra_fork_policy_none_child_requires_exact_zero_projection(self) -> None:
        usage_path = self.root / "fork-policy-none-child.json"
        value = blocked_positive_then_all_usage()
        child = value["threads"][0]
        evidence = value["fork_policy"]["call_evidence"][0]
        child["spawn_fork_turns"] = "none"
        child["spawn_fork_semantics"] = "no_history_zero"
        evidence["fork_turns"] = "none"
        evidence["fork_semantics"] = "no_history_zero"
        zero = ultra_usage_breakdown(0, 0, 0, 0)
        raw = {
            field: child[field]
            for field in (
                "input_tokens",
                "cached_input_tokens",
                "cache_write_input_tokens",
                "output_tokens",
                "reasoning_output_tokens",
                "total_tokens",
            )
        }
        child.update(
            {
                "cumulative_baseline": zero,
                "expected_cumulative_baseline": zero,
                "last_cumulative": raw,
                "expected_cumulative_projection": raw,
                "full_cumulative_projection": raw,
                "observed_cumulative_baseline": zero,
            }
        )
        write_json(usage_path, value)
        usage = read_token_usage(usage_path)
        assert usage is not None
        self.assertTrue(usage["measurement_exact"])
        none_child = next(
            item
            for item in usage["thread_accounting"]
            if item["thread_id"] == "child-all"
        )
        self.assertEqual(none_child["spawn_fork_turns"], "none")
        self.assertEqual(none_child["expected_cumulative_baseline"], zero)

        forged = json.loads(json.dumps(value))
        forged_child = forged["threads"][0]
        nonzero = ultra_usage_breakdown(5, 0, 1, 0)
        projected = {
            field: nonzero[field] + raw[field] for field in nonzero
        }
        forged_child.update(
            {
                "cumulative_baseline": nonzero,
                "expected_cumulative_baseline": nonzero,
                "last_cumulative": projected,
                "expected_cumulative_projection": projected,
                "full_cumulative_projection": projected,
                "observed_cumulative_baseline": nonzero,
            }
        )
        write_json(usage_path, forged)
        with self.assertRaisesRegex(BenchmarkToolError, "zero baseline"):
            read_token_usage(usage_path)

    def test_ultra_fork_policy_missing_or_tampered_fields_fail_closed(self) -> None:
        usage_path = self.root / "fork-policy-tamper.json"
        original = blocked_positive_then_all_usage()

        for field in list(original["fork_policy"]):
            with self.subTest(location="fork_policy", field=field):
                changed = json.loads(json.dumps(original))
                del changed["fork_policy"][field]
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

        for field in (
            "fork_policy",
            "hook_observed_spawn_call_ids",
            "hook_allowed_spawn_call_ids",
            "hook_blocked_spawn_call_ids",
            "policy_blocked_spawn_call_ids",
            "hook_invalid_spawn_call_ids",
            "fork_policy_complete",
        ):
            with self.subTest(location="usage", field=field):
                changed = json.loads(json.dumps(original))
                del changed[field]
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

        for field, forged in (
            ("usage_hint", "tampered usage hint"),
            ("usage_hint_sha256", "0" * 64),
            ("helper_sha256", "0" * 64),
            ("hooks_json_sha256", "0" * 64),
            ("matcher", "spawn_agent"),
            ("hook_trust_bypass_cli_flag_present", False),
            ("hook_trust_bypass_thread_config", {}),
            ("hook_trust_bypass_effective_source", "cli_flag"),
            ("positive_integer_fork_turns_allowed", True),
        ):
            with self.subTest(location="fork_policy_value", field=field):
                changed = json.loads(json.dumps(original))
                changed["fork_policy"][field] = forged
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

        for field in list(original["fork_policy"]["call_evidence"][0]):
            with self.subTest(location="call_evidence", field=field):
                changed = json.loads(json.dumps(original))
                del changed["fork_policy"]["call_evidence"][0][field]
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

        for field, forged in (
            ("fork_semantics", "unsupported_positive_turn_suffix"),
            ("hook_run_id", "pre-tool-use:0:/forged:call_all"),
            ("hook_source_path", "/forged/hooks.json"),
            ("decision", "block"),
            ("feedback", "forged feedback"),
            ("hook_started_count", 2),
            ("resolution_status", "policy_blocked_without_child"),
        ):
            with self.subTest(location="call_evidence_value", field=field):
                changed = json.loads(json.dumps(original))
                changed["fork_policy"]["call_evidence"][0][field] = forged
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

        for field, forged in (
            ("hook_observed_spawn_call_ids", ["call_all"]),
            ("hook_allowed_spawn_call_ids", []),
            ("hook_blocked_spawn_call_ids", []),
            ("policy_blocked_spawn_call_ids", []),
            ("hook_invalid_spawn_call_ids", ["call_all"]),
        ):
            with self.subTest(location="projected_ids", field=field):
                changed = json.loads(json.dumps(original))
                changed[field] = forged
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

    def test_ultra_fork_policy_rejects_blocked_call_activity_and_positive_child(self) -> None:
        usage_path = self.root / "fork-policy-positive-child.json"
        for mutation in ("activity", "positive_child"):
            with self.subTest(mutation=mutation):
                changed = blocked_positive_then_all_usage()
                if mutation == "activity":
                    changed["activity_spawn_call_ids"] = [
                        "call_all",
                        "call_positive",
                    ]
                    changed["fork_policy"]["call_evidence"][1][
                        "child_activity_observed"
                    ] = True
                else:
                    child = changed["threads"][0]
                    child["spawn_call_id"] = "call_positive"
                    child["spawn_fork_turns"] = "3"
                    child["spawn_fork_semantics"] = (
                        "unsupported_positive_turn_suffix"
                    )
                write_json(usage_path, changed)
                with self.assertRaises(BenchmarkToolError):
                    read_token_usage(usage_path)

    def test_job_1507844_positive_child_pattern_remains_unscorable(self) -> None:
        value = job_1507844_positive_child_usage()
        incident_agent = self.root / "job_1507844_positive_child.py"
        incident_agent.write_text(
            "from pathlib import Path\n"
            "import json, sys\n"
            f"value = {value!r}\n"
            "path = Path(sys.argv[1]); path.parent.mkdir(parents=True, exist_ok=True)\n"
            "path.write_text(json.dumps(value))\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.run_id = "job-1507844-positive-child"
        args.reasoning_effort = "ultra"
        args.token_limit = 2_000_000
        args.usage_output = (
            self.root / "logs" / "job-1507844-positive-child.usage.json"
        ).resolve()
        args.agent_command_json = json.dumps(
            [sys.executable, str(incident_agent), "{usage_output}"]
        )

        result = run_one(args)

        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertFalse(result["pass"], result)
        self.assertFalse(result["scored"], result)
        self.assertEqual(result["failure_code"], "NO_SUBMISSION")
        self.assertEqual(result["agent_exit_code"], 0)
        self.assertEqual(result["token_usage"]["model_tokens"], 754_638)
        self.assertFalse(result["token_usage"]["measurement_exact"])
        self.assertFalse(result["token_usage"]["accounting_complete"])
        self.assertFalse(result["token_usage"]["fork_policy_complete"])
        self.assertEqual(
            result["token_usage"]["hook_invalid_spawn_call_ids"],
            ["call_job1507844_positive"],
        )
        child = next(
            item
            for item in result["token_usage"]["thread_accounting"]
            if item["thread_id"] == "library-search-child"
        )
        self.assertEqual(child["total_tokens"], 729_775)
        self.assertEqual(child["last_cumulative"]["total_tokens"], 754_638)
        self.assertIsNone(child["expected_cumulative_baseline"])

    def test_ultra_accepts_authenticated_request_boundary_without_tree_drain(self) -> None:
        ultra_agent = self.root / "ultra_barrier_agent.py"
        ultra_agent.write_text(
            "from pathlib import Path\n"
            "import hashlib, json, os, sys, time\n"
            "usage = Path(sys.argv[1])\n"
            "base = str(usage)\n"
            "def auth(value, field):\n"
            "  unsigned = {k:v for k,v in value.items() if k != field}\n"
            "  value[field] = hashlib.sha256(json.dumps(unsigned, sort_keys=True, separators=(',', ':')).encode()).hexdigest()\n"
            "  return value\n"
            "def publish(path, value):\n"
            "  path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)\n"
            "  tmp = Path(str(path) + '.agent-tmp'); tmp.write_text(json.dumps(value))\n"
            "  os.replace(tmp, path)\n"
            "challenge = json.loads(Path(base + '.submission-challenge.json').read_text())\n"
            f"candidate = {SIGNATURE!r}.encode()\n"
            "Path('Candidate.lean').write_bytes(candidate)\n"
            "snapshot = Path(base + '.submission-1.lean'); snapshot.write_bytes(candidate)\n"
            f"outer_source = {codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE!r}\n"
            f"yield_record = {codex_isolated.nested_submission_exec_yield_record()!r}\n"
            "captured_unix = time.time_ns(); captured_mono = time.monotonic_ns()\n"
            "outer_observed=max(1,captured_mono-2); inner_started=max(1,captured_mono-1)\n"
            f"call = auth({{'schema_version':{codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION},'kind':'highambench_submission_call','sequence':1,"
            "'challenge_sha256':challenge['challenge_sha256'],'attempt_nonce':challenge['attempt_nonce'],"
            "'run_id':challenge['run_id'],'validator_contract_sha256':challenge['validator_contract_sha256'],"
            "'jsonrpc_request_id':7,'call_id':'call-1','inner_dynamic_call_id':'call-1',"
            "'inner_dynamic_tool_name':'submit_proof','inner_dynamic_arguments':{'candidate_path':'Candidate.lean'},"
            f"'submission_transport':{codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT!r},"
            "'outer_raw_item_id':'raw-outer-call-1','outer_raw_item_type':'custom_tool_call',"
            "'outer_exec_name':'exec','outer_exec_call_id':'outer-call-1','outer_exec_program':outer_source,"
            "'outer_exec_program_bytes':len(outer_source.encode()),"
            "'outer_exec_program_sha256':hashlib.sha256(outer_source.encode()).hexdigest(),"
            "**yield_record,"
            "'outer_raw_item_observed_at_monotonic_ns':outer_observed,"
            "'inner_dynamic_item_started_at_monotonic_ns':inner_started,"
            "'outer_raw_item_observed_before_inner_dynamic_call':True,"
            "'thread_id':'root','turn_id':'turn-1',"
            "'candidate_path':'Candidate.lean','candidate_sha256':hashlib.sha256(candidate).hexdigest(),"
            "'candidate_size_bytes':len(candidate),'snapshot_name':snapshot.name,"
            "'captured_at_unix_ns':captured_unix,'captured_at_monotonic_ns':captured_mono}, 'call_sha256')\n"
            "publish(base + '.submission-call.json', call)\n"
            "zero={'input_tokens':0,'cached_input_tokens':0,'cache_write_input_tokens':0,"
            "'output_tokens':0,'reasoning_output_tokens':0,'total_tokens':0}\n"
            "full={'input_tokens':100,'cached_input_tokens':20,'cache_write_input_tokens':0,"
            "'output_tokens':10,'reasoning_output_tokens':5,'total_tokens':110}\n"
            "thread={'thread_id':'root','parent_thread_id':None,'provisional':False,"
            "'spawn_call_id':None,'spawn_parent_turn_id':None,'spawn_parent_response_id':None,"
            "'spawn_fork_turns':None,'spawn_fork_semantics':None,'spawn_binding_status':'root_zero',"
            "'response_count':1,"
            "'input_tokens':100,'cached_input_tokens':20,'cache_write_input_tokens':0,"
            "'output_tokens':10,'reasoning_output_tokens':5,'total_tokens':110,"
            "'cumulative_baseline':zero,'expected_cumulative_baseline':zero,'last_cumulative':None,"
            "'cumulative_observation_count':0,'expected_cumulative_projection':full,"
            "'full_cumulative_projection':full,'cumulative_projection_exempt_response_id':None,"
            "'cumulative_projection_exempt_response_usage':None,'observed_cumulative_baseline':None,"
            "'cumulative_baseline_matches_expected':False,'cumulative_projection_match':False,"
            "'cumulative_projection_status':'missing_cumulative','accounting_complete':False}\n"
            "live={'schema_version':1,'accounting_projection_schema_version':"
            f"{ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION},"
            f"**{ultra_fork_policy_fields()!r},"
            "'measurement_source':'codex_app_server_rawResponse/completed',"
            "'notification':'rawResponse/completed','usage_scope':'rooted_attempt_thread_tree_completed_responses',"
            "'live_cumulative':True,'input_includes_cached':True,'root_thread_id':'root','root_turn_id':'turn-1',"
            "'thread_count':1,'response_count':1,'input_tokens':100,'cached_input_tokens':20,"
            "'cache_write_input_tokens':0,'output_tokens':10,'reasoning_output_tokens':5,'total_tokens':110,"
            "'notification_sequence':1,'observed_at_unix_ns':time.time_ns(),'first_crossing':None,"
            "'stop_reason':None,'interrupt_requested':False,'pending_interrupt_response_count':0,"
            "'active_thread_ids':['root'],'unresolved_thread_ids':[],'drain_complete':False,"
            "'measurement_exact':False,'invalid_reasons':[],"
            "'spawn_binding_source':'raw_function_call.call_id=subAgentActivity.id',"
            "'raw_spawn_call_ids':[],'activity_spawn_call_ids':[],'collab_spawn_call_ids':[],"
            "'resolved_spawn_call_ids':[],'failed_spawn_call_ids':[],"
            "'unresolved_spawn_call_ids':[],'unsupported_spawn_call_ids':[],"
            "'inference_child_thread_ids':[],'spawn_linkage_complete':True,"
            "'descendant_accounting_complete':True,'cumulative_projection_complete':False,"
            "'accounting_complete':False,'threads':[thread],'response_ids':['r1']}\n"
            "publish(usage, live)\n"
            "boundary_usage={'input_tokens':100,'cached_input_tokens':20,'cache_write_input_tokens':0,"
            "'output_tokens':10,'reasoning_output_tokens':5,'total_tokens':110,'response_count':1,"
            "'thread_count':1,'notification_sequence':1,'response_ids':['r1']}\n"
            f"request = auth({{'schema_version':{codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION},'kind':'highambench_submission_request','sequence':1,"
            "'challenge_sha256':challenge['challenge_sha256'],'call_sha256':call['call_sha256'],"
            "'attempt_nonce':challenge['attempt_nonce'],'run_id':challenge['run_id'],"
            "'validator_contract_sha256':challenge['validator_contract_sha256'],'jsonrpc_request_id':7,"
            "'call_id':'call-1','inner_dynamic_call_id':'call-1',"
            "'inner_dynamic_tool_name':'submit_proof','inner_dynamic_arguments':{'candidate_path':'Candidate.lean'},"
            f"'submission_transport':{codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT!r},"
            "'outer_raw_item_id':'raw-outer-call-1','outer_raw_item_type':'custom_tool_call',"
            "'outer_exec_name':'exec','outer_exec_call_id':'outer-call-1','outer_exec_program':outer_source,"
            "'outer_exec_program_bytes':len(outer_source.encode()),"
            "'outer_exec_program_sha256':hashlib.sha256(outer_source.encode()).hexdigest(),"
            "**yield_record,"
            "'outer_raw_item_observed_at_monotonic_ns':outer_observed,"
            "'inner_dynamic_item_started_at_monotonic_ns':inner_started,"
            "'outer_raw_item_observed_before_inner_dynamic_call':True,"
            "'thread_id':'root','turn_id':'turn-1','response_id':'r1',"
            "'raw_response_notification_sequence':1,'raw_response_observed_at_unix_ns':time.time_ns(),"
            "'raw_response_observed_at_monotonic_ns':time.monotonic_ns(),'candidate_path':'Candidate.lean',"
            "'candidate_sha256':hashlib.sha256(candidate).hexdigest(),'candidate_size_bytes':len(candidate),"
            "'snapshot_name':snapshot.name,'captured_at_unix_ns':captured_unix,"
            "'captured_at_monotonic_ns':captured_mono,'request_published_at_unix_ns':time.time_ns(),"
            "'request_published_at_monotonic_ns':time.monotonic_ns(),'boundary_usage':boundary_usage,"
            "'raw_response_completed_before_boundary_publication':True,"
            "'submission_event_order':'inner_dynamic_call_before_raw_response_completed',"
            "'dynamic_call_observed_before_raw_response_completed':True,"
            "'raw_response_completed_before_dynamic_call_observed':False,"
            "'candidate_captured_at_dynamic_call':True,'root_only':True,'descendants_quiescent':True,"
            "'sole_model_tool_call_in_response':True,'outer_exec_final_raw_item':True,"
            "'inner_dynamic_call_observed':True,'inner_dynamic_item_started':True,"
            "'inner_submit_invocation_exact':True,'inner_submit_only_nested_tool_call':True}, 'request_sha256')\n"
            "publish(base + '.submission-request.json', request)\n"
            "ack_path = Path(base + '.submission-ack.json')\n"
            "while not ack_path.exists(): time.sleep(0.005)\n"
            "ack = json.loads(ack_path.read_text())\n"
            "assert ack['decision'] == 'accept'\n"
            f"boundary={{'schema_version':{codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION},'authenticated':True,'status':'accepted','exact':True,'sequence':1,"
            "'challenge_sha256':challenge['challenge_sha256'],'call_sha256':call['call_sha256'],"
            "'attempt_nonce':challenge['attempt_nonce'],'run_id':challenge['run_id'],"
            "'validator_contract_sha256':challenge['validator_contract_sha256'],"
            "'request_sha256':request['request_sha256'],'ack_sha256':ack['ack_sha256'],"
            "'jsonrpc_request_id':7,'call_id':'call-1','inner_dynamic_call_id':'call-1',"
            "'inner_dynamic_tool_name':'submit_proof','inner_dynamic_arguments':{'candidate_path':'Candidate.lean'},"
            f"'submission_transport':{codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT!r},"
            "'outer_raw_item_id':'raw-outer-call-1','outer_raw_item_type':'custom_tool_call',"
            "'outer_exec_name':'exec','outer_exec_call_id':'outer-call-1','outer_exec_program':outer_source,"
            "'outer_exec_program_bytes':len(outer_source.encode()),"
            "'outer_exec_program_sha256':hashlib.sha256(outer_source.encode()).hexdigest(),"
            "**yield_record,"
            "'outer_raw_item_observed_at_monotonic_ns':outer_observed,"
            "'inner_dynamic_item_started_at_monotonic_ns':inner_started,"
            "'outer_raw_item_observed_before_inner_dynamic_call':True,"
            "'thread_id':'root','turn_id':'turn-1','response_id':'r1',"
            "'raw_response_notification_sequence':1,'candidate_path':'Candidate.lean',"
            "'candidate_sha256':hashlib.sha256(candidate).hexdigest(),'candidate_size_bytes':len(candidate),"
            "'request_published_at_unix_ns':request['request_published_at_unix_ns'],"
            "'request_published_at_monotonic_ns':request['request_published_at_monotonic_ns'],"
            "'validator_accepted_at_unix_ns':ack['validator_accepted_at_unix_ns'],"
            "'validator_accepted_elapsed_seconds':ack['validator_accepted_elapsed_seconds'],"
            "'raw_response_completed_before_boundary_publication':True,"
            "'submission_event_order':'inner_dynamic_call_before_raw_response_completed',"
            "'dynamic_call_observed_before_raw_response_completed':True,"
            "'raw_response_completed_before_dynamic_call_observed':False,"
            "'candidate_captured_at_dynamic_call':True,'current_response_cumulative_required':False,"
            "'root_only':True,'descendants_quiescent':True,'sole_model_tool_call_in_response':True,"
            "'outer_exec_final_raw_item':True,'inner_dynamic_call_observed':True,"
            "'inner_dynamic_item_started':True,'inner_submit_invocation_exact':True,"
            "'inner_submit_only_nested_tool_call':True,'inner_dynamic_call_left_blocked':True,"
            "'inner_dynamic_tool_response_sent':False,'outer_exec_output_emitted':False,"
            "'later_model_response_possible':False}\n"
            "thread.update({'expected_cumulative_projection':zero,"
            "'cumulative_projection_exempt_response_id':'r1',"
            "'cumulative_projection_exempt_response_usage':full,"
            "'cumulative_baseline_matches_expected':True,'cumulative_projection_match':True,"
            "'cumulative_projection_status':'zero_pre_response_without_cumulative_notification',"
            "'accounting_complete':True})\n"
            "live.update({'measurement_exact':True,'stop_reason':'first_valid_proof','submission_boundary':boundary,"
            "'cumulative_projection_complete':True,'accounting_complete':True,"
            "'observed_at_unix_ns':time.time_ns()})\n"
            "publish(usage, live)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.keep_workspace = True
        args.agent_command_json = json.dumps(
            [sys.executable, str(ultra_agent), "{usage_output}"]
        )

        validation_workspaces: list[Path] = []

        def validate_frozen(config):
            validation_workspaces.append(config.workspace)
            self.assertTrue(config.reject_workspace_local_module_imports)
            time.sleep(0.05)
            return validate_submission(config)

        with mock.patch("runner.validate", side_effect=validate_frozen) as validate_mock:
            result = run_one(args)

        self.assert_legacy_ungated_ultra_rejected(result)
        validate_mock.assert_not_called()
        return
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["scored"], result)
        self.assertEqual(validate_mock.call_count, 1)
        self.assertEqual(len(validation_workspaces), 1)
        self.assertIn("highambench-barrier-validation-", validation_workspaces[0].name)
        self.assertLess(result["first_valid_seconds"], result["actual_stop_seconds"])
        self.assertIn("authenticated nested submission-boundary", result["time_measurement"])
        self.assertIn("inner submit_proof blocked", result["time_measurement"])
        self.assertEqual(result["token_usage"]["model_tokens"], 110)
        self.assertTrue(result["token_usage"]["measurement_exact"])
        self.assertFalse(result["token_usage"]["drain_complete"])
        self.assertFalse(result["token_usage"]["tree_quiescent"])
        self.assertTrue(result["token_usage"]["submission_boundary_exact"])
        self.assertTrue(result["token_measurement"]["post_submission_usage_established"])
        self.assertTrue(
            result["protocol"]["verified"][
                "authenticated_first_valid_proof_boundary"
            ]
        )
        self.assertFalse(result["submission_changed_after_acceptance"])
        self.assertEqual(
            Path(result["accepted_submission_log"]).read_text(encoding="utf-8"),
            SIGNATURE,
        )
        boundary_record = result["ultra_submission_boundary"]
        artifacts = boundary_record["artifacts"]
        self.assertEqual(
            artifacts["snapshot"]["file_sha256"], result["submission_sha256"]
        )
        for artifact in artifacts.values():
            artifact_path = Path(artifact["path"])
            self.assertTrue(artifact_path.is_file())
            self.assertEqual(artifact_path.stat().st_mode & 0o222, 0)
        request_record = json.loads(
            Path(artifacts["request"]["path"]).read_text(encoding="utf-8")
        )
        self.assertEqual(
            request_record["request_sha256"], boundary_record["request_sha256"]
        )
        validation_path = Path(result["validation_log"])
        validation_bytes = validation_path.read_bytes()
        validation_record = json.loads(validation_bytes)
        self.assertEqual(
            result["validation_log_sha256"],
            hashlib.sha256(validation_bytes).hexdigest(),
        )
        self.assertEqual(
            result["validation_record_sha256"],
            validation_record["record_sha256"],
        )
        unsigned_validation = {
            key: value
            for key, value in validation_record.items()
            if key != "record_sha256"
        }
        self.assertEqual(
            validation_record["record_sha256"],
            hashlib.sha256(
                json.dumps(
                    unsigned_validation, sort_keys=True, separators=(",", ":")
                ).encode()
            ).hexdigest(),
        )
        authentication = validation_record["authentication"]
        self.assertEqual(
            authentication["candidate_sha256"], result["submission_sha256"]
        )
        self.assertEqual(
            authentication["submission_request_sha256"],
            boundary_record["request_sha256"],
        )
        self.assertEqual(
            authentication["submission_sequence"], boundary_record["sequence"]
        )
        self.assertFalse(validation_workspaces[0].exists())

        # A post-boundary adapter failure (including failure to delete its
        # disposable Codex state) must invalidate the otherwise valid proof.
        ultra_agent.write_text(
            ultra_agent.read_text(encoding="utf-8") + "raise SystemExit(2)\n",
            encoding="utf-8",
        )
        failed_args = self.args("N")
        failed_args.run_id = "integration-cleanup-error-N"
        failed_args.reasoning_effort = "ultra"
        failed_args.keep_workspace = True
        failed_args.time_limit_seconds = 0.5
        failed_args.usage_output = (
            self.root / "logs" / "integration-cleanup-error-N.usage.json"
        ).resolve()
        failed_args.agent_command_json = json.dumps(
            [sys.executable, str(ultra_agent), "{usage_output}"]
        )
        def delayed_valid_submission(config):
            time.sleep(0.6)
            return validate_submission(config)

        with mock.patch("runner.validate", side_effect=delayed_valid_submission):
            failed_result = run_one(failed_args)
        self.assertFalse(failed_result["pass"], failed_result)
        self.assertFalse(failed_result["scored"], failed_result)
        self.assertEqual(failed_result["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(failed_result["agent_exit_code"], 2)
        self.assertGreater(
            failed_result["actual_stop_seconds"], failed_args.time_limit_seconds
        )
        self.assertIsNone(failed_result["first_valid_seconds"])
        self.assertIsNone(failed_result["accepted_submission_log"])
        self.assertFalse(failed_result["ultra_submission_boundary"]["verified"])
        self.assertIsNone(failed_result["ultra_submission_boundary"]["artifacts"])
        self.assertIn("accepted submission boundary", failed_result["failure_note"])

    def test_ultra_direct_submission_is_an_immediate_rule_violation(self) -> None:
        crossing_agent = self.root / "ultra_crossing_agent.py"
        crossing_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit_ultra\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "emit_ultra(sys.argv[2], 1, 100, 20, 10, False)\n"
            "time.sleep(0.1)\n"
            "emit_ultra(sys.argv[2], 2, 1000, 200, 23, True, 1023)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.agent_command_json = json.dumps(
            [sys.executable, str(crossing_agent), "{submission}", "{usage_output}"]
        )

        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)

        validate_mock.assert_not_called()
        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertFalse(result["pass"], result)
        self.assertFalse(result["scored"], result)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertIsNone(result["first_valid_seconds"])
        self.assertIsNone(result["accepted_submission_log"])
        self.assertIn("Submission.lean", result["failure_note"])

    def test_ultra_direct_submission_never_uses_natural_stop_validation(self) -> None:
        inexact_agent = self.root / "ultra_inexact_agent.py"
        inexact_agent.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "from trusted_usage import emit_ultra\n"
            f"candidate = Path(sys.argv[1]); candidate.write_text({SIGNATURE!r}); candidate.unlink()\n"
            "emit_ultra(sys.argv[2], 1, 100, 20, 10, False)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.agent_command_json = json.dumps(
            [sys.executable, str(inexact_agent), "{submission}", "{usage_output}"]
        )

        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)

        validate_mock.assert_not_called()
        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "NO_SUBMISSION")
        self.assertIn("without a proof submission", result["failure_note"])
        self.assertFalse(result["protocol"]["complete"])

    def test_ultra_token_limit_precedes_simultaneous_direct_submission(self) -> None:
        limiting_agent = self.root / "ultra_direct_and_cap.py"
        limiting_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "emit_ultra(sys.argv[2], 1, 1000, 200, 23, True, 1023)\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(1)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.agent_command_json = json.dumps(
            [sys.executable, str(limiting_agent), "{submission}", "{usage_output}"]
        )
        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)
        validate_mock.assert_not_called()
        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT")
        self.assertFalse(result["scored"], result)
        self.assertNotEqual(result["agent_exit_code"], 0)
        self.assertEqual(result["token_usage"]["model_tokens"], 1023)

    def test_ultra_token_limit_allows_exact_drain_and_clean_adapter_exit(self) -> None:
        draining_agent = self.root / "ultra_exact_cap_drain.py"
        draining_agent.write_text(
            "import sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "# First publish the crossing response while its terminal event tail\n"
            "# is still active, then the exact natural drain, then finish cleanup.\n"
            "emit_ultra(sys.argv[1], 1, 1000, 200, 23, False, 1023)\n"
            "time.sleep(0.05)\n"
            "emit_ultra(sys.argv[1], 1, 1000, 200, 23, True, 1023)\n"
            "time.sleep(0.15)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.usage_grace_seconds = 1.0
        args.agent_command_json = json.dumps(
            [sys.executable, str(draining_agent), "{usage_output}"]
        )

        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)

        validate_mock.assert_not_called()
        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertFalse(result["pass"], result)
        self.assertTrue(result["scored"], result)
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT")
        self.assertEqual(result["agent_exit_code"], 0)
        self.assertIsNone(result["token_measurement"]["measurement_error"])
        self.assertTrue(result["token_usage"]["drain_complete"])
        self.assertTrue(result["token_usage"]["measurement_exact"])
        self.assertEqual(result["token_usage"]["model_tokens"], 1023)

    def test_ultra_token_limit_cleanup_timeout_stays_unscored_even_if_signal_exits_zero(
        self,
    ) -> None:
        hanging_agent = self.root / "ultra_cap_cleanup_hang.py"
        hanging_agent.write_text(
            "import signal, sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "def stopped(_signal, _frame):\n"
            "  # A signal handler cannot retroactively authenticate a natural exit.\n"
            "  emit_ultra(sys.argv[1], 1, 1000, 200, 23, True, 1023)\n"
            "  raise SystemExit(0)\n"
            "signal.signal(signal.SIGTERM, stopped)\n"
            "emit_ultra(sys.argv[1], 1, 1000, 200, 23, True, 1023)\n"
            "time.sleep(10)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.usage_grace_seconds = 0.1
        args.agent_command_json = json.dumps(
            [sys.executable, str(hanging_agent), "{usage_output}"]
        )

        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)

        validate_mock.assert_not_called()
        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertFalse(result["pass"], result)
        self.assertFalse(result["scored"], result)
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT")
        self.assertEqual(result["agent_exit_code"], 0)
        self.assertIn(
            "token-limit cleanup grace",
            result["token_measurement"]["measurement_error"],
        )
        self.assertFalse(result["protocol"]["complete"])

    def test_ultra_token_stop_before_wall_keeps_token_limit_during_cleanup(self) -> None:
        near_wall_agent = self.root / "ultra_cap_before_wall.py"
        near_wall_agent.write_text(
            "import sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "time.sleep(0.05)\n"
            "emit_ultra(sys.argv[1], 1, 1000, 200, 23, True, 1023)\n"
            "# This is adapter cleanup after the already-latched token stop.\n"
            "time.sleep(0.25)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.time_limit_seconds = 0.2
        args.usage_grace_seconds = 1.0
        args.agent_command_json = json.dumps(
            [sys.executable, str(near_wall_agent), "{usage_output}"]
        )

        result = run_one(args)

        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT", result)
        self.assertTrue(result["scored"], result)
        self.assertEqual(result["agent_exit_code"], 0)
        self.assertGreater(result["actual_stop_seconds"], args.time_limit_seconds)
        self.assertIsNone(result["token_measurement"]["measurement_error"])

    def test_ultra_exact_token_drain_cannot_change_before_exit(self) -> None:
        changing_agent = self.root / "ultra_cap_drain_changes.py"
        changing_agent.write_text(
            "import sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "emit_ultra(sys.argv[1], 1, 1000, 200, 23, True, 1023)\n"
            "time.sleep(0.1)\n"
            "emit_ultra(sys.argv[1], 2, 1010, 200, 30, True, 1023)\n"
            "time.sleep(1)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.usage_grace_seconds = 0.5
        args.agent_command_json = json.dumps(
            [sys.executable, str(changing_agent), "{usage_output}"]
        )

        result = run_one(args)

        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT", result)
        self.assertFalse(result["scored"], result)
        self.assertIn(
            "exact Ultra token-limit ledger changed",
            result["token_measurement"]["measurement_error"],
        )

    def test_ultra_initial_exact_token_drain_is_sealed_before_first_cleanup_poll(
        self,
    ) -> None:
        release_change = self.root / "release-cap-change"
        changed = self.root / "cap-change-finished"
        racing_agent = self.root / "ultra_cap_exit_race.py"
        racing_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "release_change=Path(sys.argv[2]); changed=Path(sys.argv[3])\n"
            "emit_ultra(sys.argv[1], 1, 1000, 200, 23, True, 1023)\n"
            "while not release_change.exists(): time.sleep(0.001)\n"
            "emit_ultra(sys.argv[1], 2, 1010, 200, 30, True, 1023)\n"
            "changed.write_text('done')\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.usage_grace_seconds = 0.5
        args.agent_command_json = json.dumps(
            [
                sys.executable,
                str(racing_agent),
                "{usage_output}",
                str(release_change),
                str(changed),
            ]
        )
        real_read = read_token_usage
        released = False

        def release_after_initial_read(path: Path) -> dict[str, object] | None:
            nonlocal released
            value = real_read(path)
            if (
                not released
                and value is not None
                and value.get("model_tokens", 0) >= args.token_limit
            ):
                released = True
                release_change.write_text("go", encoding="utf-8")
                deadline = time.monotonic() + 1.0
                while not changed.exists() and time.monotonic() < deadline:
                    time.sleep(0.001)
                self.assertTrue(changed.exists())
                # Let the child exit before the runner's first cleanup poll, so
                # the next read occurs in the exit branch.
                time.sleep(0.05)
            return value

        with mock.patch("runner.read_token_usage", side_effect=release_after_initial_read):
            result = run_one(args)

        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT", result)
        self.assertFalse(result["scored"], result)
        self.assertIn(
            "exact Ultra token-limit ledger changed",
            result["token_measurement"]["measurement_error"],
        )

    def test_ultra_exact_natural_no_submission_is_a_scored_failure(self) -> None:
        no_submission_agent = self.root / "ultra_no_submission.py"
        no_submission_agent.write_text(
            "import sys\n"
            "from trusted_usage import emit_ultra\n"
            "emit_ultra(sys.argv[1], 1, 100, 20, 10, True)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.reasoning_effort = "ultra"
        args.agent_command_json = json.dumps(
            [sys.executable, str(no_submission_agent), "{usage_output}"]
        )
        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)
        validate_mock.assert_not_called()
        self.assert_legacy_ungated_ultra_rejected(result)
        return
        self.assertEqual(result["failure_code"], "NO_SUBMISSION")
        self.assertTrue(result["scored"], result)
        self.assertTrue(result["token_usage"]["tree_quiescent"])
        self.assertFalse(
            result["protocol"]["verified"][
                "authenticated_first_valid_proof_boundary"
            ]
        )

    def test_ultra_boundary_is_required_only_for_an_accepted_proof(self) -> None:
        args = self.args("N")
        args.reasoning_effort = "ultra"

        failure_protocol = {"complete": True, "verified": {}, "notes": []}
        apply_ultra_boundary_deviation(
            failure_protocol,
            args,
            authenticated_boundary_verified=False,
            proof_accepted=False,
        )
        self.assertTrue(failure_protocol["complete"])
        self.assertFalse(
            failure_protocol["verified"][
                "authenticated_first_valid_proof_boundary"
            ]
        )
        self.assertEqual(failure_protocol["notes"], [])

        accepted_protocol = {"complete": True, "verified": {}, "notes": []}
        apply_ultra_boundary_deviation(
            accepted_protocol,
            args,
            authenticated_boundary_verified=False,
            proof_accepted=True,
        )
        self.assertFalse(accepted_protocol["complete"])
        self.assertIn("first-valid-proof", accepted_protocol["notes"][0])

    def test_ultra_stale_barrier_artifact_fails_before_agent_start(self) -> None:
        args = self.args("N")
        args.reasoning_effort = "ultra"
        stale_call = Path(str(args.usage_output) + ".submission-call.json")
        stale_call.parent.mkdir(parents=True, exist_ok=True)
        stale_call.symlink_to("missing-call.json")
        with mock.patch("runner.subprocess.Popen") as popen:
            result = run_one(args)
        popen.assert_not_called()
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertIn("stale submission-barrier", result["failure_note"])

    def test_post_acceptance_grace_captures_delayed_live_usage(self) -> None:
        delayed_agent = self.root / "delayed_agent.py"
        delayed_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(0.15)\n"
            "emit(sys.argv[2], 1, 60, 20, 15)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(delayed_agent), "{submission}", "{usage_output}"]
        )
        args.usage_grace_seconds = 1.0
        result = run_one(args)
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["scored"], result)
        self.assertEqual(result["token_usage"]["model_tokens"], 75)
        capture = result["token_measurement"]["capture_grace"]
        self.assertTrue(capture["attempted"])
        self.assertTrue(capture["usage_captured_during_grace"])
        self.assertGreater(capture["waited_seconds"], 0)
        self.assertEqual(result["scored_elapsed_seconds"], result["first_valid_seconds"])
        self.assertGreater(
            result["actual_stop_seconds"], result["first_valid_seconds"] + 0.05
        )
        self.assertTrue(result["token_measurement"]["post_submission_usage_established"])
        self.assertEqual(capture["captured_notification_sequence"], 1)
        self.assertTrue(Path(result["accepted_submission_log"]).is_file())
        self.assertFalse(result["submission_changed_after_acceptance"])

    def test_first_live_update_over_cap_preempts_submission_validation(self) -> None:
        limiting_agent = self.root / "limiting_agent.py"
        limiting_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit\n"
            "emit(sys.argv[2], 1, 1000, 200, 37)\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(2)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(limiting_agent), "{submission}", "{usage_output}"]
        )
        with mock.patch("runner.validate") as validate_mock:
            result = run_one(args)

        validate_mock.assert_not_called()
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT")
        self.assertTrue(result["protocol"]["complete"], result)
        self.assertTrue(result["scored"])
        self.assertLess(result["actual_stop_seconds"], 1.0)
        enforcement = result["token_measurement"]["limit_enforcement"]
        self.assertEqual(
            enforcement["mode"],
            "first_live_cumulative_update_at_or_above_limit",
        )
        self.assertTrue(enforcement["triggered"])
        self.assertEqual(enforcement["observed_tokens"], 1037)
        self.assertEqual(enforcement["overshoot_tokens"], 37)
        self.assertEqual(enforcement["final_endpoint_tokens"], 1037)
        self.assertNotIn("final_drained_tokens", enforcement)
        self.assertTrue(enforcement["checked_before_submission_validation"])
        self.assertTrue(enforcement["one_response_overshoot_possible"])

    def test_wall_timeout_has_priority_over_final_over_cap_usage(self) -> None:
        timeout_crossing_agent = self.root / "timeout_crossing_agent.py"
        timeout_crossing_agent.write_text(
            "import signal, sys, time\n"
            "from trusted_usage import emit\n"
            "def stopped(_signal, _frame):\n"
            "  emit(sys.argv[1], 1, 1000, 200, 11)\n"
            "  raise SystemExit(0)\n"
            "signal.signal(signal.SIGTERM, stopped)\n"
            "time.sleep(10)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(timeout_crossing_agent), "{usage_output}"]
        )
        args.time_limit_seconds = 0.2
        result = run_one(args)

        self.assertEqual(result["failure_code"], "TIME_LIMIT", result)
        self.assertTrue(result["protocol"]["complete"], result)
        self.assertEqual(
            result["token_measurement"]["limit_enforcement"]["observed_tokens"],
            1011,
        )
        self.assertTrue(
            result["failure_precedence"].startswith("TIME_LIMIT,TOKEN_LIMIT")
        )

    def test_ultra_wall_timeout_is_preserved_as_unscored_lower_bound(self) -> None:
        timeout_agent = self.root / "ultra_timeout_agent.py"
        timeout_agent.write_text(
            "import signal, sys, time\n"
            "from trusted_usage import emit_ultra\n"
            "def stopped(_signal, _frame):\n"
            "  # Even an apparently exact completed-response projection cannot\n"
            "  # attest tokens from the provider response interrupted by SIGTERM.\n"
            "  emit_ultra(sys.argv[1], 1, 100, 20, 11, True)\n"
            "  raise SystemExit(int(sys.argv[2]))\n"
            "signal.signal(signal.SIGTERM, stopped)\n"
            "emit_ultra(sys.argv[1], 1, 100, 20, 11, False)\n"
            "time.sleep(10)\n",
            encoding="utf-8",
        )

        for exit_code in (0, 2):
            with self.subTest(adapter_exit_code=exit_code):
                args = self.args("N")
                args.run_id = f"ultra-timeout-exit-{exit_code}"
                args.reasoning_effort = "ultra"
                args.time_limit_seconds = 0.2
                args.usage_output = (
                    self.root
                    / "logs"
                    / f"ultra-timeout-exit-{exit_code}.usage.json"
                ).resolve()
                args.agent_command_json = json.dumps(
                    [
                        sys.executable,
                        str(timeout_agent),
                        "{usage_output}",
                        str(exit_code),
                    ]
                )
                result = run_one(args)

                self.assert_legacy_ungated_ultra_rejected(result)
                continue
                self.assertFalse(result["pass"], result)
                self.assertFalse(result["scored"], result)
                self.assertEqual(result["failure_code"], "TIME_LIMIT")
                self.assertEqual(result["agent_exit_code"], exit_code)
                self.assertFalse(result["protocol"]["complete"])
                measurement = result["token_measurement"]
                self.assertFalse(measurement["provider_cumulative_total_exact"])
                self.assertIn(
                    "completed-response aggregate is only a lower bound",
                    measurement["measurement_error"],
                )
                if exit_code == 2:
                    self.assertIn(
                        "did not exit cleanly",
                        " ".join(result["protocol"]["notes"]),
                    )

    def test_passing_proof_without_post_submission_usage_is_unscored(self) -> None:
        stale_agent = self.root / "stale_agent.py"
        stale_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit\n"
            "emit(sys.argv[2], 1, 40, 10, 5)\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(2)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(stale_agent), "{submission}", "{usage_output}"]
        )
        args.usage_grace_seconds = 0.1
        result = run_one(args)

        self.assertTrue(result["pass"], result)
        self.assertFalse(result["scored"], result)
        self.assertFalse(result["protocol"]["complete"])
        measurement = result["token_measurement"]
        self.assertFalse(measurement["post_submission_usage_established"])
        self.assertFalse(measurement["capture_grace"]["fresh_update_captured"])

    def test_post_submission_over_cap_update_converts_pass_to_token_limit(self) -> None:
        crossing_agent = self.root / "crossing_agent.py"
        crossing_agent.write_text(
            "from pathlib import Path\n"
            "import sys, time\n"
            "from trusted_usage import emit\n"
            "emit(sys.argv[2], 1, 100, 20, 10)\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(0.15)\n"
            "emit(sys.argv[2], 2, 1000, 200, 23)\n"
            "time.sleep(2)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(crossing_agent), "{submission}", "{usage_output}"]
        )
        args.usage_grace_seconds = 1.0
        result = run_one(args)

        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "TOKEN_LIMIT")
        self.assertTrue(result["protocol"]["complete"], result)
        self.assertTrue(result["scored"])
        self.assertIsNotNone(result["first_valid_seconds"])
        self.assertTrue(Path(result["accepted_submission_log"]).is_file())
        self.assertTrue(result["token_measurement"]["post_submission_usage_established"])
        enforcement = result["token_measurement"]["limit_enforcement"]
        self.assertEqual(enforcement["observed_tokens"], 1023)
        self.assertEqual(enforcement["overshoot_tokens"], 23)
        self.assertEqual(enforcement["final_endpoint_tokens"], 1023)
        self.assertNotIn("final_drained_tokens", enforcement)

    def test_network_attempt_marker_overrides_a_valid_proof(self) -> None:
        violating_agent = self.root / "violating_agent.py"
        violating_agent.write_text(
            "from pathlib import Path\n"
            "import os, sys, time\n"
            "from trusted_usage import emit\n"
            "Path(os.environ['HIGHAMBENCH_NETWORK_VIOLATION_MARKER']).write_bytes(b'N')\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(0.05)\n"
            "emit(sys.argv[2], 1, 30, 10, 12)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(violating_agent), "{submission}", "{usage_output}"]
        )
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertTrue(result["network_violation"]["detected"])
        self.assertTrue(result["network_violation"]["integrity_ok"])
        self.assertEqual(result["network_violation"]["event_count"], 1)
        self.assertGreaterEqual(
            result["network_violation"]["kernel_event_count"], 1
        )
        self.assertIsNotNone(result["first_valid_seconds"])
        self.assertEqual(result["scored_elapsed_seconds"], 5.0)
        self.assertTrue(result["scored"])
        saved = Path(result["network_violation"]["saved_marker_log"])
        self.assertEqual(saved.read_bytes(), b"N")

    def test_truncating_marker_cannot_erase_trusted_kernel_event(self) -> None:
        clearing_agent = self.root / "clearing_agent.py"
        clearing_agent.write_text(
            "from pathlib import Path\n"
            "import os, sys, time\n"
            "from trusted_usage import emit\n"
            "marker = Path(os.environ['HIGHAMBENCH_NETWORK_VIOLATION_MARKER'])\n"
            "marker.write_bytes(b'N')\n"
            "marker.write_bytes(b'')\n"
            f"Path(sys.argv[1]).write_text({SIGNATURE!r})\n"
            "time.sleep(0.05)\n"
            "emit(sys.argv[2], 1, 30, 10, 12)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(clearing_agent), "{submission}", "{usage_output}"]
        )
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertTrue(result["network_violation"]["detected"])
        self.assertFalse(result["network_violation"]["integrity_ok"])
        self.assertIn("later cleared", result["network_violation"]["note"])
        self.assertFalse(result["scored"])

    def test_no_submission_has_priority_over_network_rule_violation(self) -> None:
        self.assertLess(
            FAILURE_PRECEDENCE.index("NO_SUBMISSION"),
            FAILURE_PRECEDENCE.index("RULE_VIOLATION"),
        )
        no_submission_agent = self.root / "no_submission_agent.py"
        no_submission_agent.write_text(
            "from pathlib import Path\n"
            "import os, sys\n"
            "from trusted_usage import emit\n"
            "Path(os.environ['HIGHAMBENCH_NETWORK_VIOLATION_MARKER']).write_bytes(b'N')\n"
            "emit(sys.argv[1], 1, 30, 10, 12)\n",
            encoding="utf-8",
        )
        args = self.args("N")
        args.agent_command_json = json.dumps(
            [sys.executable, str(no_submission_agent), "{usage_output}"]
        )
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "NO_SUBMISSION")
        self.assertTrue(result["useful_work_started"])
        self.assertTrue(result["network_violation"]["detected"])

    def test_agent_startup_failure_remains_a_system_error(self) -> None:
        args = self.args("N")
        args.agent_command_json = json.dumps([str(self.root / "missing-agent")])
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertFalse(result["useful_work_started"])
        self.assertIn("No such file", result["failure_note"])
        self.assertFalse(result["network_violation"]["detected"])

    def test_nonzero_adapter_exit_after_prompt_release_is_useful_work(self) -> None:
        failed_adapter = self.root / "failed_adapter.py"
        failed_adapter.write_text("raise SystemExit(7)\n", encoding="utf-8")
        args = self.args("N")
        args.agent_command_json = json.dumps([sys.executable, str(failed_adapter)])
        result = run_one(args)
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "NO_SUBMISSION")
        self.assertTrue(result["useful_work_started"])
        self.assertEqual(result["agent_exit_code"], 7)
        self.assertIn("without a proof submission", result["failure_note"])
        self.assertIn("before producing", result["agent_system_error"])

    def test_n_preflight_scans_the_staged_controlled_task(self) -> None:
        (self.task / "leaked-context.md").write_text(
            "A forbidden NumStability declaration name is visible.\n", encoding="utf-8"
        )
        write_json(self.manifest, create_manifest(self.task))
        result = run_one(self.args("N"))
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertFalse(result["useful_work_started"])
        self.assertTrue(result["n_preflight"]["filesystem_leaks"])

    def test_system_error_after_agent_start_is_a_charged_final_failure(self) -> None:
        with mock.patch("runner.validate", side_effect=BenchmarkToolError("validator crashed")):
            result = run_one(self.args("N"))
        self.assertFalse(result["pass"], result)
        self.assertEqual(result["failure_code"], "SYSTEM_ERROR")
        self.assertTrue(result["useful_work_started"])
        self.assertTrue(result["scored"])
        self.assertEqual(result["scored_elapsed_seconds"], 5.0)


if __name__ == "__main__":
    unittest.main()
