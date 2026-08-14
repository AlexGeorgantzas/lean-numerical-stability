from __future__ import annotations

import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

from paper_bencmark.highambench.tools.common import BenchmarkToolError
from paper_bencmark.highambench.tools import codex_isolated
from paper_bencmark.highambench.tools import render_report as construction_report
from paper_bencmark.highambench.tools import render_p01_report as report
from paper_bencmark.highambench.tools import run_token_control_canary as token_canary
from paper_bencmark.highambench.tools import run_ultra_orchestration_canary as ultra_canary
from paper_bencmark.highambench.tools import run_matrix
from paper_bencmark.highambench.tools import runner
from paper_bencmark.highambench.tools import validator


_PROVIDER_TRANSPORT_FIXTURE: dict[str, object] | None = None


def provider_transport_fixture() -> dict[str, object]:
    global _PROVIDER_TRANSPORT_FIXTURE
    if _PROVIDER_TRANSPORT_FIXTURE is None:
        _PROVIDER_TRANSPORT_FIXTURE = runner.authenticate_provider_transport_provenance(
            ["/usr/bin/python3.10"]
        )
    return json.loads(json.dumps(_PROVIDER_TRANSPORT_FIXTURE))


def provider_catalog_fixture() -> dict[str, object]:
    codex_raw = shutil.which("codex")
    if codex_raw is None:
        raise AssertionError("fixture requires the installed Codex binary")
    codex_path = Path(codex_raw).resolve()
    return {
        "source": "authenticated_codex_debug_models_bundled",
        "codex_path": str(codex_path),
        "codex_binary_sha256": report.file_sha256(codex_path),
        "catalog_sha256": runner.FROZEN_BUNDLED_MODEL_CATALOG_SHA256,
        "catalog_canonical_bytes": 1000,
        "model_count": 1,
        "matching_model_count": 1,
        "entry_sha256": runner.FROZEN_BUNDLED_MODEL_ENTRY_SHA256,
        "entry_canonical_bytes": 500,
        "slug": "gpt-5.6-sol",
        "context_window": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        "max_context_window": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        "effective_context_window_percent": 95,
        "tool_mode": "code_mode_only",
        "multi_agent_version": "v2",
        "reasoning_effort": "ultra",
        "reasoning_effort_supported": True,
        "response_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
    }


def install_accepted_provider_gate_fixture(
    *,
    usage_path: Path,
    usage: dict[str, object],
    boundary: dict[str, object],
    run_id: str,
    token_limit: int,
    root_thread_id: str,
    turn_id: str,
    response_id: str,
    prompt_release_record: dict[str, object],
    prompt_sha256: str,
    request_published_monotonic_ns: int,
    request_published_unix_ns: int,
    raw_response_monotonic_ns: int,
    raw_response_unix_ns: int,
    close_reason: str = "accepted_submission",
) -> tuple[dict[str, object], dict[str, object], dict[str, object], str]:
    """Attach one sealed accepted or token-crossing production gate fixture."""

    if close_reason not in {"accepted_submission", "token_limit"}:
        raise AssertionError("fixture supports only accepted/token gate endpoints")
    crossed = close_reason == "token_limit"

    gate_paths = runner.provider_gate_paths(usage_path)
    source_path = Path(runner.__file__).resolve().with_name(
        runner.PROVIDER_GATE_IMPLEMENTATION_NAME
    )
    source_sha = report.file_sha256(source_path)
    catalog = provider_catalog_fixture()
    transport = provider_transport_fixture()
    normalized = {
        "input_tokens": int(usage["input_tokens"]),
        "cached_input_tokens": int(usage["cached_input_tokens"]),
        "cache_write_input_tokens": int(usage["cache_write_input_tokens"]),
        "output_tokens": int(usage["output_tokens"]),
        "reasoning_output_tokens": int(usage["reasoning_output_tokens"]),
        "total_tokens": int(usage["total_tokens"]),
    }
    if crossed is not (normalized["total_tokens"] >= token_limit):
        raise AssertionError("fixture token total does not match its gate endpoint")
    raw_provider_usage = {
        "input_tokens": normalized["input_tokens"],
        "input_tokens_details": {
            "cached_tokens": normalized["cached_input_tokens"],
            "cache_write_tokens": normalized["cache_write_input_tokens"],
        },
        "output_tokens": normalized["output_tokens"],
        "output_tokens_details": {
            "reasoning_tokens": normalized["reasoning_output_tokens"]
        },
        "total_tokens": normalized["total_tokens"],
    }
    admitted_mono = raw_response_monotonic_ns - 400_000
    upstream_mono = raw_response_monotonic_ns - 300_000
    commit_mono = raw_response_monotonic_ns - 200_000
    bind_mono = raw_response_monotonic_ns - 100_000
    admitted_unix = raw_response_unix_ns - 400_000
    upstream_unix = raw_response_unix_ns - 300_000
    commit_unix = raw_response_unix_ns - 200_000
    bind_unix = raw_response_unix_ns - 100_000
    sanitized_event = {
        "type": "response.completed",
        "response": {
            "id": response_id,
            "usage": raw_provider_usage,
            "end_turn": True,
            "output": [],
        },
    }
    sanitized_events = [sanitized_event]
    sanitized_body = "".join(
        "event: "
        + str(item["type"])
        + "\ndata: "
        + json.dumps(item, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n\n"
        for item in sanitized_events
    ).encode("utf-8")
    upstream = sanitized_body
    released = sanitized_body if crossed else upstream
    call = {
        "sequence": 3,
        "call_id": "provider-call-00000003",
        "method": "POST",
        "route": "/responses",
        "request_body_sha256": hashlib.sha256(b"fixture request").hexdigest(),
        "request_bytes": len(b"fixture request"),
        "request_model": "gpt-5.6-sol",
        "request_stream": True,
        "request_metadata": {
            "installation_id": "fixture-installation",
            "session_id": "fixture-session",
            "thread_id": root_thread_id,
            "turn_id": turn_id,
            "request_kind": "turn",
            "window_id": "fixture-window",
        },
        "credential_headers_present": ["authorization"],
        "admission_mode": "EXCLUSIVE",
        "response_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        "completed_before": 0,
        "open_before": 0,
        "reserved_before": 0,
        "reservation_after": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        "admitted_unix_ns": admitted_unix,
        "admitted_monotonic_ns": admitted_mono,
        "upstream_started": True,
        "upstream_start_unix_ns": upstream_unix,
        "upstream_start_monotonic_ns": upstream_mono,
        "upstream_status": 200,
        "upstream_content_type_occurrences": 1,
        "upstream_content_type": "text/event-stream; charset=utf-8",
        "upstream_content_encoding_occurrences": 1,
        "upstream_content_encoding": "identity",
        "upstream_sse_authentication": {
            "schema_version": 1,
            "protocol": "highambench-responses-sse-envelope-v1",
            "parser": "highambench-strict-responses-sse-v2",
            "complete": True,
            "content_type_basis": "declared_text_event_stream",
            "content_encoding_basis": "declared_identity",
            "json_event_count": 1,
            "completed_event_index": 0,
            "done_count": 0,
            "body_sha256": hashlib.sha256(upstream).hexdigest(),
            "body_bytes": len(upstream),
            "response_id": response_id,
            "downstream_content_type_synthesized": False,
        },
        "upstream_body_sha256": hashlib.sha256(upstream).hexdigest(),
        "upstream_body_bytes": len(upstream),
        "response_id": response_id,
        "usage": raw_provider_usage,
        "normalized_usage": normalized,
        "previous_total": 0,
        "committed_total": normalized["total_tokens"],
        "commit_unix_ns": commit_unix,
        "commit_monotonic_ns": commit_mono,
        "crossed_cap": crossed,
        "release_kind": (
            runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE
            if crossed
            else "byte_identity"
        ),
        "released_body_sha256": hashlib.sha256(released).hexdigest(),
        "released_body_bytes": len(released),
        "released_sanitized_event": sanitized_event if crossed else None,
        "released_sanitized_events": sanitized_events if crossed else None,
        "released_sanitized_body_utf8": (
            sanitized_body.decode("utf-8") if crossed else None
        ),
        "client_release_complete": True,
        "response_output_manifest": {
            "schema_version": 1,
            "response_id": response_id,
            "output_item_count": 0,
            "action_capable_item_count": 0,
            "items": [],
        },
        "appserver_crossbind": {
            "thread_id": root_thread_id,
            "turn_id": turn_id,
            "event_sequence": 1,
            "normalized_usage": normalized,
            "bind_unix_ns": bind_unix,
            "bind_monotonic_ns": bind_mono,
        },
        "appserver_delivery": {
            "kind": "direct_raw_response",
            "successor_call_id": None,
            "successor_response_id": None,
            "bind_unix_ns": bind_unix,
            "bind_monotonic_ns": bind_mono,
        },
        "error": None,
    }
    close_mono = request_published_monotonic_ns + 100_000
    close_unix = request_published_unix_ns + 100_000
    crossing = (
        {
            "call_id": "provider-call-00000003",
            "response_id": response_id,
            "sequence": 4,
            "previous_total": 0,
            "response_tokens": normalized["total_tokens"],
            "completed_tokens": normalized["total_tokens"],
            "overshoot_tokens": normalized["total_tokens"] - token_limit,
            "commit_unix_ns": commit_unix,
            "commit_monotonic_ns": commit_mono,
            "sole_inflight": True,
            "release_kind": runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
            "request_kind": "turn",
        }
        if crossed
        else None
    )
    terminal_sequence = 5 if crossed else 4
    state = {
        "phase": "CLOSED",
        "completed_tokens": normalized["total_tokens"],
        "close_reason": close_reason,
        "crossing": crossing,
        "crossing_closed": crossed,
        "poison_reasons": [],
        "open_request_ids": [],
        "all_complete": True,
        "no_post_close_upstream": True,
        "poisoned": False,
        "sequence": terminal_sequence,
        "active_handler_count": 0,
        "handlers_quiescent": True,
    }
    release_sha = hashlib.sha256(
        report.canonical_bytes(prompt_release_record) + b"\n"
    ).hexdigest()
    record: dict[str, object] = {
        "schema_version": runner.PROVIDER_GATE_SCHEMA_VERSION,
        "protocol": runner.PROVIDER_GATE_PROTOCOL,
        "implementation": {
            "name": runner.PROVIDER_GATE_IMPLEMENTATION_NAME,
            "version": runner.PROVIDER_GATE_IMPLEMENTATION_VERSION,
            "source_sha256": source_sha,
        },
        "configuration": {
            "token_limit": token_limit,
            "response_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
            "response_bound_enforcement": (
                "runtime_fail_closed_before_buffered_response_release"
            ),
            "model_catalog_sha256": catalog["catalog_sha256"],
            "model_entry_sha256": catalog["entry_sha256"],
            "strict_admission_inequality": (
                "completed_tokens + (open_request_count + 1) * response_bound < token_limit"
            ),
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
            "crossing_release_policy": runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY,
            "upstream_response_contract": {
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
            },
            "transport_provenance": transport,
        },
        "bindings": {
            "root_thread_id": root_thread_id,
            "prompt_release_sha256": release_sha,
            "prompt_release_protocol": prompt_release_record["protocol_version"],
            "prompt_sha256": prompt_sha256,
            "run_id": run_id,
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
        },
        "lifecycle": {
            "started_unix_ns": admitted_unix - 400_000,
            "started_monotonic_ns": admitted_mono - 400_000,
            "stopped_unix_ns": close_unix + 100_000,
            "stopped_monotonic_ns": close_mono + 100_000,
            "finalized_unix_ns": close_unix + 200_000,
            "finalized_monotonic_ns": close_mono + 200_000,
        },
        "state": state,
        "calls": [call],
        "transitions": [
            {
                "sequence": 1,
                "from_phase": "CONCURRENT",
                "to_phase": "DRAINING",
                "reason": "concurrent_reservation_would_reach_limit",
                "call_id": None,
                "unix_ns": admitted_unix - 300_000,
                "monotonic_ns": admitted_mono - 300_000,
            },
            {
                "sequence": 2,
                "from_phase": "DRAINING",
                "to_phase": "EXCLUSIVE",
                "reason": "concurrent_requests_drained",
                "call_id": None,
                "unix_ns": admitted_unix - 200_000,
                "monotonic_ns": admitted_mono - 200_000,
            },
            {
                "sequence": terminal_sequence,
                "from_phase": "EXCLUSIVE",
                "to_phase": "CLOSED",
                "reason": (
                    "first_token_limit_crossing"
                    if crossed
                    else "terminal_close:accepted_submission"
                ),
                "call_id": "provider-call-00000003" if crossed else None,
                "unix_ns": close_unix,
                "monotonic_ns": close_mono,
            },
        ],
        "denials": [],
        "setup_requests": [],
        "invariants": {key: True for key in runner.PROVIDER_GATE_INVARIANT_KEYS},
        "canonical_encoding": runner.PROVIDER_GATE_CANONICAL_ENCODING,
        "sealed_mode": runner.PROVIDER_GATE_SEALED_MODE,
    }
    record["record_sha256"] = hashlib.sha256(
        report.canonical_bytes(record) + b"\n"
    ).hexdigest()
    if gate_paths["final"].exists():
        gate_paths["final"].chmod(0o600)
    write_canonical_json(gate_paths["final"], record)
    gate_paths["final"].chmod(0o444)
    if crossed:
        boundary.pop("provider_gate_close", None)
    else:
        boundary["provider_gate_close"] = {
            "won": True,
            "requested_reason": "accepted_submission",
            "effective_reason": "accepted_submission",
            "phase": "CLOSED",
            "sequence": terminal_sequence,
        }
    usage.update(
        {
            "call_count": 1,
            "provider_response_count": 1,
            "provider_response_ids": [response_id],
            "provider_usage": normalized,
            "appserver_response_count": 1,
            "appserver_response_ids": [response_id],
            "appserver_usage": normalized,
            "suppressed_collaboration_wait_response_count": 0,
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_usage": {
                field: 0 for field in normalized
            },
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_count": 0,
            "superseded_by_collaboration_message_response_ids": [],
            "superseded_by_collaboration_message_usage": {
                field: 0 for field in normalized
            },
            "superseded_by_collaboration_message_evidence": [],
            "discarded_after_explicit_child_interrupt_response_count": 0,
            "discarded_after_explicit_child_interrupt_response_ids": [],
            "discarded_after_explicit_child_interrupt_usage": {
                field: 0 for field in normalized
            },
            "discarded_after_explicit_child_interrupt_evidence": [],
            "provider_usage_reconciliation": {
                "schema_version": codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
                "provider_response_count": 1,
                "appserver_response_count": 1,
                "suppressed_collaboration_wait_response_count": 0,
                "provider_usage": normalized,
                "appserver_usage": normalized,
                "suppressed_collaboration_wait_usage": {
                    field: 0 for field in normalized
                },
                "provider_response_ids": [response_id],
                "appserver_response_ids": [response_id],
                "suppressed_collaboration_wait_response_ids": [],
                "suppressed_collaboration_wait_evidence": [],
                "superseded_by_collaboration_message_response_count": 0,
                "superseded_by_collaboration_message_usage": {
                    field: 0 for field in normalized
                },
                "superseded_by_collaboration_message_response_ids": [],
                "superseded_by_collaboration_message_evidence": [],
                "discarded_after_explicit_child_interrupt_response_count": 0,
                "discarded_after_explicit_child_interrupt_usage": {
                    field: 0 for field in normalized
                },
                "discarded_after_explicit_child_interrupt_response_ids": [],
                "discarded_after_explicit_child_interrupt_evidence": [],
            },
            "appserver_response_ledger": [
                {
                    "response_id": response_id,
                    "thread_id": root_thread_id,
                    "turn_id": turn_id,
                    "raw_response_notification_sequence": 1,
                    "raw_response_observed_at_unix_ns": raw_response_unix_ns,
                    "raw_response_observed_at_monotonic_ns": raw_response_monotonic_ns,
                    "usage": normalized,
                    "provider_gate_call": call,
                }
            ],
            "provider_token_gate": {
                "enabled": True,
                "response_token_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                "artifact_path": str(gate_paths["final"]),
                "record_sha256": record["record_sha256"],
                "final_attached": True,
                "exact_for_usage": True,
                "live": state,
                "terminal": state,
            },
            "adapter_teardown": {
                "process_group_isolated": True,
                "immediate": True,
                "stdin_closed": True,
                "signal": "SIGTERM",
                "returncode": -15,
                "completed": True,
                "started_at_unix_ns": close_unix + 300_000,
                "started_at_monotonic_ns": close_mono + 300_000,
                "completed_at_unix_ns": close_unix + 400_000,
                "completed_at_monotonic_ns": close_mono + 400_000,
            },
            "pending_interrupt_response_count": 0,
        }
    )
    # The adapter artifact keeps its raw structural name; runner.read_token_usage
    # exposes the same rows as appserver_response_ledger after normalization.
    usage["response_ledger"] = json.loads(
        json.dumps(usage["appserver_response_ledger"])
    )
    return record, catalog, transport, source_sha


def upgrade_token_gate_to_two_call_compaction_fixture(
    *,
    usage_path: Path,
    usage: dict[str, object],
    record: dict[str, object],
    token_limit: int,
) -> dict[str, object]:
    """Match the V6 token canary: below-cap turn, then compaction crossing."""

    calls = record["calls"]
    if not isinstance(calls, list) or len(calls) != 1:
        raise AssertionError("token gate upgrade requires one crossing call")
    crossing_call = json.loads(json.dumps(calls[0]))
    total_input = int(usage["input_tokens"])
    total_output = int(usage["output_tokens"])
    total_cached = int(usage["cached_input_tokens"])
    total_cache_write = int(usage["cache_write_input_tokens"])
    total_reasoning = int(usage["reasoning_output_tokens"])
    below = {
        "input_tokens": 400,
        "cached_input_tokens": 40,
        "cache_write_input_tokens": 10,
        "output_tokens": 100,
        "reasoning_output_tokens": 20,
        "total_tokens": 500,
    }
    crossing_usage = {
        "input_tokens": total_input - below["input_tokens"],
        "cached_input_tokens": total_cached - below["cached_input_tokens"],
        "cache_write_input_tokens": total_cache_write
        - below["cache_write_input_tokens"],
        "output_tokens": total_output - below["output_tokens"],
        "reasoning_output_tokens": total_reasoning
        - below["reasoning_output_tokens"],
        "total_tokens": total_input + total_output - below["total_tokens"],
    }
    if not 0 < below["total_tokens"] < token_limit <= (
        below["total_tokens"] + crossing_usage["total_tokens"]
    ):
        raise AssertionError("two-call token fixture does not cross exactly once")

    def raw_provider(normalized: dict[str, int]) -> dict[str, object]:
        return {
            "input_tokens": normalized["input_tokens"],
            "input_tokens_details": {
                "cached_tokens": normalized["cached_input_tokens"],
                "cache_write_tokens": normalized["cache_write_input_tokens"],
            },
            "output_tokens": normalized["output_tokens"],
            "output_tokens_details": {
                "reasoning_tokens": normalized["reasoning_output_tokens"]
            },
            "total_tokens": normalized["total_tokens"],
        }

    second_response_id = str(crossing_call["response_id"])
    first_response_id = second_response_id + "-below"
    compaction_turn_id = str(crossing_call["request_metadata"]["turn_id"]) + "-compaction"
    original_admit_mono = int(crossing_call["admitted_monotonic_ns"])
    original_admit_unix = int(crossing_call["admitted_unix_ns"])
    first_completed_event = {
        "type": "response.completed",
        "response": {
            "id": first_response_id,
            "usage": raw_provider(below),
        },
    }
    first_upstream = (
        "event: response.completed\ndata: "
        + json.dumps(
            first_completed_event,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        + "\n\n"
    ).encode("utf-8")
    first_call = json.loads(json.dumps(crossing_call))
    first_call.update(
        {
            "sequence": 3,
            "call_id": "provider-call-00000003",
            "request_metadata": {
                **first_call["request_metadata"],
                "request_kind": "turn",
            },
            "completed_before": 0,
            "open_before": 0,
            "reserved_before": 0,
            "reservation_after": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
            "admitted_monotonic_ns": original_admit_mono - 800_000,
            "upstream_start_monotonic_ns": original_admit_mono - 700_000,
            "commit_monotonic_ns": original_admit_mono - 600_000,
            "admitted_unix_ns": original_admit_unix - 800_000,
            "upstream_start_unix_ns": original_admit_unix - 700_000,
            "commit_unix_ns": original_admit_unix - 600_000,
            "response_id": first_response_id,
            "response_output_manifest": {
                **first_call["response_output_manifest"],
                "response_id": first_response_id,
            },
            "usage": raw_provider(below),
            "normalized_usage": below,
            "previous_total": 0,
            "committed_total": below["total_tokens"],
            "crossed_cap": False,
            "release_kind": "byte_identity",
            "upstream_body_sha256": hashlib.sha256(first_upstream).hexdigest(),
            "upstream_body_bytes": len(first_upstream),
            "upstream_sse_authentication": {
                **first_call["upstream_sse_authentication"],
                "json_event_count": 1,
                "completed_event_index": 0,
                "done_count": 0,
                "body_sha256": hashlib.sha256(first_upstream).hexdigest(),
                "body_bytes": len(first_upstream),
                "response_id": first_response_id,
            },
            "released_body_sha256": hashlib.sha256(first_upstream).hexdigest(),
            "released_body_bytes": len(first_upstream),
            "released_sanitized_event": None,
            "released_sanitized_events": None,
            "released_sanitized_body_utf8": None,
            "appserver_crossbind": {
                **first_call["appserver_crossbind"],
                "event_sequence": 1,
                "normalized_usage": below,
                "bind_monotonic_ns": original_admit_mono - 550_000,
                "bind_unix_ns": original_admit_unix - 550_000,
            },
            "appserver_delivery": {
                **first_call["appserver_delivery"],
                "bind_monotonic_ns": original_admit_mono - 550_000,
                "bind_unix_ns": original_admit_unix - 550_000,
            },
        }
    )
    crossing_call.update(
        {
            "sequence": 4,
            "call_id": "provider-call-00000004",
            "request_metadata": {
                **crossing_call["request_metadata"],
                "request_kind": "compaction",
                "turn_id": compaction_turn_id,
            },
            "completed_before": below["total_tokens"],
            "open_before": 0,
            "reserved_before": below["total_tokens"],
            "reservation_after": (
                below["total_tokens"] + runner.PROVIDER_RESPONSE_TOKEN_BOUND
            ),
            "usage": raw_provider(crossing_usage),
            "normalized_usage": crossing_usage,
            "previous_total": below["total_tokens"],
            "committed_total": below["total_tokens"]
            + crossing_usage["total_tokens"],
            "appserver_crossbind": {
                **crossing_call["appserver_crossbind"],
                "turn_id": compaction_turn_id,
                "event_sequence": 2,
                "normalized_usage": crossing_usage,
            },
        }
    )
    completed_event = {
        "type": "response.completed",
        "response": {
            "id": second_response_id,
            "usage": crossing_call["usage"],
            "end_turn": True,
            "output": [],
        },
    }
    compaction_events = [
        {
            "type": "response.output_item.done",
            "item": {
                "type": "compaction",
                "encrypted_content": "opaque-fixture-compaction",
            },
        },
        completed_event,
    ]
    compaction_body = "".join(
        "event: "
        + str(item["type"])
        + "\ndata: "
        + json.dumps(item, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n\n"
        for item in compaction_events
    ).encode("utf-8")
    crossing_call.update(
        {
            "upstream_body_sha256": hashlib.sha256(compaction_body).hexdigest(),
            "upstream_body_bytes": len(compaction_body),
            "upstream_sse_authentication": {
                **crossing_call["upstream_sse_authentication"],
                "json_event_count": 2,
                "completed_event_index": 1,
                "done_count": 0,
                "body_sha256": hashlib.sha256(compaction_body).hexdigest(),
                "body_bytes": len(compaction_body),
                "response_id": second_response_id,
            },
            "release_kind": runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            "released_body_sha256": hashlib.sha256(compaction_body).hexdigest(),
            "released_body_bytes": len(compaction_body),
            "released_sanitized_event": completed_event,
            "released_sanitized_events": compaction_events,
            "released_sanitized_body_utf8": compaction_body.decode("utf-8"),
        }
    )
    crossing = record["state"]["crossing"]
    crossing.update(
        {
            "call_id": crossing_call["call_id"],
            "sequence": 5,
            "previous_total": below["total_tokens"],
            "response_tokens": crossing_usage["total_tokens"],
            "completed_tokens": crossing_call["committed_total"],
            "overshoot_tokens": int(crossing_call["committed_total"])
            - token_limit,
            "release_kind": runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            "request_kind": "compaction",
        }
    )
    record["state"]["sequence"] = 6
    record["calls"] = [first_call, crossing_call]
    record["lifecycle"]["started_monotonic_ns"] = original_admit_mono - 1_100_000
    record["lifecycle"]["started_unix_ns"] = original_admit_unix - 1_100_000
    record["transitions"][0]["monotonic_ns"] = original_admit_mono - 1_000_000
    record["transitions"][0]["unix_ns"] = original_admit_unix - 1_000_000
    record["transitions"][1]["monotonic_ns"] = original_admit_mono - 900_000
    record["transitions"][1]["unix_ns"] = original_admit_unix - 900_000
    record["transitions"][-1].update(
        {
            "sequence": 6,
            "call_id": crossing_call["call_id"],
        }
    )
    record.pop("record_sha256", None)
    record["record_sha256"] = hashlib.sha256(
        report.canonical_bytes(record) + b"\n"
    ).hexdigest()
    gate_path = runner.provider_gate_paths(usage_path)["final"]
    gate_path.chmod(0o600)
    write_canonical_json(gate_path, record)
    gate_path.chmod(0o444)
    first_observed_mono = int(first_call["appserver_crossbind"]["bind_monotonic_ns"]) + 1
    first_observed_unix = int(first_call["appserver_crossbind"]["bind_unix_ns"]) + 1
    prior_ledger = usage["appserver_response_ledger"]
    if not isinstance(prior_ledger, list) or len(prior_ledger) != 1:
        raise AssertionError("token gate upgrade requires one response ledger row")
    second_row = prior_ledger[0]
    second_row.update(
        {
            "turn_id": compaction_turn_id,
            "raw_response_notification_sequence": 2,
            "usage": crossing_usage,
            "provider_gate_call": crossing_call,
        }
    )
    usage.update(
        {
            "response_count": 2,
            "call_count": 2,
            "notification_sequence": 2,
            "response_ids": [first_response_id, second_response_id],
            "provider_response_count": 2,
            "provider_response_ids": [first_response_id, second_response_id],
            "provider_usage": {
                field: below[field] + crossing_usage[field] for field in below
            },
            "appserver_response_count": 2,
            "appserver_response_ids": [first_response_id, second_response_id],
            "appserver_usage": {
                field: below[field] + crossing_usage[field] for field in below
            },
            "suppressed_collaboration_wait_response_count": 0,
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_usage": {field: 0 for field in below},
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_count": 0,
            "superseded_by_collaboration_message_response_ids": [],
            "superseded_by_collaboration_message_usage": {field: 0 for field in below},
            "superseded_by_collaboration_message_evidence": [],
            "discarded_after_explicit_child_interrupt_response_count": 0,
            "discarded_after_explicit_child_interrupt_response_ids": [],
            "discarded_after_explicit_child_interrupt_usage": {field: 0 for field in below},
            "discarded_after_explicit_child_interrupt_evidence": [],
            "appserver_response_ledger": [
                {
                    "response_id": first_response_id,
                    "thread_id": first_call["request_metadata"]["thread_id"],
                    "turn_id": first_call["request_metadata"]["turn_id"],
                    "raw_response_notification_sequence": 1,
                    "raw_response_observed_at_unix_ns": first_observed_unix,
                    "raw_response_observed_at_monotonic_ns": first_observed_mono,
                    "usage": below,
                    "provider_gate_call": first_call,
                },
                second_row,
            ],
            "first_crossing": {
                "response_id": second_response_id,
                "notification_sequence": 2,
                "observed_at_unix_ns": second_row[
                    "raw_response_observed_at_unix_ns"
                ],
                "tokens": crossing_call["committed_total"],
                "active_thread_ids": [],
            },
        }
    )
    usage["provider_usage_reconciliation"] = {
        "schema_version": codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        "provider_response_count": 2,
        "appserver_response_count": 2,
        "suppressed_collaboration_wait_response_count": 0,
        "provider_usage": usage["provider_usage"],
        "appserver_usage": usage["appserver_usage"],
        "suppressed_collaboration_wait_usage": usage[
            "suppressed_collaboration_wait_usage"
        ],
        "provider_response_ids": usage["provider_response_ids"],
        "appserver_response_ids": usage["appserver_response_ids"],
        "suppressed_collaboration_wait_response_ids": [],
        "suppressed_collaboration_wait_evidence": [],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_usage": usage[
            "superseded_by_collaboration_message_usage"
        ],
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_usage": usage[
            "discarded_after_explicit_child_interrupt_usage"
        ],
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_evidence": [],
    }
    usage["response_ledger"] = json.loads(
        json.dumps(usage["appserver_response_ledger"])
    )
    usage["provider_token_gate"]["record_sha256"] = record["record_sha256"]
    usage["provider_token_gate"]["live"] = record["state"]
    usage["provider_token_gate"]["terminal"] = record["state"]
    return record


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def write_canonical_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report.canonical_bytes(value) + b"\n")


def write_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


def descriptor(path: Path, relative: str) -> dict[str, object]:
    return {
        "path": relative,
        "sha256": report.file_sha256(path),
        "bytes": path.stat().st_size,
    }


def token_canary_prompt_release_summary() -> dict[str, object]:
    released = 1_000_000_000
    wall = 300
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
                "path": f"/trusted/logs/token.prompt-{label}.json",
                "file_sha256": character * 64,
                "record_sha256": character * 64,
            }
            for label, character in (("ready", "1"), ("go", "2"), ("release", "3"))
        },
        "canonical_encoding": "compact_sorted_key_utf8_json_newline",
        "sealed_mode": "0444",
        "handshake_nonce": "4" * 64,
        "root_thread_id": "synthetic-root",
        "effective_prompt_sha256": "5" * 64,
        "effective_prompt_bytes": 123,
        "turn_start_request_sha256": "6" * 64,
        "turn_start_wire_verified": True,
        "command_binding_verified": True,
        "root_identity_verified": True,
        "ready_sha256": "7" * 64,
        "go_sha256": "8" * 64,
        "release_sha256": "9" * 64,
        "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
        "released_at_monotonic_ns": released,
        "deadline_monotonic_ns": released + wall * 1_000_000_000,
        "deadline_derivation": (
            "released_at_monotonic_ns + wall_time_seconds*1000000000"
        ),
        "wall_time_seconds": wall,
        "actual_stop_seconds": 10.0,
        "token_crossing_within_deadline": True,
        "first_valid_seconds": None,
        "submission_boundary": None,
        "sanitized_provider_gate_crossing": True,
        "top_level_artifact_count_unchanged": len(token_canary.ARTIFACT_LABELS),
    }


def token_canary_projection_fixture(
    *,
    record_sha256: str = "a" * 64,
    response_ids: list[str] | None = None,
    provider_usage_reconciliation: dict[str, object],
) -> dict[str, object]:
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
    projection: dict[str, object] = {
        "accounting_projection_schema_version": (
            token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "provider_gate_protocol": runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": record_sha256,
        "provider_gate_close_reason": "token_limit",
        "provider_gate_response_ids": (
            ["token-below", "token-crossing"]
            if response_ids is None
            else response_ids
        ),
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": provider_usage_reconciliation,
        "provider_gate_setup_requests_empty": True,
        "provider_requests_quiescent": True,
        "adapter_teardown_complete": True,
        "spawn_binding_source": ultra_canary.SPAWN_BINDING_SOURCE,
        "root_thread_id": "synthetic-root",
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
            **codex_isolated.ultra_fork_policy_static_record(),
            "call_evidence": [],
            "complete": True,
        },
        "accounting_complete": False,
        "root_only": True,
    }
    projection["projection_payload_sha256"] = report.document_sha256(projection)
    return projection


def ultra_canary_prompt_release_summary() -> dict[str, object]:
    released = 1_000_000_000
    return {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "authenticated": True,
        "timing_exact": True,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "startup_timeout_seconds": 120,
        "artifact_count": 3,
        "artifacts_reauthenticated": True,
        "released_at_monotonic_ns": released,
        "measurement_deadline_monotonic_ns": released + 300_000_000_000,
        "request_published_at_monotonic_ns": released + 1_000_000,
        "request_publication_timing_verified": True,
    }


def ultra_canary_projection_fixture(
    *,
    record_sha256: str = "b" * 64,
    response_ids: list[str] | None = None,
    provider_usage_reconciliation: dict[str, object],
) -> dict[str, object]:
    static = codex_isolated.ultra_fork_policy_static_record()
    allowed_id = "call_allowed_root"
    blocked_ids = ["call_blocked_child", "call_blocked_root"]

    def call(
        call_id: str,
        *,
        parent: str,
        turn_id: str,
        response_id: str,
        allowed: bool,
    ) -> dict[str, object]:
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
            "hook_run_id": f"pre-tool-use:0:{static['source_path']}:{call_id}",
            "hook_source_path": static["source_path"],
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
                else codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
            ),
            "resolution_status": (
                "resolved_child"
                if allowed
                else codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
            ),
            "child_activity_observed": allowed,
        }

    return {
        "accounting_projection_schema_version": (
            ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "provider_gate_protocol": runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": record_sha256,
        "provider_gate_close_reason": "accepted_submission",
        "provider_gate_response_ids": (
            ["ultra-canary-response"] if response_ids is None else response_ids
        ),
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": provider_usage_reconciliation,
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
        "fork_policy_complete": True,
        "fork_policy": {
            **static,
            "call_evidence": [
                call(
                    allowed_id,
                    parent="root",
                    turn_id="root-turn",
                    response_id="root-response",
                    allowed=True,
                ),
                call(
                    "call_blocked_child",
                    parent="child",
                    turn_id="child-turn",
                    response_id="child-blocked-response",
                    allowed=False,
                ),
                call(
                    "call_blocked_root",
                    parent="root",
                    turn_id="root-turn",
                    response_id="root-blocked-response",
                    allowed=False,
                ),
            ],
            "complete": True,
        },
        "thread_accounting": [{"thread_id": "child"}, {"thread_id": "root"}],
    }


def nested_submission_wire_fixture(
    index: int = 0,
    *,
    outer_observed_ns: int = 8,
    inner_started_ns: int = 9,
) -> dict[str, object]:
    """Return the frozen outer-exec/inner-submit identity used by test evidence."""

    return {
        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
        "candidate_path": "Candidate.lean",
        "call_id": f"inner-submit-call-{index}",
        "submission_transport": codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
        "outer_raw_item_id": f"outer-raw-item-{index}",
        "outer_raw_item_type": "custom_tool_call",
        "outer_exec_name": "exec",
        "outer_exec_call_id": f"outer-exec-call-{index}",
        "outer_exec_program": codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
        "outer_exec_program_bytes": codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
        "outer_exec_program_sha256": (
            codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        ),
        **codex_isolated.nested_submission_exec_yield_record(),
        "outer_raw_item_observed_at_monotonic_ns": outer_observed_ns,
        "inner_dynamic_item_started_at_monotonic_ns": inner_started_ns,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "inner_dynamic_call_id": f"inner-submit-call-{index}",
        "inner_dynamic_tool_name": "submit_proof",
        "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
    }


class SyntheticP01Fixture:
    def __init__(self, root: Path) -> None:
        self.project = root
        self.benchmark = root / "paper_bencmark" / "highambench"
        self.metadata = self.benchmark / "metadata"
        self.results = self.benchmark / "scratch_pad" / "p01-results"
        self.output = root / "report-output"
        self.benchmark_id = "synthetic-highambench-20-paper-freeze"
        self.token_limit = 5_000_000
        self.wall_limit = 1800
        self.prompt_startup_timeout = 120.0
        self.agent = {
            "id": "codex-cli",
            "version": "0.146.0-alpha.9.2",
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
        }
        self.agent_binary_sha = "a" * 64
        self.host_class = {
            "cpu_vendor": "GenuineIntel",
            "processor": "Synthetic Xeon",
            "cpu_family": 6,
            "cpu_model": 143,
            "cpu_stepping": 8,
            "kernel": "Linux synthetic x86_64",
            "virtualization": "LXC",
            "online_logical_cpus": 4,
            "allocated_physical_cores": 2,
            "allocated_sockets": 1,
            "allocated_threads_per_core": [2, 2],
            "visible_memory_bytes": 900_000_000_000,
            "allocation_memory_limit_bytes": 34_359_738_368,
            "slurm_num_nodes": 1,
            "slurm_num_cpus": 4,
            "slurm_num_tasks": 1,
            "slurm_cpus_per_task": 4,
            "slurm_allocated_memory_bytes": 34_359_738_368,
        }
        self._build()

    def _build(self) -> None:
        self.metadata.mkdir(parents=True)
        self.results.mkdir(parents=True)
        self.python_executable = Path("/usr/bin/python3.10").resolve()
        self.toolchain_root = (self.project / "synthetic-toolchain").resolve()
        self.packages_runtime_root = (self.project / "synthetic-packages").resolve()
        self.shared_olean_root = (self.project / "synthetic-shared-olean" / "P01").resolve()
        self.library_source_root = (self.project / "NumStability").resolve()
        self.library_root_file = (self.project / "NumStability.lean").resolve()
        self.library_olean_root = (self.project / "synthetic-library-olean").resolve()
        write_text(self.toolchain_root / "bin" / "lean", "synthetic Lean binary\n")
        write_text(
            self.packages_runtime_root / "mathlib" / "Mathlib.lean",
            "import Mathlib\n",
        )
        write_text(self.shared_olean_root / "HighamBench" / "Core.olean", "core\n")
        write_text(
            self.shared_olean_root / "HighamBench" / "P01Definitions.olean",
            "p01 definitions\n",
        )
        write_text(self.library_source_root / "Basic.lean", "namespace NumStability\nend NumStability\n")
        write_text(self.library_root_file, "import NumStability.Basic\n")
        write_text(self.library_olean_root / "NumStability" / "Basic.olean", "basic\n")
        source_files = [self.library_root_file] + sorted(
            path for path in self.library_source_root.rglob("*") if path.is_file()
        )
        self.library_source_manifest_path = self.metadata / "library_source.json"
        write_json(
            self.library_source_manifest_path,
            {
                "schema_version": 1,
                "kind": "highambench-controlled-files",
                "label": "synthetic-numstability-source",
                "files": [
                    descriptor(path, path.relative_to(self.project).as_posix())
                    for path in source_files
                ],
            },
        )
        compiled_files = sorted(
            path for path in self.library_olean_root.rglob("*") if path.is_file()
        )
        self.library_compiled_manifest_path = self.metadata / "library_olean.json"
        write_json(
            self.library_compiled_manifest_path,
            {
                "schema_version": 1,
                "kind": "highambench-controlled-files",
                "label": "synthetic-numstability-compiled",
                "files": [
                    descriptor(path, path.relative_to(self.library_olean_root).as_posix())
                    for path in compiled_files
                ],
            },
        )
        packages_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "synthetic-packages-runtime",
            "files": [
                descriptor(
                    self.packages_runtime_root / "mathlib" / "Mathlib.lean",
                    "mathlib/Mathlib.lean",
                )
            ],
        }
        self.packages_manifest_path = self.metadata / "packages_runtime.json"
        write_json(self.packages_manifest_path, packages_manifest)
        compiled_summary = {
            "schema_version": 1,
            "kind": "highambench-compiled-environment-summary",
            "toolchain": {
                "relative_root": ".",
                **run_matrix.exact_tree_digest(self.toolchain_root),
            },
            "packages": [],
        }
        self.compiled_summary_path = self.metadata / "packages_olean.json"
        write_json(self.compiled_summary_path, compiled_summary)
        self.shared_olean_bundle = {
            path.relative_to(self.shared_olean_root).as_posix(): report.file_sha256(path)
            for path in sorted(self.shared_olean_root.rglob("*"))
            if path.is_file()
        }
        common = self.benchmark / "agent_prompt.md"
        supplement = self.benchmark / "condition_prompts" / "L.md"
        write_text(common, "Prove the fixed theorem in Candidate.lean.\n")
        write_text(
            supplement,
            "You may import and use the mounted NumStability snapshot. Search it with "
            "rg or find under /library/NumStability and /library/NumStability.lean; "
            "compiled modules are at /library-olean.\n",
        )
        common_record = descriptor(common, "agent_prompt.md")
        supplement_record = descriptor(supplement, "condition_prompts/L.md")
        self.production_prompt_protocol = {
            "version": "signposted-library-v1",
            "composition_order": [
                "common_prompt",
                "condition_L_supplement_if_condition_L",
                "task_context",
                "fixed_target",
            ],
            "N_receives_condition_supplement": False,
            "relevant_theorem_or_module_hints_supplied": False,
            "common_prompt": common_record,
            "condition_supplements": {"L": supplement_record},
        }
        self.execution_components = {
            field: hashlib.sha256(f"synthetic-{field}".encode()).hexdigest()
            for field in run_matrix.EXECUTION_COMPONENT_FIELDS
        }

        papers: list[dict[str, object]] = []
        task_ids: list[str] = []
        release_paths: list[Path] = [
            self.packages_manifest_path,
            self.compiled_summary_path,
            self.library_source_manifest_path,
            self.library_compiled_manifest_path,
        ]
        for paper_index in range(1, 21):
            paper_id = f"P{paper_index:02d}"
            targets: list[dict[str, object]] = []
            for tier_index in range(1, 4):
                tier = f"T{tier_index}"
                task_id = f"{paper_id}-{tier}"
                task_ids.append(task_id)
                target = self.benchmark / "tasks" / paper_id / tier / "Target.lean"
                context = self.benchmark / "tasks" / paper_id / tier / "context.md"
                write_text(
                    target,
                    f"import HighamBench.Core\nnamespace HighamBench\ntheorem synthetic_{paper_id.lower()}_{tier.lower()} : True := by trivial\nend HighamBench\n",
                )
                write_text(context, f"Synthetic context for {task_id}.\n")
                release_paths.extend((target, context))
                targets.append(
                    {
                        "task_id": task_id,
                        "tier": tier,
                        "title": f"Synthetic {task_id}",
                        "lean_target": {
                            "file": target.relative_to(self.project).as_posix(),
                            "controlled_file_sha256": report.file_sha256(target),
                            "declaration": f"synthetic_{paper_id.lower()}_{tier.lower()}",
                        },
                    }
                )
                controlled = {
                    "files": [
                        descriptor(
                            target,
                            target.relative_to(self.benchmark).as_posix(),
                        ),
                        descriptor(
                            context,
                            context.relative_to(self.benchmark).as_posix(),
                        ),
                    ]
                }
                controlled_path = self.metadata / "controlled" / f"{task_id}.json"
                write_json(controlled_path, controlled)
                release_paths.append(controlled_path)
            papers.append(
                {
                    "paper_id": paper_id,
                    "source": {"sha256": hashlib.sha256(paper_id.encode()).hexdigest()},
                    "targets": targets,
                }
            )
        specification = self.benchmark / "scratch_pad" / "HighamBench_Simple_Two_Condition_Specification.pdf"
        specification.parent.mkdir(parents=True, exist_ok=True)
        specification.write_bytes(b"%PDF-1.4\n% synthetic four-page v0.2 specification\n")
        manifest = {
            "schema_version": 1,
            "benchmark_id": self.benchmark_id,
            "specification": {
                "version": "0.2",
                "title": "Synthetic HighamBench Two-Condition Specification",
                "pdf_pages": 4,
                "local_path": specification.relative_to(self.project).as_posix(),
                "sha256": report.file_sha256(specification),
            },
            "papers": papers,
        }
        manifest_path = self.metadata / "manifest.json"
        write_json(manifest_path, manifest)

        salt = "synthetic-p01-order"
        pairs: list[dict[str, object]] = []
        for task_id in task_ids:
            for repetition in report.EXPECTED_REPETITIONS:
                digest = hashlib.sha256(f"{salt}|{task_id}|{repetition}".encode()).hexdigest()
                order = ["N", "L"] if int(digest[:2], 16) % 2 == 0 else ["L", "N"]
                pair_id = f"{task_id}-{repetition}"
                pairs.append(
                    {
                        "pair_id": pair_id,
                        "task_id": task_id,
                        "repetition_id": repetition,
                        "condition_order": order,
                        "run_ids": [f"{pair_id}-{condition}" for condition in order],
                        "sha256": digest,
                    }
                )
        run_order = {
            "schema_version": 1,
            "benchmark_id": self.benchmark_id,
            "method": {"name": "sha256_first_byte_parity", "salt": salt},
            "pairs": pairs,
        }
        run_order_path = self.metadata / "run_order.json"
        write_json(run_order_path, run_order)

        self._construction(manifest, task_ids)

        token_descriptor = self._canary("token")
        ultra_descriptor = self._canary("ultra")
        review_override = self._reviews(manifest_path, task_ids)
        release_paths.extend((common, supplement, manifest_path, run_order_path))
        release = {
            "schema_version": 1,
            "kind": "synthetic-release",
            "files": [
                descriptor(path, path.relative_to(self.benchmark).as_posix())
                for path in sorted(set(release_paths))
            ],
        }
        release_path = self.metadata / "release_files.json"
        write_json(release_path, release)
        release_sha = report.file_sha256(release_path)

        token_control = {
            "measurement_source": runner.ULTRA_USAGE_MEASUREMENT_SOURCE,
            "notification": runner.ULTRA_USAGE_NOTIFICATION,
            "usage_scope": runner.ULTRA_USAGE_SCOPE,
            "live_cumulative": True,
            "input_includes_cached": True,
            "limit_tokens": self.token_limit,
        }
        prompt_protocol = self.production_prompt_protocol
        ultra_orchestration = {"enabled": True, "max_concurrent_threads_per_session": 4}
        config = {
            "schema_version": 1,
            "benchmark_id": self.benchmark_id,
            "repetitions": [
                {"id": repetition, "backend_seed": None}
                for repetition in report.EXPECTED_REPETITIONS
            ],
            "limits": {
                "wall_clock_seconds": self.wall_limit,
                "failure_scored_time_seconds": self.wall_limit,
                "total_model_tokens": self.token_limit,
                "prompt_startup_timeout_seconds": self.prompt_startup_timeout,
                "post_submission_validation_reserve_seconds": (
                    report.POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
                ),
            },
            "token_control": token_control,
            "private_measurement_review_override": review_override,
            "frozen_environment": {
                "agent_id": self.agent["id"],
                "agent_version": self.agent["version"],
                "agent_binary_sha256": self.agent_binary_sha,
                "model_version": self.agent["model"],
                "model_reasoning_effort": self.agent["reasoning_effort"],
                "python_version": "3.10.synthetic",
                "python_binary_sha256": report.file_sha256(self.python_executable),
                "lean_binary_sha256": report.file_sha256(
                    self.toolchain_root / "bin" / "lean"
                ),
                "compiled_environment_summary": self.compiled_summary_path.relative_to(
                    self.project
                ).as_posix(),
                "compiled_environment_summary_sha256": report.file_sha256(
                    self.compiled_summary_path
                ),
                "packages_runtime_manifest": self.packages_manifest_path.relative_to(
                    self.project
                ).as_posix(),
                "packages_runtime_manifest_sha256": report.file_sha256(
                    self.packages_manifest_path
                ),
                "numstability_source_manifest": self.library_source_manifest_path.relative_to(
                    self.project
                ).as_posix(),
                "numstability_source_manifest_sha256": report.file_sha256(
                    self.library_source_manifest_path
                ),
                "numstability_compiled_manifest": self.library_compiled_manifest_path.relative_to(
                    self.project
                ).as_posix(),
                "numstability_compiled_manifest_sha256": report.file_sha256(
                    self.library_compiled_manifest_path
                ),
                "ultra_orchestration": ultra_orchestration,
                "prompt_protocol": prompt_protocol,
                "release_manifest_sha256": release_sha,
                "token_control_canary": token_descriptor,
                "ultra_orchestration_canary": ultra_descriptor,
                "environment_id": "pending",
                "environment_bundle_sha256": "pending",
            },
        }
        environment = {
            "schema_version": 1,
            "benchmark_id": self.benchmark_id,
            "agent": {**self.agent, "prompt_protocol": prompt_protocol},
            "host_class": self.host_class,
            "isolation": dict(self.execution_components),
            "runtime": {
                "prompt_startup_timeout_seconds": self.prompt_startup_timeout,
                "post_submission_validation_reserve_seconds": (
                    report.POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
                ),
                "python": {
                    "version": "3.10.synthetic",
                    "binary_sha256": report.file_sha256(self.python_executable),
                },
                "packages_runtime_manifest": self.packages_manifest_path.relative_to(
                    self.project
                ).as_posix(),
                "packages_runtime_manifest_sha256": report.file_sha256(
                    self.packages_manifest_path
                ),
            },
            "lean": {
                "binary_sha256": report.file_sha256(
                    self.toolchain_root / "bin" / "lean"
                ),
                "compiled_environment_summary": self.compiled_summary_path.relative_to(
                    self.project
                ).as_posix(),
                "compiled_environment_summary_sha256": report.file_sha256(
                    self.compiled_summary_path
                ),
                "shared_olean_bundles": {"P01": self.shared_olean_bundle},
                "numstability_source_manifest": self.library_source_manifest_path.relative_to(
                    self.project
                ).as_posix(),
                "numstability_source_manifest_sha256": report.file_sha256(
                    self.library_source_manifest_path
                ),
                "numstability_compiled_manifest": self.library_compiled_manifest_path.relative_to(
                    self.project
                ).as_posix(),
                "numstability_compiled_manifest_sha256": report.file_sha256(
                    self.library_compiled_manifest_path
                ),
            },
            "release_manifest_sha256": release_sha,
            "token_control": token_control,
            "token_control_canary": token_descriptor,
            "ultra_orchestration_canary": ultra_descriptor,
            "environment_id": "pending",
            "environment_bundle_sha256": "pending",
            "known_reference_protocol_deviations": [
                "Condition L receives the frozen signposted-library-v1 supplement while "
                "condition N does not. This user-directed treatment intentionally departs "
                "from the reference PDF's identical-prompt rule and is kept separate from "
                "the earlier raw-access P01 measurements."
            ],
        }
        bundle = report.environment_bundle_sha256(config, environment)
        environment_id = f"synthetic-p01-{bundle[:16]}"
        config["frozen_environment"]["environment_id"] = environment_id  # type: ignore[index]
        config["frozen_environment"]["environment_bundle_sha256"] = bundle  # type: ignore[index]
        environment["environment_id"] = environment_id
        environment["environment_bundle_sha256"] = bundle
        config_path = self.metadata / "config.json"
        environment_path = self.metadata / "environment.json"
        write_json(config_path, config)
        write_json(environment_path, environment)
        freeze = {
            "schema_version": 1,
            "kind": "highambench-frozen-run-verification",
            "ok": True,
            "benchmark_id": self.benchmark_id,
            "environment_id": environment_id,
            "environment_bundle_sha256": bundle,
            "metadata_document_sha256": {
                "config": report.document_sha256(config),
                "environment": report.document_sha256(environment),
                "manifest": report.document_sha256(manifest),
                "run_order": report.document_sha256(run_order),
            },
            "release_manifest": {
                "path": "metadata/release_files.json",
                "sha256": release_sha,
                "file_count": len(release["files"]),
                "verification": {
                    "ok": True,
                    "expected": len(release["files"]),
                    "verified": len(release["files"]),
                    "missing": [],
                    "changed": [],
                },
            },
            "agent": {
                **self.agent,
                "binary_sha256": self.agent_binary_sha,
                "ultra_orchestration": ultra_orchestration,
            },
            "python": {
                "version": "3.10.synthetic",
                "binary_sha256": report.file_sha256(self.python_executable),
            },
            "limits": {
                "wall_clock_seconds": self.wall_limit,
                "total_model_tokens": self.token_limit,
                "prompt_startup_timeout_seconds": self.prompt_startup_timeout,
                "post_submission_validation_reserve_seconds": (
                    report.POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
                ),
            },
            "host_class": self.host_class,
            "lean": {
                "binary_sha256": report.file_sha256(
                    self.toolchain_root / "bin" / "lean"
                ),
                "source_files_verified": len(source_files),
                "compiled_files_verified": len(compiled_files),
            },
            "packages_runtime": {
                "path": self.packages_manifest_path.relative_to(self.project).as_posix(),
                "sha256": report.file_sha256(self.packages_manifest_path),
                "file_count": 1,
                "source_file_count": 1,
                "olean_file_count": 0,
                "compiled_support_file_count": 0,
                "verification": {
                    "ok": True,
                    "expected": 1,
                    "verified": 1,
                    "missing": [],
                    "changed": [],
                },
            },
            "compiled_environment_summary": {
                "path": self.compiled_summary_path.relative_to(self.project).as_posix(),
                "sha256": report.file_sha256(self.compiled_summary_path),
                "toolchain_file_count": 1,
                "package_count": 0,
                "package_file_count": 0,
            },
            "token_control": token_control,
            "token_control_canary": token_descriptor,
            "ultra_orchestration_canary": ultra_descriptor,
        }
        write_json(self.results / "freeze_check.json", freeze)
        self.hardware_descriptor = self._hardware_record(
            environment, release_sha, freeze
        )

        all_expected, p01_expected = report._expected_assignments(config, run_order, report._manifest_tasks(self.benchmark, manifest))
        first_later = next(item for item in all_expected if str(item["task_id"]).startswith("P02-"))
        last = p01_expected[-1]
        write_json(
            self.results / "last_chunk_status.json",
            {
                "schema_version": 1,
                "kind": "highambench-matrix-chunk-status",
                "status": "stopped_after_requested_paper",
                "requested_paper_id": "P01",
                "last_run_id": last["run_id"],
                "last_pair_id": last["pair_id"],
                "completed_runs_through_boundary": 18,
                "planned_runs_through_boundary": 18,
                "next_run_id": first_later["run_id"],
                "next_pair_id": first_later["pair_id"],
                "next_paper_id": "P02",
                "matrix_planned_runs": len(all_expected),
            },
        )
        records: list[dict[str, object]] = []
        base_time = dt.datetime(2026, 8, 7, 0, 0, tzinfo=dt.timezone.utc)
        task_map = report._manifest_tasks(self.benchmark, manifest)
        for index, planned in enumerate(p01_expected):
            record = self._run_record(
                config,
                freeze,
                task_map[str(planned["task_id"])],
                planned,
                index,
                base_time,
            )
            records.append(record)
            write_json(self.results / "records" / f"{record['run_id']}.json", record)
            write_json(self.results / "attempts" / f"{record['run_id']}.attempt-1.json", record)
            write_text(
                self.results / "attempts" / f"{record['run_id']}.attempt-1.jsonl",
                json.dumps({"method": "rawResponse/completed", "run_id": record["run_id"]}) + "\n",
            )
        write_text(
            self.results / "runs.jsonl",
            "".join(json.dumps(item, sort_keys=True) + "\n" for item in records),
        )

    def _construction(
        self, manifest: dict[str, object], task_ids: list[str]
    ) -> None:
        tool_names = (
            "tools/check_construction.py",
            "tools/common.py",
            "tools/dependency_audit.lean",
            "tools/hashes.py",
            "tools/lean_isolated.py",
            "tools/preflight.py",
            "tools/validator.py",
        )
        tools: dict[str, str] = {}
        for relative in tool_names:
            path = self.benchmark / relative
            write_text(path, f"synthetic frozen construction tool {relative}\n")
            tools[relative] = report.file_sha256(path)

        descriptor_data: dict[str, dict[str, object]] = {}
        for name in ("numstability_compiled", "numstability_source", "packages_runtime"):
            path = self.metadata / "evidence" / f"{name}.json"
            write_json(path, {"kind": f"synthetic-{name}", "verified": True})
            value: dict[str, object] = {
                "path": path.relative_to(self.benchmark).as_posix(),
                "sha256": report.file_sha256(path),
                "file_count": 3,
                "verified": 3,
                "exact_tree": True,
            }
            if name == "numstability_compiled":
                value["only_numstability_namespace"] = True
            if name == "packages_runtime":
                value["only_mathlib_source_and_lean_compiled_artifacts"] = True
                value["condition_n_absence_scan"] = {
                    "ok": True,
                    "complete": True,
                    "matches": [],
                    "files_scanned": 3,
                }
            descriptor_data[name] = value

        papers = [str(item["paper_id"]) for item in manifest["papers"]]  # type: ignore[index]
        task_info: dict[str, tuple[str, str, str]] = {}
        for paper in manifest["papers"]:  # type: ignore[index]
            for target in paper["targets"]:
                task_info[str(target["task_id"])] = (
                    str(paper["paper_id"]),
                    str(target["tier"]),
                    f"HighamBench.{target['lean_target']['declaration']}",
                )
        shared = {
            paper_id: {
                "HighamBench/Core.olean": hashlib.sha256(
                    f"core-{paper_id}".encode()
                ).hexdigest(),
                f"HighamBench/{paper_id}Definitions.olean": hashlib.sha256(
                    f"definitions-{paper_id}".encode()
                ).hexdigest(),
            }
            for paper_id in papers
        }
        results: list[dict[str, object]] = []
        for task_id in task_ids:
            paper_id, tier, theorem = task_info[task_id]
            controlled = self.metadata / "controlled" / f"{task_id}.json"
            for condition in report.EXPECTED_CONDITIONS:
                declarations = (
                    [{"name": f"NumStability.synthetic.{task_id}"}]
                    if condition == "L"
                    else []
                )
                dependency = {
                    "complete": True,
                    "exit_code": 0,
                    "format_version": 2,
                    "forbidden_dependency_count": 0,
                    "missing_helper_modules": [],
                    "library_use": condition == "L",
                    "library_declarations": declarations,
                    "semantic_type_check": {
                        "candidate": theorem,
                        "expected": theorem,
                        "equal": True,
                    },
                }
                validation = {
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
                    "note": "synthetic hidden construction validation passed",
                    "dependency_audit": dependency,
                }
                preflight = None
                if condition == "N":
                    preflight = {
                        "ok": True,
                        "complete": True,
                        "controlled_manifest_sha256": report.file_sha256(controlled),
                        "filesystem_leaks": [],
                        "controlled_files_verified_after_staging": {
                            "ok": True,
                            "changed": [],
                            "missing": [],
                            "expected": 2,
                            "verified": 2,
                        },
                        "import_probe": {
                            "attempted": True,
                            "reliable": True,
                            "importable": False,
                            "timed_out": False,
                            "system_error": None,
                        },
                    }
                results.append(
                    {
                        "task_id": task_id,
                        "paper_id": paper_id,
                        "tier": tier,
                        "condition": condition,
                        "pass": True,
                        "target_theorem": theorem,
                        "manifest_sha256": report.file_sha256(controlled),
                        "gold_source_sha256": hashlib.sha256(
                            f"gold-{task_id}-{condition}".encode()
                        ).hexdigest(),
                        "helpers": [
                            {
                                "module": f"HighamBench.{paper_id}Definitions",
                                "path": f"private/{task_id}.lean",
                                "source_sha256": hashlib.sha256(task_id.encode()).hexdigest(),
                                "build": {
                                    "exit_code": 0,
                                    "olean_created": True,
                                    "timed_out": False,
                                    "system_error": None,
                                },
                            }
                        ],
                        "reasons": [],
                        "condition_n_library_arguments_omitted": condition == "N",
                        "n_preflight": preflight,
                        "validation": validation,
                    }
                )
        construction = {
            "schema_version": 1,
            "kind": "highambench-private-construction-check",
            "pass": True,
            "record_status": "current_final",
            "summary": {
                "expected": 120,
                "checked": 120,
                "passed": 120,
                "condition_n_passed": 60,
                "condition_l_passed": 60,
            },
            "scope": {
                "central_manifest": "metadata/manifest.json",
                "central_manifest_sha256": report.file_sha256(
                    self.metadata / "manifest.json"
                ),
                "complete_manifest_scope": True,
                "manifest_available_task_ids": sorted(task_ids),
                "selected_task_ids": sorted(task_ids),
                "manifest_paper_ids": papers,
                "selected_paper_ids": papers,
            },
            "execution": {
                "jobs": 4,
                "result_order": "central manifest order, N then L per task",
            },
            "isolation": {
                "condition_l_numstability_mounts_configured": True,
                "condition_n_numstability_mounts_configured": False,
                "condition_n_preflight_after_complete_controlled_staging": True,
                "controlled_task_staged_under": "task/",
                "fresh_workspace_per_result": True,
                "private_gold_staged_as": "Submission.lean",
                "private_helper_oleans_reused": False,
                "validator_hidden_rebuild": True,
            },
            "verification_basis": {
                "tools": tools,
                **descriptor_data,
                "shared_olean": {
                    "bundles": shared,
                    "exact_file_count": 40,
                    "condition_n_absence_scan": {
                        "ok": True,
                        "complete": True,
                        "matches": [],
                        "files_scanned": 40,
                    },
                },
                "executables": {
                    "bubblewrap": {"path": "/usr/bin/bwrap", "sha256": "c" * 64},
                    "python": {"path": "/usr/bin/python3", "sha256": "d" * 64},
                },
            },
            "results": results,
        }
        evidence = self.metadata / "evidence"
        certificate_path = evidence / "construction_validation_full_current.json"
        write_json(certificate_path, construction)
        certificate_sha = report.file_sha256(certificate_path)
        pointer_common = {
            "status": "current complete-corpus construction evidence",
            "current_evidence": (
                "paper_bencmark/highambench/metadata/evidence/"
                "construction_validation_full_current.json"
            ),
            "current_evidence_sha256": certificate_sha,
        }
        write_json(
            evidence / "condition_n_preflight.json",
            {
                **pointer_common,
                "kind": "highambench-condition-n-preflight-evidence-pointer",
                "current_result": {
                    "condition_n_tasks_checked": 60,
                    "complete_staged_task_scans_passed": 60,
                    "reliable_failed_import_probes": 60,
                    "filesystem_leaks": 0,
                },
            },
        )
        write_json(
            evidence / "library_dependency_probe.json",
            {
                **pointer_common,
                "kind": "highambench-library-dependency-evidence-pointer",
                "current_result": {
                    "proofs_checked": 120,
                    "proofs_passed": 120,
                    "condition_n_library_use": False,
                    "condition_l_passed_proofs_using_numstability": 60,
                    "dependency_audit_format": 2,
                    "forbidden_dependencies": 0,
                },
            },
        )

    def _canary(self, kind: str) -> dict[str, object]:
        artifact_root = self.project / "artifacts" / kind
        labels = (
            token_canary.ARTIFACT_LABELS
            if kind == "token"
            else ultra_canary.ARTIFACT_LABELS
        )
        artifacts: dict[str, dict[str, object]] = {}
        for label in labels:
            artifact = artifact_root / f"{label}.json"
            artifact_value = (
                {
                    "benchmark_id": self.benchmark_id,
                    "prompt_protocol": self.production_prompt_protocol,
                    "execution_components": self.execution_components,
                }
                if label == "freeze_check"
                else {"kind": f"synthetic-{kind}-{label}", "authenticated": True}
            )
            write_json(
                artifact,
                artifact_value,
            )
            artifacts[label] = {
                "path": artifact.name,
                "sha256": report.file_sha256(artifact),
            }
        runner_label = "record" if kind == "token" else "runner_record"
        runner_record_path = artifact_root / f"{runner_label}.json"
        usage_path = (artifact_root / "usage.json").resolve()
        gate_paths = runner.provider_gate_paths(usage_path)
        run_id = (
            token_canary.CANARY_ID if kind == "token" else ultra_canary.CANARY_ID
        )
        gate_token_limit = (
            token_canary.DEFAULT_CANARY_TOKEN_LIMIT
            if kind == "token"
            else self.token_limit
        )
        root_thread_id = f"{kind}-canary-root"
        turn_id = f"{kind}-canary-turn"
        response_id = f"{kind}-canary-response"
        released_record = {
            "schema_version": 1,
            "protocol_version": "highambench-prompt-release-v1",
            "kind": "highambench_prompt_released",
            "run_id": run_id,
            "released_at_monotonic_ns": 1_000_000_000,
            "released_at_unix_ns": 2_000_000_000,
        }
        prompt_sha = hashlib.sha256(f"{kind}-canary-prompt".encode()).hexdigest()
        if kind == "token":
            raw_usage: dict[str, object] = {
                "input_tokens": 240_000,
                "cached_input_tokens": 20_000,
                "cache_write_input_tokens": 2_000,
                "output_tokens": 20_000,
                "reasoning_output_tokens": 5_000,
                "total_tokens": 260_000,
            }
            boundary: dict[str, object] = {}
        else:
            raw_usage = {
                "input_tokens": 800,
                "cached_input_tokens": 100,
                "cache_write_input_tokens": 20,
                "output_tokens": 200,
                "reasoning_output_tokens": 50,
                "total_tokens": 1_000,
            }
            boundary = {
                "response_id": response_id,
                "raw_response_notification_sequence": 1,
                "request_published_at_monotonic_ns": 1_020_000_000,
                "request_published_at_unix_ns": 2_020_000_000,
            }
        raw_usage.update(
            {
                "model_tokens": raw_usage["total_tokens"],
                "response_count": 1,
                "notification_sequence": 1,
                "response_ids": [response_id],
                "root_thread_id": root_thread_id,
                "interrupt_requested": False,
                "pending_interrupt_response_count": 0,
                "invalid_reasons": [],
                "measurement_exact": True,
                "first_crossing": None,
            }
        )
        gate_record, gate_catalog, gate_transport, gate_source_sha = (
            install_accepted_provider_gate_fixture(
                usage_path=usage_path,
                usage=raw_usage,
                boundary=boundary,
                run_id=run_id,
                token_limit=gate_token_limit,
                root_thread_id=root_thread_id,
                turn_id=turn_id,
                response_id=response_id,
                prompt_release_record=released_record,
                prompt_sha256=prompt_sha,
                request_published_monotonic_ns=1_020_000_000,
                request_published_unix_ns=2_020_000_000,
                raw_response_monotonic_ns=1_019_000_000,
                raw_response_unix_ns=2_019_000_000,
                close_reason=("token_limit" if kind == "token" else "accepted_submission"),
            )
        )
        if kind == "token":
            gate_record = upgrade_token_gate_to_two_call_compaction_fixture(
                usage_path=usage_path,
                usage=raw_usage,
                record=gate_record,
                token_limit=gate_token_limit,
            )
            raw_usage.update(
                {
                    "submission_boundary": None,
                    "submission_boundary_exact": False,
                    "drain_complete": False,
                    "tree_quiescent": False,
                    "stop_reason": "token_limit",
                }
            )
        else:
            raw_usage.update(
                {
                    "submission_boundary": boundary,
                    "submission_boundary_exact": True,
                    "drain_complete": False,
                    "tree_quiescent": False,
                    "stop_reason": "first_valid_proof",
                }
            )
        write_json(usage_path, raw_usage)
        gate_authentication = runner.authenticate_provider_gate_artifact(
            gate_paths["final"],
            token_limit=gate_token_limit,
            run_id=run_id,
            model="gpt-5.6-sol",
            reasoning_effort="ultra",
            root_thread_id=root_thread_id,
            prompt_release_sha256=hashlib.sha256(
                report.canonical_bytes(released_record) + b"\n"
            ).hexdigest(),
            prompt_release_protocol="highambench-prompt-release-v1",
            prompt_sha256=prompt_sha,
            model_catalog_sha256=str(gate_catalog["catalog_sha256"]),
            model_entry_sha256=str(gate_catalog["entry_sha256"]),
            expected_transport_provenance=gate_transport,
            usage=raw_usage,
            expected_source_sha256=gate_source_sha,
        )
        gate_summary = runner.provider_gate_run_record(
            required=True,
            status="final_artifact_authenticated",
            paths=gate_paths,
            source_sha256=gate_source_sha,
            catalog=gate_catalog,
            transport_provenance=gate_transport,
            live_crossing=(
                gate_authentication["derived"]["first_crossing"]
                if kind == "token"
                else None
            ),
            final=gate_authentication,
            error=None,
        )
        gate_command = [
            "fixture-adapter",
            "--usage-output",
            str(usage_path),
            "--provider-gate-live-output",
            str(gate_paths["live"]),
            "--provider-gate-output",
            str(gate_paths["final"]),
            "--model-catalog-sha256",
            str(gate_catalog["catalog_sha256"]),
            "--model-entry-sha256",
            str(gate_catalog["entry_sha256"]),
            "--provider-response-bound",
            str(runner.PROVIDER_RESPONSE_TOKEN_BOUND),
        ]
        gate_runner_record = {
            "run_id": run_id,
            "pass": kind != "token",
            "failure_code": "TOKEN_LIMIT" if kind == "token" else None,
            "agent_exit_code": 0,
            "agent": {
                "model": "gpt-5.6-sol",
                "reasoning_effort": "ultra",
            },
            "limits": {"model_tokens": gate_token_limit},
            "agent_command": gate_command,
            "prompt_release": {
                "effective_prompt_sha256": prompt_sha,
                "released": {"record": released_record},
            },
            "token_usage": raw_usage,
            "token_measurement": {
                "limit_enforcement": {
                    "mode": runner.ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE,
                    "notification": runner.ULTRA_USAGE_NOTIFICATION,
                    "configured_limit_tokens": gate_token_limit,
                    "triggered": kind == "token",
                    "observed_tokens": (
                        raw_usage["first_crossing"]["tokens"]
                        if kind == "token"
                        else None
                    ),
                    "overshoot_tokens": (
                        raw_usage["first_crossing"]["tokens"] - gate_token_limit
                        if kind == "token"
                        else None
                    ),
                    "first_crossing_tokens": (
                        raw_usage["first_crossing"]["tokens"]
                        if kind == "token"
                        else None
                    ),
                    "first_crossing_overshoot_tokens": (
                        raw_usage["first_crossing"]["tokens"] - gate_token_limit
                        if kind == "token"
                        else None
                    ),
                    "final_endpoint_tokens": (
                        raw_usage["model_tokens"] if kind == "token" else None
                    ),
                    "final_overshoot_tokens": (
                        max(0, raw_usage["model_tokens"] - gate_token_limit)
                        if kind == "token"
                        else None
                    ),
                    "checked_before_submission_validation": True,
                    "one_response_overshoot_possible": True,
                    "concurrent_inflight_overshoot_possible": False,
                }
            },
            "provider_token_gate": gate_summary,
        }
        write_json(runner_record_path, gate_runner_record)
        artifacts[runner_label] = {
            "path": runner_record_path.name,
            "sha256": report.file_sha256(runner_record_path),
        }
        artifacts["usage"] = {
            "path": usage_path.name,
            "sha256": report.file_sha256(usage_path),
        }
        artifacts["provider_gate"] = {
            "path": gate_paths["final"].name,
            "sha256": report.file_sha256(gate_paths["final"]),
        }
        gate_projection = (
            token_canary_projection_fixture(
                record_sha256=str(gate_record["record_sha256"]),
                response_ids=list(raw_usage["response_ids"]),
                provider_usage_reconciliation=dict(
                    raw_usage["provider_usage_reconciliation"]
                ),
            )
            if kind == "token"
            else ultra_canary_projection_fixture(
                record_sha256=str(gate_record["record_sha256"]),
                response_ids=list(raw_usage["response_ids"]),
                provider_usage_reconciliation=dict(
                    raw_usage["provider_usage_reconciliation"]
                ),
            )
        )
        relative_evidence = (
            token_canary.FROZEN_EVIDENCE_PATH
            if kind == "token"
            else ultra_canary.FROZEN_EVIDENCE_PATH
        )
        evidence_path = self.project / relative_evidence
        canary_agent = {
            **self.agent,
            "binary_sha256": self.agent_binary_sha,
            "ultra_orchestration": {
                "enabled": True,
                "max_concurrent_threads_per_session": 4,
            },
        }
        if kind == "token":
            evidence = {
                "schema_version": token_canary.EVIDENCE_SCHEMA_VERSION,
                "kind": token_canary.EVIDENCE_KIND,
                "status": "passed",
                "public_release": False,
                "scored": False,
                "matrix_assignment": False,
                "synthetic_input": True,
                "benchmark_task_bytes_used": False,
                "canary_id": token_canary.CANARY_ID,
                "benchmark_id": self.benchmark_id,
                "agent": canary_agent,
                "prompt": token_canary.prompt_record(),
                "controls": {
                    "frozen_benchmark_token_limit": self.token_limit,
                    "outer_canary_token_limit": token_canary.DEFAULT_CANARY_TOKEN_LIMIT,
                },
                "source_separation": {"audit_sha256": "c" * 64},
                "outcome": {
                    "first_crossing_tokens": 260_000,
                    "total_model_tokens": 260_000,
                    "thread_count": 1,
                    "response_count": 2,
                    "drain_complete": False,
                    "measurement_exact": True,
                    "accounting_projection": gate_projection,
                },
                "artifact_root": artifact_root.relative_to(self.project).as_posix(),
                "artifacts": artifacts,
            }
        else:
            evidence = {
                "schema_version": 1,
                "kind": ultra_canary.EVIDENCE_KIND,
                "status": "passed",
                "public_release": False,
                "scored": False,
                "matrix_assignment": False,
                "synthetic_input": True,
                "canary_id": ultra_canary.CANARY_ID,
                "benchmark_id": self.benchmark_id,
                "agent": canary_agent,
                "prompt": ultra_canary.prompt_record(),
                "controls": {
                    "outer_token_limit": self.token_limit,
                    "production_dependency_audit_required": True,
                    "dependency_audit_complete_required": True,
                },
                "outcome": {
                    "measurement_exact": True,
                    "submission_boundary_exact": True,
                    "stop_reason": "first_valid_proof",
                    "drain_complete": False,
                    "root_active_at_boundary": True,
                    "descendants_quiescent": True,
                    "token_limit_triggered": False,
                    "positive_usage_descendant_thread_count": 1,
                    "accounting_projection": gate_projection,
                },
                "artifact_root": artifact_root.relative_to(self.project).as_posix(),
                "artifacts": artifacts,
            }
        write_json(evidence_path, evidence)
        return {
            "path": relative_evidence,
            "sha256": report.file_sha256(evidence_path),
            "status": "passed",
        }

    def _reviews(self, manifest_path: Path, task_ids: list[str]) -> dict[str, object]:
        collisions = task_ids[:13]
        task_reviews = [
            {
                "task_id": task_id,
                "source_faithful": True,
                "novelty": task_id not in collisions,
                "novelty_decision": (
                    "fail_exact_target_collision"
                    if task_id in collisions
                    else "pass_exact_target_novelty"
                ),
            }
            for task_id in task_ids
        ]
        manifest_sha = report.file_sha256(manifest_path)
        source = {
            "schema_version": 1,
            "kind": "synthetic-independent-source-review",
            "benchmark_manifest_sha256": manifest_sha,
            "reviewer": {
                "id": "codex-fresh-context-source-reviewer",
                "identity": "Codex independent source reviewer",
                "fresh_context": True,
            },
            "overall_decision": "fail_exact_target_novelty",
            "public_release": False,
            "task_reviews": task_reviews,
            "summary": {
                "source_faithful": 60,
                "exact_target_novel": 47,
                "exact_target_collisions": 13,
                "collision_task_ids": collisions,
            },
        }
        formal = {
            "schema_version": 1,
            "kind": "synthetic-independent-formal-review",
            "benchmark_manifest_sha256": manifest_sha,
            "reviewer": {
                "id": "codex-fresh-context-formal-reviewer",
                "identity": "non-human formal review agent",
                "fresh_context": True,
            },
            "overall_decision": "fail_exact_target_novelty",
            "release_approval": False,
            "task_reviews": task_reviews,
            "summary": {
                "source_faithful_count": 60,
                "exact_target_absent_from_both_count": 47,
                "exact_target_collision_count": 13,
                "retained_novelty_rejections": collisions,
            },
        }
        records: list[dict[str, object]] = []
        for name, value in (("source.json", source), ("formal.json", formal)):
            path = self.metadata / "reviews" / name
            write_json(path, value)
            records.append(
                {
                    "path": path.relative_to(self.benchmark).as_posix(),
                    "sha256": report.file_sha256(path),
                    "task_count": 60,
                    "record_status": "current_with_blocking_defects",
                }
            )
        return {
            "enabled": True,
            "fresh_context_reviews_required": True,
            "source_fidelity_required": True,
            "scope": "exact-target novelty rejections only",
            "ignored_rejection_task_ids": collisions,
            "review_records": records,
        }

    def _hardware_record(
        self,
        environment: dict[str, object],
        release_sha: str,
        freeze: dict[str, object],
    ) -> dict[str, object]:
        job_id = "123456"
        hostname = "synthetic-node"
        scheduler = {
            "partition": "KFOUNTOU",
            "job_oversubscribe": "OK",
            "partition_oversubscribe": "FORCE:1",
            "node_list": hostname,
            "exclusive": False,
            "sharing_policy": "partition_forced_oversubscription",
            "dynamic_co_tenant_count_recorded": False,
        }
        hardware = {
            "schema_version": 1,
            "kind": "highambench-allocation-hardware-record",
            "job_id": job_id,
            "hostname": hostname,
            "measurement_environment": {
                "environment_id": environment["environment_id"],
                "environment_bundle_sha256": environment["environment_bundle_sha256"],
                "release_manifest_sha256": release_sha,
                "freeze_check_sha256": report.document_sha256(freeze),
            },
            "host_class": self.host_class,
            "host": {
                "hostname": hostname,
                "kernel": self.host_class["kernel"],
                "virtualization": self.host_class["virtualization"],
                "cpu_vendor": self.host_class["cpu_vendor"],
                "processor": self.host_class["processor"],
                "cpu_family": self.host_class["cpu_family"],
                "cpu_model": self.host_class["cpu_model"],
                "cpu_stepping": self.host_class["cpu_stepping"],
                "benchmark_process_visible_memory_bytes": self.host_class[
                    "visible_memory_bytes"
                ],
            },
            "allocation": {
                "cpu_affinity_logical_cpus": [0, 1, 2, 3],
                "online_logical_cpus": self.host_class["online_logical_cpus"],
                "allocated_physical_cores": self.host_class["allocated_physical_cores"],
                "allocated_sockets": self.host_class["allocated_sockets"],
                "allocated_threads_per_core": self.host_class[
                    "allocated_threads_per_core"
                ],
                "cgroup_memory_limit_bytes": self.host_class[
                    "allocation_memory_limit_bytes"
                ],
            },
            "slurm": {
                "job_id": job_id,
                "node_list": hostname,
                "num_nodes": self.host_class["slurm_num_nodes"],
                "num_cpus": self.host_class["slurm_num_cpus"],
                "num_tasks": self.host_class["slurm_num_tasks"],
                "cpus_per_task": self.host_class["slurm_cpus_per_task"],
                "allocated_memory_bytes": self.host_class[
                    "slurm_allocated_memory_bytes"
                ],
                "alloc_tres": "billing=4,cpu=4,mem=32G,node=1",
                "allocated_gpu_count": 0,
                "gpu_environment": {
                    "SLURM_GPUS_ON_NODE": "0",
                    "SLURM_JOB_GPUS": None,
                    "CUDA_VISIBLE_DEVICES": "",
                },
            },
            "scheduler_sharing": scheduler,
        }
        hardware["record_sha256"] = report.document_sha256(hardware)
        path = self.results / "allocation_hardware" / f"slurm-{job_id}.json"
        write_json(path, hardware)
        return {
            "path": path.relative_to(self.results).as_posix(),
            "sha256": report.file_sha256(path),
            "record_sha256": hardware["record_sha256"],
            "job_id": job_id,
        }

    def _run_record(
        self,
        config: dict[str, object],
        freeze: dict[str, object],
        task: dict[str, object],
        planned: dict[str, object],
        index: int,
        base_time: dt.datetime,
    ) -> dict[str, object]:
        run_id = str(planned["run_id"])
        condition = str(planned["condition"])
        candidate = f"import HighamBench.P01Definitions\n-- measured {run_id}\nexample : True := by trivial\n".encode()
        candidate_sha = hashlib.sha256(candidate).hexdigest()
        usage_path = (self.results / "logs" / f"{run_id}.attempt-1.usage.json").resolve()
        usage_path.parent.mkdir(parents=True, exist_ok=True)
        sequence = 1
        elapsed = 10.0 + index
        slot_ns = index * 100_000_000_000
        ready_monotonic_ns = 10_000_000_000_000 + slot_ns
        go_monotonic_ns = ready_monotonic_ns + 1_000_000
        release_monotonic_ns = go_monotonic_ns + 1_000_000
        flushed_monotonic_ns = release_monotonic_ns + 1_000_000
        request_published_monotonic_ns = release_monotonic_ns + int(
            elapsed * 1_000_000_000
        )
        ready_unix_ns = 1_800_000_000_000_000_000 + slot_ns
        go_unix_ns = ready_unix_ns + 1_000_000
        release_unix_ns = go_unix_ns + 1_000_000
        flushed_unix_ns = release_unix_ns + 1_000_000
        request_published_unix_ns = release_unix_ns + int(
            elapsed * 1_000_000_000
        )
        dynamic_before_response = index % 2 == 0
        outer_observed_monotonic_ns = request_published_monotonic_ns - 4_000_000
        if dynamic_before_response:
            inner_started_monotonic_ns = request_published_monotonic_ns - 3_000_000
            captured_monotonic_ns = request_published_monotonic_ns - 2_000_000
            raw_response_monotonic_ns = request_published_monotonic_ns - 1_000_000
            captured_unix_ns = request_published_unix_ns - 2_000_000
            raw_response_unix_ns = request_published_unix_ns - 1_000_000
            submission_event_order = (
                "inner_dynamic_call_before_raw_response_completed"
            )
        else:
            raw_response_monotonic_ns = request_published_monotonic_ns - 3_000_000
            inner_started_monotonic_ns = request_published_monotonic_ns - 2_000_000
            captured_monotonic_ns = request_published_monotonic_ns - 1_000_000
            raw_response_unix_ns = request_published_unix_ns - 3_000_000
            captured_unix_ns = request_published_unix_ns - 1_000_000
            submission_event_order = (
                "raw_response_completed_before_inner_dynamic_call"
            )
        total_input = 10_000 + 100 * index
        total_output = 1_000 + 10 * index
        total = total_input + total_output
        response_id = f"response-{index}"
        boundary_usage = {
            "input_tokens": total_input,
            "cached_input_tokens": total_input // 2,
            "cache_write_input_tokens": 0,
            "output_tokens": total_output,
            "reasoning_output_tokens": total_output,
            "total_tokens": total,
            "response_count": 1,
            "thread_count": 1,
            "notification_sequence": 1,
            "response_ids": [response_id],
            "appserver_response_count": 1,
            "appserver_response_ids": [response_id],
        }
        paths = codex_isolated.submission_barrier_paths(usage_path, sequence)
        target_theorem = f"HighamBench.{task['declaration']}"
        generated_id = f"{index:032x}"
        expected_theorem = f"HighamBench.highamBenchExpected_{generated_id}"
        library_arguments = (
            [
                "--library-source",
                str(self.library_source_root),
                "--library-root-file",
                str(self.library_root_file),
                "--library-olean",
                str(self.library_olean_root),
            ]
            if condition == "L"
            else []
        )
        lean_base = [
            str(self.python_executable),
            str((self.benchmark / "tools" / "lean_isolated.py").resolve()),
            "--condition",
            condition,
            "--workspace",
            "{workspace}",
            "--toolchain-root",
            str(self.toolchain_root),
            "--packages-root",
            str(self.packages_runtime_root),
            "--shared-olean-root",
            str(self.shared_olean_root),
            *library_arguments,
        ]
        compile_template = lean_base[:2] + ["olean"] + lean_base[2:] + [
            "--source",
            "{checked_submission}",
        ]
        audit_template = lean_base[:2] + ["audit"] + lean_base[2:] + [
            "--source",
            "{checked_submission}",
            "--audit-helper",
            str((self.benchmark / "tools" / "dependency_audit.lean").resolve()),
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
        controlled_sha = report.file_sha256(
            self.metadata / "controlled" / f"{task['task_id']}.json"
        )
        target_relative = Path(str(task["target_file"])).resolve().relative_to(
            self.benchmark.resolve()
        ).as_posix()
        validator_sha = report.document_sha256(
            {
                "condition": condition,
                "submission_relative": "Submission.lean",
                "canonical_relative": f"task/{target_relative}",
                "target_theorem": target_theorem,
                "compile_command": compile_template,
                "audit_command": audit_template,
                "controlled_manifest_sha256": controlled_sha,
                "reject_workspace_local_module_imports": True,
            }
        )
        nested_wire = nested_submission_wire_fixture(
            index,
            outer_observed_ns=outer_observed_monotonic_ns,
            inner_started_ns=inner_started_monotonic_ns,
        )
        challenge = codex_isolated.authenticated_record(
            {
                "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_challenge",
                "sequence": sequence,
                "attempt_nonce": f"nonce-{index}",
                "run_id": run_id,
                "validator_contract_sha256": validator_sha,
                **codex_isolated.nested_submission_exec_yield_record(),
                "published_at_unix_ns": ready_unix_ns - 2_000_000,
                "published_at_monotonic_ns": ready_monotonic_ns - 2_000_000,
            },
            "challenge_sha256",
        )
        call = codex_isolated.authenticated_record(
            {
                **nested_wire,
                "kind": "highambench_submission_call",
                "sequence": sequence,
                "challenge_sha256": challenge["challenge_sha256"],
                "attempt_nonce": challenge["attempt_nonce"],
                "run_id": run_id,
                "validator_contract_sha256": validator_sha,
                "jsonrpc_request_id": index + 1,
                "thread_id": f"root-{index}",
                "turn_id": f"turn-{index}",
                "candidate_path": "Candidate.lean",
                "candidate_sha256": candidate_sha,
                "candidate_size_bytes": len(candidate),
                "snapshot_name": paths["snapshot"].name,
                "captured_at_unix_ns": captured_unix_ns,
                "captured_at_monotonic_ns": captured_monotonic_ns,
            },
            "call_sha256",
        )
        request = codex_isolated.authenticated_record(
            {
                **nested_wire,
                "kind": "highambench_submission_request",
                "sequence": sequence,
                "challenge_sha256": challenge["challenge_sha256"],
                "call_sha256": call["call_sha256"],
                "attempt_nonce": challenge["attempt_nonce"],
                "run_id": run_id,
                "validator_contract_sha256": validator_sha,
                "jsonrpc_request_id": index + 1,
                "thread_id": f"root-{index}",
                "turn_id": f"turn-{index}",
                "response_id": response_id,
                "raw_response_notification_sequence": 1,
                "raw_response_observed_at_unix_ns": raw_response_unix_ns,
                "raw_response_observed_at_monotonic_ns": raw_response_monotonic_ns,
                "candidate_path": "Candidate.lean",
                "snapshot_name": paths["snapshot"].name,
                "candidate_sha256": candidate_sha,
                "candidate_size_bytes": len(candidate),
                "captured_at_unix_ns": call["captured_at_unix_ns"],
                "captured_at_monotonic_ns": call["captured_at_monotonic_ns"],
                "request_published_at_unix_ns": request_published_unix_ns,
                "request_published_at_monotonic_ns": request_published_monotonic_ns,
                "boundary_usage": boundary_usage,
                "raw_response_completed_before_boundary_publication": True,
                "submission_event_order": submission_event_order,
                "dynamic_call_observed_before_raw_response_completed": (
                    dynamic_before_response
                ),
                "raw_response_completed_before_dynamic_call_observed": (
                    not dynamic_before_response
                ),
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
        ack = codex_isolated.authenticated_record(
            {
                "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_ack",
                "sequence": sequence,
                "request_sha256": request["request_sha256"],
                "candidate_sha256": candidate_sha,
                "decision": "accept",
                "note": "accepted",
                "validator_accepted_at_unix_ns": request_published_unix_ns + 1_000_000,
                "validator_accepted_elapsed_seconds": elapsed,
                "published_at_unix_ns": request_published_unix_ns + 2_000_000,
                "published_at_monotonic_ns": request_published_monotonic_ns + 2_000_000,
            },
            "ack_sha256",
        )
        for name, value in (
            ("challenge", challenge),
            ("call", call),
            ("request", request),
            ("ack", ack),
        ):
            write_json(paths[name], value)
        paths["snapshot"].write_bytes(candidate)
        barrier_artifacts: dict[str, dict[str, object]] = {}
        for name, value in (
            ("challenge", challenge),
            ("call", call),
            ("request", request),
            ("ack", ack),
        ):
            barrier_artifacts[name] = {
                "path": str(paths[name]),
                "record_sha256": value[f"{name}_sha256"],
                "file_sha256": report.file_sha256(paths[name]),
            }
        barrier_artifacts["snapshot"] = {
            "path": str(paths["snapshot"]),
            "file_sha256": candidate_sha,
            "size_bytes": len(candidate),
        }
        for path in paths.values():
            path.chmod(0o444)
        boundary = {
            **nested_wire,
            "authenticated": True,
            "status": "accepted",
            "exact": True,
            "sequence": sequence,
            "request_sha256": request["request_sha256"],
            "ack_sha256": ack["ack_sha256"],
            "challenge_sha256": challenge["challenge_sha256"],
            "call_sha256": call["call_sha256"],
            "attempt_nonce": challenge["attempt_nonce"],
            "run_id": run_id,
            "validator_contract_sha256": validator_sha,
            "jsonrpc_request_id": request["jsonrpc_request_id"],
            "call_id": request["call_id"],
            "thread_id": request["thread_id"],
            "turn_id": request["turn_id"],
            "response_id": request["response_id"],
            "candidate_path": "Candidate.lean",
            "candidate_sha256": candidate_sha,
            "candidate_size_bytes": len(candidate),
            "request_published_at_unix_ns": request["request_published_at_unix_ns"],
            "request_published_at_monotonic_ns": request[
                "request_published_at_monotonic_ns"
            ],
            "validator_accepted_at_unix_ns": ack["validator_accepted_at_unix_ns"],
            "validator_accepted_elapsed_seconds": ack[
                "validator_accepted_elapsed_seconds"
            ],
            "raw_response_notification_sequence": 1,
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": submission_event_order,
            "candidate_captured_at_dynamic_call": True,
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
            "current_response_cumulative_required": False,
            "dynamic_call_observed_before_raw_response_completed": (
                dynamic_before_response
            ),
            "raw_response_completed_before_dynamic_call_observed": (
                not dynamic_before_response
            ),
        }
        zero_usage = {
            "input_tokens": 0,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 0,
            "reasoning_output_tokens": 0,
            "total_tokens": 0,
        }
        full_usage = {
            "input_tokens": total_input,
            "cached_input_tokens": total_input // 2,
            "cache_write_input_tokens": 0,
            "output_tokens": total_output,
            "reasoning_output_tokens": total_output,
            "total_tokens": total,
        }
        raw_usage = {
            "schema_version": 1,
            "accounting_projection_schema_version": (
                runner.ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
            ),
            "measurement_source": runner.ULTRA_USAGE_MEASUREMENT_SOURCE,
            "notification": runner.ULTRA_USAGE_NOTIFICATION,
            "usage_scope": runner.ULTRA_USAGE_SCOPE,
            "live_cumulative": True,
            "input_includes_cached": True,
            "notification_sequence": 1,
            "observed_at_unix_ns": 1_800_000_000_000_000_000 + index,
            "root_thread_id": request["thread_id"],
            "root_turn_id": request["turn_id"],
            "thread_count": 1,
            "response_count": 1,
            "response_ids": [request["response_id"]],
            "input_tokens": total_input,
            "cached_input_tokens": total_input // 2,
            "cache_write_input_tokens": 0,
            "output_tokens": total_output,
            "reasoning_output_tokens": total_output,
            "total_tokens": total,
            "threads": [
                {
                    "thread_id": request["thread_id"],
                    "parent_thread_id": None,
                    "provisional": False,
                    "agent_path": "root",
                    "turn_seen": True,
                    "active_turn_id": request["turn_id"],
                    "turn_status": "inProgress",
                    "thread_status": "active",
                    "spawn_call_id": None,
                    "spawn_parent_turn_id": None,
                    "spawn_parent_response_id": None,
                    "spawn_fork_turns": None,
                    "spawn_fork_semantics": None,
                    "spawn_binding_status": "root_zero",
                    "response_count": 1,
                    "input_tokens": total_input,
                    "cached_input_tokens": total_input // 2,
                    "cache_write_input_tokens": 0,
                    "output_tokens": total_output,
                    "reasoning_output_tokens": total_output,
                    "total_tokens": total,
                    "cumulative_baseline": zero_usage,
                    "expected_cumulative_baseline": zero_usage,
                    "last_cumulative": None,
                    "cumulative_observation_count": 0,
                    "expected_cumulative_projection": zero_usage,
                    "full_cumulative_projection": full_usage,
                    "cumulative_projection_exempt_response_id": response_id,
                    "cumulative_projection_exempt_response_usage": full_usage,
                    "observed_cumulative_baseline": None,
                    "cumulative_baseline_matches_expected": True,
                    "cumulative_projection_match": True,
                    "cumulative_projection_status": (
                        "zero_pre_response_without_cumulative_notification"
                    ),
                    "accounting_complete": True,
                }
            ],
            "drain_complete": False,
            "measurement_exact": True,
            "active_thread_ids": [request["thread_id"]],
            "unresolved_thread_ids": [],
            "invalid_reasons": [],
            "submission_boundary": boundary,
            "stop_reason": "first_valid_proof",
            "interrupt_requested": False,
            "first_crossing": None,
            "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
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
            "spawn_linkage_complete": True,
            "descendant_accounting_complete": True,
            "cumulative_projection_complete": True,
            "fork_policy_complete": True,
            "fork_policy": {
                **codex_isolated.ultra_fork_policy_static_record(),
                "call_evidence": [],
                "complete": True,
            },
            "accounting_complete": True,
        }
        accepted = self.results / "logs" / f"{run_id}.accepted.lean"
        accepted.write_bytes(candidate)
        declarations = ["NumStability.synthetic"] if condition == "L" and index % 2 else []
        rich_declarations = (
            [
                {
                    "name": "NumStability.synthetic",
                    "module": "NumStability.Synthetic",
                    "distance": 1,
                }
            ]
            if declarations
            else []
        )
        library_use = bool(declarations)
        hidden_workspace = (
            self.results
            / "hidden"
            / f"highambench-hidden-{index:08x}"
            / "project"
        ).resolve()
        checked_submission = hidden_workspace / f"HighamBenchChecked_{generated_id}.lean"
        expected_submission = hidden_workspace / f"HighamBenchExpected_{generated_id}.lean"
        command_values = {
            "{workspace}": str(hidden_workspace),
            "{checked_submission}": str(checked_submission),
            "{submission_module}": f"HighamBenchChecked_{generated_id}",
            "{expected_module}": f"HighamBenchExpected_{generated_id}",
            "{expected_theorem}": expected_theorem,
            "{local_modules_file}": str(
                hidden_workspace / f"{validator.LOCAL_MODULES_FILENAME}-{generated_id}"
            ),
        }

        def render_validation_command(
            template: list[str], *, expected: bool = False
        ) -> list[str]:
            replacements = dict(command_values)
            if expected:
                replacements["{checked_submission}"] = str(expected_submission)
            return [replacements.get(item, item) for item in template]

        candidate_command = render_validation_command(compile_template)
        expected_command = render_validation_command(compile_template, expected=True)
        dependency_command = render_validation_command(audit_template)
        controlled_checkpoint = {
            "ok": True,
            "expected": 2,
            "verified": 2,
            "missing": [],
            "changed": [],
        }
        command_result = {
            "command": candidate_command,
            "display": " ".join(candidate_command),
            "exit_code": 0,
            "output": "",
            "output_truncated": False,
            "seconds": 0.25,
            "system_error": None,
            "timed_out": False,
        }
        expected_command_result = {
            **command_result,
            "command": expected_command,
            "display": " ".join(expected_command),
        }
        audit_command_result = {
            **command_result,
            "command": dependency_command,
            "display": " ".join(dependency_command),
        }
        audit_output = (
            "format\t2\n"
            f"typeeq\t{target_theorem}\t{expected_theorem}\ttrue\n"
            f"target\t{target_theorem}\tHighamBenchChecked_{generated_id}\n"
            f"localmodule\tHighamBenchChecked_{generated_id}\n"
            "localmodule\tSubmission\n"
            + (
                "library\tNumStability.synthetic\tNumStability.Synthetic\t1\n"
                if declarations
                else ""
            )
            + "summary\t0\t0\n"
        )
        parsed_audit = validator.parse_dependency_audit(audit_output)
        parsed_audit["expected_helper_modules"] = []
        parsed_audit["missing_helper_modules"] = []
        validation = {
            "pass": True,
            "failure_code": None,
            "note": "accepted by hidden Lean validation",
            "condition": condition,
            "target_theorem": target_theorem,
            "submission": "Submission.lean",
            "reject_workspace_local_module_imports": True,
            "controlled_before": dict(controlled_checkpoint),
            "controlled_hidden": dict(controlled_checkpoint),
            "controlled_after_compile": dict(controlled_checkpoint),
            "controlled_after_expected_compile": dict(controlled_checkpoint),
            "controlled_after_audit": dict(controlled_checkpoint),
            "candidate_inventory": {
                "controlled_file_count": 2,
                "scanned_sources": ["Submission.lean"],
                "candidate_oleans": [],
                "ignored_build_roots": [],
                "local_modules": ["Submission"],
                "protected_modules": ["HighamBench.Core"],
                "findings": [],
            },
            "static_findings": [],
            "statement_check": {
                "ok": True,
                "submitted": f"theorem {task['declaration']} : True",
                "canonical": f"theorem {task['declaration']} : True",
            },
            "compile": dict(command_result),
            "expected_statement_compile": expected_command_result,
            "local_modules_side_channel": {
                "created_after_candidate_compilation": True,
                "candidate_recompiled_during_audit": False,
                "unchanged_after_audit": True,
            },
            "semantic_statement_check": {
                "candidate": target_theorem,
                "expected": expected_theorem,
                "equal": True,
            },
            "dependency_audit": {
                **audit_command_result,
                "output": audit_output,
                "parsed": parsed_audit,
            },
            "library_use": library_use,
            "library_declarations": rich_declarations,
            "library_audit_complete": True,
        }
        validation = runner._authenticate_validation_result(
            validation,
            run_id=run_id,
            task_id=str(task["task_id"]),
            candidate_sha256=candidate_sha,
            target_theorem=target_theorem,
            controlled_manifest_sha256=report.file_sha256(
                self.metadata / "controlled" / f"{task['task_id']}.json"
            ),
            validator_contract_sha256=validator_sha,
            submission_request_sha256=str(request["request_sha256"]),
            submission_sequence=sequence,
        )
        validation_path = self.results / "logs" / f"{run_id}.validation.json"
        write_json(validation_path, validation)
        agent_log = self.results / "logs" / f"{run_id}.agent.log"
        write_text(agent_log, "authenticated synthetic provider transcript\n")
        start = base_time + dt.timedelta(minutes=2 * index)
        finish = start + dt.timedelta(seconds=20 + index)
        staged = (self.results / "workspaces" / run_id / "staged").resolve()
        model_workspace = (
            self.results / "workspaces" / f"highambench-run-{run_id}"
        ).resolve()
        command = [
            str(self.python_executable),
            str((self.benchmark / "tools" / "codex_isolated.py").resolve()),
            "--condition",
            condition,
            "--workspace",
            str(model_workspace),
            "--prompt-file",
            str((staged / "agent_prompt.md").resolve()),
            "--context-file",
            str((staged / f"tasks/P01/{task['tier']}/context.md").resolve()),
            "--target-file",
            str((staged / f"tasks/P01/{task['tier']}/Target.lean").resolve()),
            "--usage-output",
            str(usage_path),
            "--toolchain-root",
            str(self.toolchain_root),
            "--packages-root",
            str(self.packages_runtime_root),
            "--shared-olean-root",
            str(self.shared_olean_root),
        ]
        if condition == "L":
            supplement = config["frozen_environment"]["prompt_protocol"]["condition_supplements"]["L"]  # type: ignore[index]
            command.extend(
                [
                    "--library-source",
                    str(self.library_source_root),
                    "--library-root-file",
                    str(self.library_root_file),
                    "--library-olean",
                    str(self.library_olean_root),
                    "--condition-prompt-file",
                    str((self.benchmark / str(supplement["path"])).resolve()),
                    "--condition-prompt-sha256",
                    str(supplement["sha256"]),
                ]
            )
        prompt_paths = codex_isolated.prompt_handshake_paths(usage_path)
        prompt_nonce = hashlib.sha256(f"prompt-release|{run_id}".encode()).hexdigest()
        source_supplement = (
            self.benchmark / "condition_prompts" / "L.md"
            if condition == "L"
            else None
        )
        effective_prompt = codex_isolated.build_prompt(
            self.benchmark / "agent_prompt.md",
            self.benchmark / f"tasks/P01/{task['tier']}/context.md",
            Path(str(task["target_file"])),
            source_supplement,
        )
        effective_bytes = effective_prompt.encode("utf-8")
        prompt_common = {
            "schema_version": codex_isolated.PROMPT_RELEASE_SCHEMA_VERSION,
            "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
            "handshake_nonce": prompt_nonce,
            "run_id": run_id,
            "condition": condition,
            "model": self.agent["model"],
            "reasoning_effort": self.agent["reasoning_effort"],
            "root_thread_id": request["thread_id"],
            "turn_start_request_id": codex_isolated.TURN_START_REQUEST_ID,
            "effective_prompt_sha256": hashlib.sha256(effective_bytes).hexdigest(),
            "effective_prompt_bytes": len(effective_bytes),
            "adapter_name": codex_isolated.PROMPT_RELEASE_ADAPTER_NAME,
            "adapter_version": codex_isolated.PROMPT_RELEASE_ADAPTER_VERSION,
            "app_server_client_name": codex_isolated.APP_SERVER_CLIENT_NAME,
            "app_server_client_version": codex_isolated.APP_SERVER_CLIENT_VERSION,
            "elapsed_clock": "CLOCK_MONOTONIC",
        }
        ready = codex_isolated.authenticated_record(
            {
                **prompt_common,
                "kind": codex_isolated.PROMPT_READY_KIND,
                "turn_start_write_state": "not_started",
                "ready_at_monotonic_ns": ready_monotonic_ns,
                "ready_at_unix_ns": ready_unix_ns,
            },
            "ready_sha256",
        )
        go = codex_isolated.authenticated_record(
            {
                **prompt_common,
                "kind": codex_isolated.PROMPT_GO_KIND,
                "ready_sha256": ready["ready_sha256"],
                "turn_start_write_authorized": True,
                "authorized_at_monotonic_ns": go_monotonic_ns,
                "authorized_at_unix_ns": go_unix_ns,
            },
            "go_sha256",
        )
        turn_start_wire = codex_isolated.canonical_protocol_wire(
            codex_isolated.prompt_turn_start_request(
                prompt=effective_prompt,
                root_thread_id=str(request["thread_id"]),
                model=str(self.agent["model"]),
                reasoning_effort=str(self.agent["reasoning_effort"]),
            )
        )
        released = codex_isolated.authenticated_record(
            {
                **prompt_common,
                "kind": codex_isolated.PROMPT_RELEASED_KIND,
                "ready_sha256": ready["ready_sha256"],
                "go_sha256": go["go_sha256"],
                "turn_start_write_state": "flushed",
                "timestamp_capture_point": "immediately_before_turn_start_write",
                "turn_start_request_sha256": hashlib.sha256(turn_start_wire).hexdigest(),
                "turn_start_request_bytes": len(turn_start_wire),
                "released_at_monotonic_ns": release_monotonic_ns,
                "released_at_unix_ns": release_unix_ns,
                "turn_start_flushed_at_monotonic_ns": flushed_monotonic_ns,
                "turn_start_flushed_at_unix_ns": flushed_unix_ns,
            },
            "release_sha256",
        )
        prompt_records = {"ready": ready, "go": go, "release": released}
        prompt_hash_fields = {
            "ready": "ready_sha256",
            "go": "go_sha256",
            "release": "release_sha256",
        }
        prompt_descriptors: dict[str, dict[str, object]] = {}
        for name, prompt_record in prompt_records.items():
            prompt_path = prompt_paths[name]
            write_canonical_json(prompt_path, prompt_record)
            prompt_path.chmod(0o444)
            prompt_descriptors[name] = {
                "path": str(prompt_path),
                "file_sha256": report.file_sha256(prompt_path),
                "record_sha256": prompt_record[prompt_hash_fields[name]],
                "record": prompt_record,
            }
        command.extend(
            [
                "--prompt-ready-output",
                str(prompt_paths["ready"]),
                "--prompt-go-input",
                str(prompt_paths["go"]),
                "--prompt-release-output",
                str(prompt_paths["release"]),
                "--prompt-handshake-nonce",
                prompt_nonce,
                "--prompt-run-id",
                run_id,
            ]
        )
        prompt_release = {
            "schema_version": codex_isolated.PROMPT_RELEASE_SCHEMA_VERSION,
            "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
            "required": True,
            "status": "released_authenticated",
            "authenticated": True,
            "timing_exact": True,
            "useful_work_basis": "authenticated_release",
            "startup_timeout_seconds": self.prompt_startup_timeout,
            "startup_timeout_triggered": False,
            "go_minimum_release_window_seconds": (
                runner.PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS
            ),
            "handshake_nonce": prompt_nonce,
            "elapsed_clock": "CLOCK_MONOTONIC",
            "artifact_paths": {
                name: str(path) for name, path in prompt_paths.items()
            },
            "effective_prompt_sha256": hashlib.sha256(effective_bytes).hexdigest(),
            "effective_prompt_bytes": len(effective_bytes),
            "ready": prompt_descriptors["ready"],
            "go": prompt_descriptors["go"],
            "released": prompt_descriptors["release"],
            "stale_artifacts_removed": [],
            "error": None,
        }
        gate_record, gate_catalog, gate_transport, gate_source_sha = (
            install_accepted_provider_gate_fixture(
                usage_path=usage_path,
                usage=raw_usage,
                boundary=boundary,
                run_id=run_id,
                token_limit=self.token_limit,
                root_thread_id=str(request["thread_id"]),
                turn_id=str(request["turn_id"]),
                response_id=response_id,
                prompt_release_record=released,
                prompt_sha256=hashlib.sha256(effective_bytes).hexdigest(),
                request_published_monotonic_ns=request_published_monotonic_ns,
                request_published_unix_ns=request_published_unix_ns,
                raw_response_monotonic_ns=raw_response_monotonic_ns,
                raw_response_unix_ns=raw_response_unix_ns,
            )
        )
        gate_paths = runner.provider_gate_paths(usage_path)
        command.extend(
            [
                "--provider-gate-live-output",
                str(gate_paths["live"]),
                "--provider-gate-output",
                str(gate_paths["final"]),
                "--model-catalog-sha256",
                str(gate_catalog["catalog_sha256"]),
                "--model-entry-sha256",
                str(gate_catalog["entry_sha256"]),
                "--provider-response-bound",
                str(runner.PROVIDER_RESPONSE_TOKEN_BOUND),
            ]
        )
        write_json(usage_path, raw_usage)
        parsed_usage = runner.read_token_usage(usage_path)
        assert parsed_usage is not None
        gate_authentication = runner.authenticate_provider_gate_artifact(
            gate_paths["final"],
            token_limit=self.token_limit,
            run_id=run_id,
            model=str(self.agent["model"]),
            reasoning_effort=str(self.agent["reasoning_effort"]),
            root_thread_id=str(request["thread_id"]),
            prompt_release_sha256=hashlib.sha256(
                report.canonical_bytes(released) + b"\n"
            ).hexdigest(),
            prompt_release_protocol=str(released["protocol_version"]),
            prompt_sha256=hashlib.sha256(effective_bytes).hexdigest(),
            model_catalog_sha256=str(gate_catalog["catalog_sha256"]),
            model_entry_sha256=str(gate_catalog["entry_sha256"]),
            expected_transport_provenance=gate_transport,
            usage=parsed_usage,
            expected_source_sha256=gate_source_sha,
        )
        provider_gate_summary = runner.provider_gate_run_record(
            required=True,
            status="final_artifact_authenticated",
            paths=gate_paths,
            source_sha256=gate_source_sha,
            catalog=gate_catalog,
            transport_provenance=gate_transport,
            live_crossing=None,
            final=gate_authentication,
            error=None,
        )
        if gate_authentication["record"] != gate_record:
            raise AssertionError("fixture gate authentication changed the sealed record")
        preflight = None
        if condition == "N":
            preflight = {
                "ok": True,
                "complete": True,
                "controlled_task_staging": {
                    "manifest_sha256": report.file_sha256(
                        self.metadata / "controlled" / f"{task['task_id']}.json"
                    ),
                    "verified_files": 2,
                    "expected_files": 2,
                    "complete": True,
                },
                "filesystem_leaks": [],
                "filesystem_scan": {
                    "root": ".",
                    "markers": ["NumStability", "numStability", "lean-fp-analysis"],
                    "regular_file_count": 3,
                    "directory_count": 2,
                    "symlink_count": 0,
                    "content_limit_bytes": 4 * 1024 * 1024,
                },
                "import_probe": {
                    "attempted": True,
                    "reliable": True,
                    "importable": False,
                    "command": [
                        str(self.python_executable),
                        str((self.benchmark / "tools" / "lean_isolated.py").resolve()),
                        "probe",
                        "--condition",
                        "N",
                        "--workspace",
                        str(
                            (
                                self.results
                                / "workspaces"
                                / f"highambench-run-{run_id}"
                            ).resolve()
                        ),
                        "--toolchain-root",
                        str(self.toolchain_root),
                        "--packages-root",
                        str(self.packages_runtime_root),
                        "--shared-olean-root",
                        str(self.shared_olean_root),
                        "--source",
                        str(
                            (
                                self.results
                                / "workspaces"
                                / f"highambench-run-{run_id}"
                                / "HighamBenchNoLibraryProbe_fixture.lean"
                            ).resolve()
                        ),
                    ],
                    "exit_code": 1,
                    "timed_out": False,
                    "system_error": None,
                    "output": "error: unknown module prefix 'NumStability'",
                    "output_truncated": False,
                    "conclusion": "compiler reported that the forbidden module is absent",
                },
            }
        record = {
            "schema_version": 1,
            "kind": "highambench-run",
            "run_id": run_id,
            "pair_id": planned["pair_id"],
            "task_id": planned["task_id"],
            "paper_id": "P01",
            "paper_sha256": task["paper_sha256"],
            "tier": task["tier"],
            "condition": condition,
            "repetition_id": planned["repetition_id"],
            "backend_seed": planned["backend_seed"],
            "pair_order": planned["pair_order"],
            "order_index": planned["order_index"],
            "agent": self.agent,
            "environment_id": config["frozen_environment"]["environment_id"],  # type: ignore[index]
            "frozen_run_verification": {
                "freeze_check": freeze,
                "freeze_check_sha256": report.document_sha256(freeze),
            },
            "limits": {
                "time_seconds": self.wall_limit,
                "model_tokens": self.token_limit,
                "prompt_startup_seconds": self.prompt_startup_timeout,
                "post_acceptance_usage_grace_seconds": 2.0,
            },
            "allocation_hardware": self.hardware_descriptor,
            "started_at_utc": start.isoformat(),
            "finished_at_utc": finish.isoformat(),
            "pass": True,
            "useful_work_started": True,
            "scored": True,
            "failure_code": None,
            "failure_note": "",
            "actual_stop_seconds": elapsed,
            "first_valid_seconds": elapsed,
            "scored_elapsed_seconds": elapsed,
            "time_measurement": (
                "authenticated CLOCK_MONOTONIC turn/start write to authenticated "
                "nested submission-boundary publication after outer exec raw-response "
                "completion with inner submit_proof blocked; hidden validation certifies "
                "the immutable requested bytes"
            ),
            "token_usage": parsed_usage,
            "token_measurement": {
                "provider_cumulative_total_exact": True,
                "source": runner.ULTRA_TOKEN_MEASUREMENT_SOURCE,
                "usage_scope": runner.ULTRA_USAGE_SCOPE,
                "thread_count": parsed_usage["thread_count"],
                "response_count": parsed_usage["response_count"],
                "tree_drain_complete": parsed_usage["drain_complete"],
                "cached_input_counted_once": True,
                "measurement_error": None,
                "trusted_usage_path_outside_workspace": True,
                "post_submission_usage_established": True,
                "limit_enforcement": {
                    "mode": runner.ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE,
                    "notification": runner.ULTRA_USAGE_NOTIFICATION,
                    "configured_limit_tokens": self.token_limit,
                    "checked_before_submission_validation": True,
                    "triggered": False,
                    "one_response_overshoot_possible": True,
                    "concurrent_inflight_overshoot_possible": False,
                    "observed_tokens": None,
                    "overshoot_tokens": None,
                    "first_crossing_tokens": None,
                    "first_crossing_overshoot_tokens": None,
                    "final_endpoint_tokens": None,
                    "final_overshoot_tokens": None,
                },
            },
            "library_use": library_use,
            "library_declarations": declarations,
            "n_preflight": preflight,
            "network_violation": {
                "detected": False,
                "integrity_ok": True,
                "event_count": 0,
            },
            "failure_precedence": ",".join(report.FAILURE_PRECEDENCE),
            "protocol": {
                "complete": True,
                "claims": dict(report.EXPECTED_PROTOCOL_CLAIMS),
                "verified": {field: True for field in report.PROTOCOL_VERIFICATIONS},
                "notes": [report.UNSEEDED_PROTOCOL_NOTE],
            },
            "agent_command": command,
            "prompt_release": prompt_release,
            "prompt_provenance": report.expected_prompt_provenance(
                self.benchmark, config, task, condition
            ),
            "submission_sha256": candidate_sha,
            "final_submission_sha256": candidate_sha,
            "accepted_submission_log": str(accepted.resolve()),
            "submission_changed_after_acceptance": False,
            "validation_log": str(validation_path.resolve()),
            "validation_log_sha256": report.file_sha256(validation_path),
            "validation_record_sha256": validation["record_sha256"],
            "agent_log": str(agent_log.resolve()),
            "agent_exit_code": 0,
            "provider_token_gate": provider_gate_summary,
            "ultra_submission_boundary": {
                "verified": True,
                "sequence": 1,
                "request_sha256": request["request_sha256"],
                "ack_sha256": ack["ack_sha256"],
                "artifacts": barrier_artifacts,
            },
        }
        record["matrix_attempt"] = 1
        record["matrix_record_sha256"] = report.document_sha256(record)
        return record

    def _replace_record(
        self, updated: dict[str, object], *, reseal_matrix_record: bool = True
    ) -> None:
        run_id = str(updated["run_id"])
        if reseal_matrix_record:
            updated.pop("matrix_record_sha256", None)
            updated["matrix_record_sha256"] = report.document_sha256(updated)
        write_json(self.results / "records" / f"{run_id}.json", updated)
        attempt_paths = list((self.results / "attempts").glob(f"{run_id}.attempt-*.json"))
        self_record_paths = [path for path in attempt_paths if report.read_json(path).get("run_id") == run_id]
        if len(self_record_paths) != 1:
            raise AssertionError(f"fixture has ambiguous attempt record for {run_id}")
        write_json(self_record_paths[0], updated)
        records = [
            json.loads(line)
            for line in (self.results / "runs.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        records = [updated if item.get("run_id") == run_id else item for item in records]
        write_text(
            self.results / "runs.jsonl",
            "".join(json.dumps(item, sort_keys=True) + "\n" for item in records),
        )

    def _reseal_provider_gate(
        self,
        record: dict[str, object],
        usage: dict[str, object],
        *,
        close_reason: str,
        published_monotonic_ns: int | None = None,
        published_unix_ns: int | None = None,
    ) -> dict[str, object]:
        """Reseal a fixture endpoint after an authorized outcome/time mutation."""

        if close_reason not in {"accepted_submission", "natural_end"}:
            raise AssertionError("fixture reseal supports accepted or natural endpoints")
        usage_path = Path(
            str(report._option(record["agent_command"], "--usage-output", "fixture"))
        ).resolve()
        paths = runner.provider_gate_paths(usage_path)
        gate_path = paths["final"]
        gate = report.read_json(gate_path)
        usage["model_tokens"] = usage["total_tokens"]
        terminal_sequence = int(gate["state"]["sequence"])
        transition = gate["transitions"][-1]
        transition.update(
            {
                "reason": f"terminal_close:{close_reason}",
                "call_id": None,
            }
        )
        if published_monotonic_ns is not None or published_unix_ns is not None:
            if type(published_monotonic_ns) is not int or type(published_unix_ns) is not int:
                raise AssertionError("retimed gate needs both strict integer clocks")
            transition["monotonic_ns"] = published_monotonic_ns + 100_000
            transition["unix_ns"] = published_unix_ns + 100_000
            gate["lifecycle"].update(
                {
                    "stopped_monotonic_ns": published_monotonic_ns + 200_000,
                    "stopped_unix_ns": published_unix_ns + 200_000,
                    "finalized_monotonic_ns": published_monotonic_ns + 300_000,
                    "finalized_unix_ns": published_unix_ns + 300_000,
                }
            )
            teardown = usage["adapter_teardown"]
            teardown.update(
                {
                    "started_at_monotonic_ns": published_monotonic_ns + 400_000,
                    "started_at_unix_ns": published_unix_ns + 400_000,
                    "completed_at_monotonic_ns": published_monotonic_ns + 500_000,
                    "completed_at_unix_ns": published_unix_ns + 500_000,
                }
            )
        gate["state"].update(
            {
                "close_reason": close_reason,
                "crossing": None,
                "crossing_closed": False,
            }
        )
        if close_reason == "accepted_submission":
            boundary = usage.get("submission_boundary")
            if not isinstance(boundary, dict):
                raise AssertionError("accepted gate reseal needs its boundary")
            boundary["provider_gate_close"] = {
                "won": True,
                "requested_reason": close_reason,
                "effective_reason": close_reason,
                "phase": "CLOSED",
                "sequence": terminal_sequence,
            }
        else:
            usage.pop("submission_boundary", None)
            usage["submission_boundary_exact"] = False
            usage["adapter_teardown"]["immediate"] = False
            usage["adapter_teardown"]["signal"] = None
            usage["adapter_teardown"]["returncode"] = 0
        gate.pop("record_sha256", None)
        gate["record_sha256"] = hashlib.sha256(
            report.canonical_bytes(gate) + b"\n"
        ).hexdigest()
        gate_path.chmod(0o600)
        write_canonical_json(gate_path, gate)
        gate_path.chmod(0o444)
        usage_gate = usage["provider_token_gate"]
        usage_gate.update(
            {
                "record_sha256": gate["record_sha256"],
                "live": gate["state"],
                "terminal": gate["state"],
            }
        )
        authentication = runner.authenticate_provider_gate_artifact(
            gate_path,
            token_limit=int(gate["configuration"]["token_limit"]),
            run_id=str(gate["bindings"]["run_id"]),
            model=str(gate["bindings"]["model"]),
            reasoning_effort=str(gate["bindings"]["reasoning_effort"]),
            root_thread_id=str(gate["bindings"]["root_thread_id"]),
            prompt_release_sha256=str(
                gate["bindings"]["prompt_release_sha256"]
            ),
            prompt_release_protocol=str(
                gate["bindings"]["prompt_release_protocol"]
            ),
            prompt_sha256=str(gate["bindings"]["prompt_sha256"]),
            model_catalog_sha256=str(
                gate["configuration"]["model_catalog_sha256"]
            ),
            model_entry_sha256=str(
                gate["configuration"]["model_entry_sha256"]
            ),
            expected_transport_provenance=gate["configuration"][
                "transport_provenance"
            ],
            usage=usage,
            expected_source_sha256=str(gate["implementation"]["source_sha256"]),
        )
        old_summary = record["provider_token_gate"]
        record["provider_token_gate"] = runner.provider_gate_run_record(
            required=True,
            status="final_artifact_authenticated",
            paths=paths,
            source_sha256=str(gate["implementation"]["source_sha256"]),
            catalog=old_summary["model_catalog"],
            transport_provenance=gate["configuration"]["transport_provenance"],
            live_crossing=None,
            final=authentication,
            error=None,
        )
        write_json(usage_path, usage)
        parsed = runner.read_token_usage(usage_path)
        assert parsed is not None
        return parsed

    def mutate_validation(
        self,
        record: dict[str, object],
        mutation: object,
    ) -> dict[str, object]:
        validation_path = Path(str(record["validation_log"]))
        validation = report.read_json(validation_path)
        validation.pop("record_sha256")
        assert callable(mutation)
        mutation(validation)
        validation["record_sha256"] = report.document_sha256(validation)
        write_json(validation_path, validation)
        record["validation_log_sha256"] = report.file_sha256(validation_path)
        record["validation_record_sha256"] = validation["record_sha256"]
        self._replace_record(record)
        return validation

    def retime_accepted_record(
        self,
        record: dict[str, object],
        *,
        request_elapsed: float,
        validator_elapsed: float,
        actual_stop: float,
    ) -> None:
        usage_path = Path(
            str(report._option(record["agent_command"], "--usage-output", "fixture"))
        )
        paths = codex_isolated.submission_barrier_paths(usage_path, 1)
        released = record["prompt_release"]["released"]["record"]
        release_mono = int(released["released_at_monotonic_ns"])
        release_unix = int(released["released_at_unix_ns"])
        request_ns = int(round(request_elapsed * 1_000_000_000))
        validator_ns = int(round(validator_elapsed * 1_000_000_000))
        published_mono = release_mono + request_ns
        published_unix = release_unix + request_ns

        call = report.read_json(paths["call"])
        call.pop("call_sha256")
        call.update(
            {
                "outer_raw_item_observed_at_monotonic_ns": published_mono - 4_000_000,
                "inner_dynamic_item_started_at_monotonic_ns": published_mono - 3_000_000,
                "captured_at_monotonic_ns": published_mono - 2_000_000,
                "captured_at_unix_ns": published_unix - 2_000_000,
            }
        )
        call = codex_isolated.authenticated_record(call, "call_sha256")

        request = report.read_json(paths["request"])
        request.pop("request_sha256")
        request.update(
            {
                "call_sha256": call["call_sha256"],
                "captured_at_monotonic_ns": call["captured_at_monotonic_ns"],
                "captured_at_unix_ns": call["captured_at_unix_ns"],
                "outer_raw_item_observed_at_monotonic_ns": call[
                    "outer_raw_item_observed_at_monotonic_ns"
                ],
                "inner_dynamic_item_started_at_monotonic_ns": call[
                    "inner_dynamic_item_started_at_monotonic_ns"
                ],
                "raw_response_observed_at_monotonic_ns": (
                    published_mono - 1_000_000
                ),
                "raw_response_observed_at_unix_ns": (
                    published_unix - 1_000_000
                ),
                "request_published_at_monotonic_ns": published_mono,
                "request_published_at_unix_ns": published_unix,
                "submission_event_order": (
                    "inner_dynamic_call_before_raw_response_completed"
                ),
                "dynamic_call_observed_before_raw_response_completed": True,
                "raw_response_completed_before_dynamic_call_observed": False,
            }
        )
        request = codex_isolated.authenticated_record(request, "request_sha256")

        ack = report.read_json(paths["ack"])
        ack.pop("ack_sha256")
        ack.update(
            {
                "request_sha256": request["request_sha256"],
                "validator_accepted_at_unix_ns": release_unix + validator_ns,
                "validator_accepted_elapsed_seconds": validator_elapsed,
                "published_at_unix_ns": release_unix + validator_ns + 1_000_000,
                "published_at_monotonic_ns": release_mono
                + validator_ns
                + 1_000_000,
            }
        )
        ack = codex_isolated.authenticated_record(ack, "ack_sha256")

        retained = record["ultra_submission_boundary"]
        retained.update(
            {
                "request_sha256": request["request_sha256"],
                "ack_sha256": ack["ack_sha256"],
            }
        )
        for name, value in (("call", call), ("request", request), ("ack", ack)):
            path = paths[name]
            path.chmod(0o644)
            write_json(path, value)
            path.chmod(0o444)
            retained["artifacts"][name].update(
                {
                    "record_sha256": value[f"{name}_sha256"],
                    "file_sha256": report.file_sha256(path),
                }
            )

        raw_usage = report.read_json(usage_path)
        raw_usage["submission_boundary"].update(
            {
                "call_sha256": call["call_sha256"],
                "request_sha256": request["request_sha256"],
                "ack_sha256": ack["ack_sha256"],
                "request_published_at_unix_ns": request[
                    "request_published_at_unix_ns"
                ],
                "request_published_at_monotonic_ns": request[
                    "request_published_at_monotonic_ns"
                ],
                "validator_accepted_at_unix_ns": ack[
                    "validator_accepted_at_unix_ns"
                ],
                "validator_accepted_elapsed_seconds": validator_elapsed,
                "outer_raw_item_observed_at_monotonic_ns": request[
                    "outer_raw_item_observed_at_monotonic_ns"
                ],
                "inner_dynamic_item_started_at_monotonic_ns": request[
                    "inner_dynamic_item_started_at_monotonic_ns"
                ],
                "submission_event_order": request["submission_event_order"],
                "dynamic_call_observed_before_raw_response_completed": request[
                    "dynamic_call_observed_before_raw_response_completed"
                ],
                "raw_response_completed_before_dynamic_call_observed": request[
                    "raw_response_completed_before_dynamic_call_observed"
                ],
            }
        )
        parsed_usage = self._reseal_provider_gate(
            record,
            raw_usage,
            close_reason="accepted_submission",
            published_monotonic_ns=published_mono,
            published_unix_ns=published_unix,
        )
        record["token_usage"] = parsed_usage

        validation_path = Path(str(record["validation_log"]))
        validation = report.read_json(validation_path)
        authentication = validation["authentication"]
        validation = runner._authenticate_validation_result(
            validation,
            run_id=str(authentication["run_id"]),
            task_id=str(authentication["task_id"]),
            candidate_sha256=str(authentication["candidate_sha256"]),
            target_theorem=str(authentication["target_theorem"]),
            controlled_manifest_sha256=str(
                authentication["controlled_manifest_sha256"]
            ),
            validator_contract_sha256=str(
                authentication["validator_contract_sha256"]
            ),
            submission_request_sha256=str(request["request_sha256"]),
            submission_sequence=int(authentication["submission_sequence"]),
        )
        write_json(validation_path, validation)
        record.update(
            {
                "validation_log_sha256": report.file_sha256(validation_path),
                "validation_record_sha256": validation["record_sha256"],
                "first_valid_seconds": request_elapsed,
                "scored_elapsed_seconds": request_elapsed,
                "actual_stop_seconds": actual_stop,
            }
        )
        self._replace_record(record)

    def make_rejected_l_validation_failure(
        self, *, validation_code: str = "PROOF_ERROR"
    ) -> str:
        record = next(
            report.read_json(path)
            for path in sorted((self.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "L"
        )
        run_id = str(record["run_id"])
        usage_path = Path(
            str(report._option(record["agent_command"], "--usage-output", "fixture"))
        )
        raw_usage = report.read_json(usage_path)
        raw_usage.pop("submission_boundary", None)
        raw_usage["drain_complete"] = True
        raw_usage["tree_quiescent"] = True
        raw_usage["submission_boundary_exact"] = False
        raw_usage["measurement_exact"] = True
        raw_usage["active_thread_ids"] = []
        raw_usage["stop_reason"] = None
        thread = raw_usage["threads"][0]
        zero = dict(thread["expected_cumulative_baseline"])
        full = dict(thread["full_cumulative_projection"])
        thread.update(
            {
                "last_cumulative": full,
                "cumulative_observation_count": 1,
                "expected_cumulative_projection": full,
                "cumulative_projection_exempt_response_id": None,
                "cumulative_projection_exempt_response_usage": None,
                "observed_cumulative_baseline": zero,
                "cumulative_baseline_matches_expected": True,
                "cumulative_projection_match": True,
                "cumulative_projection_status": "matched_full_projection",
                "accounting_complete": True,
                "active_turn_id": None,
                "turn_status": "completed",
                "thread_status": "idle",
            }
        )
        parsed = self._reseal_provider_gate(
            record, raw_usage, close_reason="natural_end"
        )
        for raw_path in record["ultra_submission_boundary"]["artifacts"].values():
            Path(str(raw_path["path"])).unlink()
        Path(str(record["accepted_submission_log"])).unlink()

        def reject(validation: dict[str, object]) -> None:
            validation.update(
                {
                    "pass": False,
                    "failure_code": validation_code,
                    "note": "hidden Lean build rejected the submission",
                    "compile": {
                        **validation["compile"],
                        "exit_code": 1,
                        "output": "error: unsolved goals",
                    },
                    "expected_statement_compile": None,
                    "controlled_after_expected_compile": None,
                    "local_modules_side_channel": None,
                    "controlled_after_audit": None,
                    "dependency_audit": None,
                    "semantic_statement_check": None,
                    "library_use": None,
                    "library_declarations": [],
                    "library_audit_complete": None,
                }
            )

        self.mutate_validation(record, reject)
        record = report.read_json(self.results / "records" / f"{run_id}.json")
        record.update(
            {
                "pass": False,
                "failure_code": validation_code,
                "failure_note": "hidden Lean build rejected the submission",
                "actual_stop_seconds": 25.0,
                "first_valid_seconds": None,
                "scored_elapsed_seconds": 1800.0,
                "token_usage": parsed,
                "library_use": None,
                "library_declarations": [],
                "accepted_submission_log": None,
                "ultra_submission_boundary": {"verified": False},
            }
        )
        record["protocol"]["verified"]["authenticated_first_valid_proof_boundary"] = False
        record["token_measurement"]["post_submission_usage_established"] = False
        record["token_measurement"]["tree_drain_complete"] = True
        self._replace_record(record)
        return run_id

    def make_l_failure(self, ordinal: int, failure_code: str) -> str:
        l_records = [
            report.read_json(path)
            for path in sorted((self.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "L"
        ]
        record = l_records[ordinal]
        usage_path = Path(
            str(report._option(record["agent_command"], "--usage-output", "fixture"))
        )
        raw_usage = report.read_json(usage_path)
        raw_usage.pop("submission_boundary", None)
        raw_usage["drain_complete"] = True
        raw_usage["tree_quiescent"] = True
        raw_usage["submission_boundary_exact"] = False
        raw_usage["measurement_exact"] = True
        raw_usage["active_thread_ids"] = []
        raw_usage["stop_reason"] = None
        thread = raw_usage["threads"][0]
        zero = dict(thread["expected_cumulative_baseline"])
        full = dict(thread["full_cumulative_projection"])
        thread.update(
            {
                "last_cumulative": full,
                "cumulative_observation_count": 1,
                "expected_cumulative_projection": full,
                "cumulative_projection_exempt_response_id": None,
                "cumulative_projection_exempt_response_usage": None,
                "observed_cumulative_baseline": zero,
                "cumulative_baseline_matches_expected": True,
                "cumulative_projection_match": True,
                "cumulative_projection_status": "matched_full_projection",
                "accounting_complete": True,
                "active_turn_id": None,
                "turn_status": "completed",
                "thread_status": "idle",
            }
        )
        parsed = self._reseal_provider_gate(
            record, raw_usage, close_reason="natural_end"
        )
        for raw_path in record["ultra_submission_boundary"]["artifacts"].values():
            Path(str(raw_path["path"])).unlink()
        Path(str(record["accepted_submission_log"])).unlink()
        Path(str(record["validation_log"])).unlink()
        record.update(
            {
                "pass": False,
                "failure_code": failure_code,
                "failure_note": "synthetic charged failure",
                "actual_stop_seconds": 1800.0 if failure_code == "TIME_LIMIT" else 25.0,
                "first_valid_seconds": None,
                "scored_elapsed_seconds": 1800.0,
                "token_usage": parsed,
                "library_use": None,
                "library_declarations": [],
                "submission_sha256": None,
                "final_submission_sha256": None,
                "accepted_submission_log": None,
                "submission_changed_after_acceptance": False,
                "validation_log": None,
                "validation_log_sha256": None,
                "validation_record_sha256": None,
                "ultra_submission_boundary": {"verified": False},
            }
        )
        record["protocol"]["verified"]["authenticated_first_valid_proof_boundary"] = False
        record["token_measurement"]["post_submission_usage_established"] = False
        record["token_measurement"]["tree_drain_complete"] = True
        self._replace_record(record)
        return str(record["run_id"])

    def make_network_rule_failure(self) -> str:
        path = sorted((self.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        marker = self.results / "logs" / f"{record['run_id']}.network-violation.marker"
        write_text(marker, "socket syscall denied\n")
        record.update(
            {
                "pass": False,
                "failure_code": "RULE_VIOLATION",
                "failure_note": "model shell attempted a forbidden socket syscall",
                "actual_stop_seconds": float(record["first_valid_seconds"]) + 1.0,
                "scored_elapsed_seconds": 1800.0,
                "network_violation": {
                    "detected": True,
                    "integrity_ok": True,
                    "event_count": 1,
                    "saved_marker_log": str(marker.resolve()),
                    "marker_sha256": report.file_sha256(marker),
                },
            }
        )
        self._replace_record(record)
        return str(record["run_id"])

    def add_qualifying_startup_retry(self) -> str:
        final_path = sorted((self.results / "records").glob("*.json"))[0]
        final = report.read_json(final_path)
        run_id = str(final["run_id"])
        attempts = self.results / "attempts"
        attempt_one = attempts / f"{run_id}.attempt-1.json"
        transcript_one = attempt_one.with_suffix(".jsonl")
        final["matrix_attempt"] = 2
        self._replace_record(final)
        write_json(attempts / f"{run_id}.attempt-2.json", final)
        write_text(
            attempts / f"{run_id}.attempt-2.jsonl",
            transcript_one.read_text(encoding="utf-8"),
        )
        startup = dict(final)
        startup["matrix_attempt"] = 1
        startup.pop("matrix_record_sha256", None)
        startup.update(
            {
                "pass": False,
                "scored": False,
                "useful_work_started": False,
                "failure_code": "SYSTEM_ERROR",
                "failure_note": "adapter failed before useful work",
                "token_usage": None,
                "token_measurement": None,
                "first_valid_seconds": None,
                "submission_sha256": None,
                "final_submission_sha256": None,
                "accepted_submission_log": None,
                "validation_log": None,
                "validation_log_sha256": None,
                "validation_record_sha256": None,
                "started_at_utc": (
                    dt.datetime.fromisoformat(str(final["started_at_utc"]))
                    - dt.timedelta(minutes=2)
                ).isoformat(),
                "finished_at_utc": (
                    dt.datetime.fromisoformat(str(final["started_at_utc"]))
                    - dt.timedelta(minutes=1)
                ).isoformat(),
            }
        )
        original_agent_log = Path(str(startup["agent_log"]))
        frozen_source_agent_log = (
            self.results
            / "attempts"
            / f"{run_id}.attempt-1.agent_log.artifact"
        )
        frozen_source_agent_log.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(original_agent_log, frozen_source_agent_log)
        startup["agent_log"] = frozen_source_agent_log.relative_to(self.results).as_posix()
        startup["agent_log_sha256"] = report.file_sha256(frozen_source_agent_log)
        write_json(attempt_one, startup)
        incident_run_id = f"{run_id}-system-attempt-1"
        incident = json.loads(json.dumps(startup))
        incident["planned_run_id"] = run_id
        incident["run_id"] = incident_run_id
        incident["scored"] = False
        incident["matrix_incident"] = {
            "status": "retryable_pre_prompt_system_error",
            "retry_allowed": True,
            "scored": False,
            "final_assignment_record_written": False,
        }
        source_agent_log = self.results / str(startup["agent_log"])
        copied_agent_log = (
            self.results
            / "incidents"
            / f"{incident_run_id}.attempt-1.{source_agent_log.name}"
        )
        copied_agent_log.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_agent_log, copied_agent_log)
        incident["agent_log"] = copied_agent_log.relative_to(self.results).as_posix()
        planned_assignment = {
            field: startup[field]
            for field in (
                "run_id",
                "pair_id",
                "task_id",
                "paper_id",
                "paper_sha256",
                "tier",
                "condition",
                "repetition_id",
                "backend_seed",
                "pair_order",
                "order_index",
            )
        }
        incident["incident_provenance"] = {
            "schema_version": 1,
            "planned_assignment": planned_assignment,
            "matrix_attempt": 1,
            "source_attempt": {
                "path": f"attempts/{run_id}.attempt-1.json",
                "sha256": report.file_sha256(attempt_one),
            },
            "transcript": {
                "path": f"attempts/{run_id}.attempt-1.jsonl",
                "sha256": report.file_sha256(transcript_one),
            },
        }
        incident["matrix_incident_sha256"] = report.document_sha256(incident)
        write_json(self.results / "incidents" / f"{run_id}.attempt-1.json", incident)
        stream = [
            json.loads(line)
            for line in (self.results / "runs.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        rebuilt: list[dict[str, object]] = []
        for item in stream:
            if item.get("run_id") == run_id:
                rebuilt.append(incident)
            rebuilt.append(item)
        write_text(
            self.results / "runs.jsonl",
            "".join(json.dumps(item, sort_keys=True) + "\n" for item in rebuilt),
        )
        return run_id


class RenderP01ReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.token_canary_verifier = mock.patch.object(
            token_canary,
            "validate_attestation_document",
            side_effect=self._verify_fixture_token_canary,
        )
        self.ultra_canary_verifier = mock.patch.object(
            ultra_canary,
            "verify_frozen_attestation",
            side_effect=self._verify_fixture_ultra_canary,
        )
        self.token_canary_verifier.start()
        self.ultra_canary_verifier.start()
        self.fixture = SyntheticP01Fixture(Path(self.temporary.name))

    def tearDown(self) -> None:
        self.ultra_canary_verifier.stop()
        self.token_canary_verifier.stop()
        self.temporary.cleanup()

    @staticmethod
    def _verified_fixture_artifacts(
        evidence: dict[str, object],
        project_root: Path,
        expected_labels: tuple[str, ...],
    ) -> dict[str, dict[str, object]]:
        artifacts = evidence.get("artifacts")
        if not isinstance(artifacts, dict) or set(artifacts) != set(expected_labels):
            raise BenchmarkToolError("synthetic canary artifact set is incomplete")
        artifact_root = project_root / str(evidence.get("artifact_root"))
        verified: dict[str, dict[str, object]] = {}
        for label in expected_labels:
            raw = artifacts[label]
            if not isinstance(raw, dict):
                raise BenchmarkToolError("synthetic canary artifact is malformed")
            path = artifact_root / str(raw.get("path"))
            if (
                not path.is_file()
                or report.file_sha256(path) != raw.get("sha256")
            ):
                raise BenchmarkToolError("synthetic canary artifact failed authentication")
            verified[label] = {
                "path": raw["path"],
                "sha256": raw["sha256"],
                "bytes": path.stat().st_size,
            }
        return verified

    @classmethod
    def _verify_fixture_token_canary(
        cls,
        evidence: dict[str, object],
        *,
        project_root: Path,
        expected_benchmark_id: str,
        expected_agent: dict[str, object],
        expected_frozen_token_limit: int,
    ) -> dict[str, object]:
        outcome = evidence.get("outcome")
        if (
            evidence.get("kind") != token_canary.EVIDENCE_KIND
            or evidence.get("canary_id") != token_canary.CANARY_ID
            or evidence.get("benchmark_id") != expected_benchmark_id
            or evidence.get("agent") != expected_agent
            or evidence.get("scored") is not False
            or evidence.get("matrix_assignment") is not False
            or evidence.get("synthetic_input") is not True
            or evidence.get("benchmark_task_bytes_used") is not False
            or expected_frozen_token_limit != 5_000_000
            or not isinstance(outcome, dict)
            or outcome.get("thread_count") != 1
            or outcome.get("response_count") != 2
            or outcome.get("drain_complete") is not False
            or outcome.get("measurement_exact") is not True
        ):
            raise BenchmarkToolError(
                "synthetic token-canary lacks an exact root-only provider crossing"
            )
        artifacts = cls._verified_fixture_artifacts(
            evidence, project_root, token_canary.ARTIFACT_LABELS
        )
        return {
            "status": "passed",
            "canary_limit_tokens": token_canary.DEFAULT_CANARY_TOKEN_LIMIT,
            "first_crossing_tokens": outcome["first_crossing_tokens"],
            "final_endpoint_tokens": outcome["total_model_tokens"],
            "thread_count": 1,
            "observed_child_thread_count": 0,
            "response_count": 2,
            "drain_complete": False,
            "provider_gate_quiescent": True,
            "measurement_exact": True,
            "synthetic_input": True,
            "matrix_assignment": False,
            "benchmark_task_bytes_used": False,
            "prompt_protocol": token_canary.PROMPT_PROTOCOL,
            "prompt_release": token_canary_prompt_release_summary(),
            "source_separation_audit_sha256": "c" * 64,
            "accounting_projection": outcome["accounting_projection"],
            "artifacts": artifacts,
        }

    @classmethod
    def _verify_fixture_ultra_canary(
        cls,
        project_root: Path,
        descriptor: dict[str, object],
        *,
        expected_benchmark_id: str,
        expected_agent: dict[str, object],
        expected_token_limit: int,
        expected_prompt_protocol: dict[str, object],
        expected_execution_components: dict[str, object],
    ) -> dict[str, object]:
        evidence_path = project_root / ultra_canary.FROZEN_EVIDENCE_PATH
        evidence = report.read_json(evidence_path)
        controls = evidence.get("controls")
        outcome = evidence.get("outcome")
        if (
            descriptor.get("path") != ultra_canary.FROZEN_EVIDENCE_PATH
            or descriptor.get("sha256") != report.file_sha256(evidence_path)
            or evidence.get("kind") != ultra_canary.EVIDENCE_KIND
            or evidence.get("canary_id") != ultra_canary.CANARY_ID
            or evidence.get("benchmark_id") != expected_benchmark_id
            or evidence.get("agent") != expected_agent
            or evidence.get("scored") is not False
            or evidence.get("matrix_assignment") is not False
            or evidence.get("synthetic_input") is not True
            or expected_token_limit != 5_000_000
            or not isinstance(controls, dict)
            or controls.get("production_dependency_audit_required") is not True
            or controls.get("dependency_audit_complete_required") is not True
            or not isinstance(outcome, dict)
            or outcome.get("measurement_exact") is not True
            or outcome.get("submission_boundary_exact") is not True
            or outcome.get("drain_complete") is not False
            or outcome.get("root_active_at_boundary") is not True
            or outcome.get("positive_usage_descendant_thread_count") != 1
        ):
            raise BenchmarkToolError(
                "Ultra canary lacks the blocked boundary or production dependency audit"
            )
        artifacts = cls._verified_fixture_artifacts(
            evidence, project_root, ultra_canary.ARTIFACT_LABELS
        )
        raw_artifacts = evidence.get("artifacts")
        if not isinstance(raw_artifacts, dict):
            raise BenchmarkToolError("synthetic Ultra canary artifacts are malformed")
        freeze_descriptor = raw_artifacts.get("freeze_check")
        if not isinstance(freeze_descriptor, dict):
            raise BenchmarkToolError("synthetic Ultra canary freeze is missing")
        freeze = report.read_json(
            project_root
            / str(evidence.get("artifact_root"))
            / str(freeze_descriptor.get("path"))
        )
        if freeze.get("prompt_protocol") != dict(expected_prompt_protocol):
            raise BenchmarkToolError(
                "synthetic Ultra canary production prompt protocol is stale"
            )
        if freeze.get("execution_components") != dict(
            expected_execution_components
        ):
            raise BenchmarkToolError(
                "synthetic Ultra canary production execution components are stale"
            )
        return {
            "path": ultra_canary.FROZEN_EVIDENCE_PATH,
            "sha256": descriptor["sha256"],
            "status": "passed",
            "thread_count": 2,
            "observed_descendant_thread_count": 1,
            "positive_usage_descendant_thread_count": 1,
            "response_count": 1,
            "total_model_tokens": 1_000,
            "drain_complete": False,
            "measurement_exact": True,
            "submission_boundary_exact": True,
            "accounting_projection": outcome["accounting_projection"],
            "prompt_release": ultra_canary_prompt_release_summary(),
            "dependency_audit": {
                "complete": True,
                "helper_sha256": "d" * 64,
                "command_sha256": "e" * 64,
                "library_use": False,
                "library_declarations": [],
                "target_seen": True,
                "semantic_type_equal": True,
            },
            "validation_authentication": {"authenticated": True},
            "barrier": {
                **nested_submission_wire_fixture(),
                "sequence": 1,
                "challenge_sha256": "1" * 64,
                "call_sha256": "2" * 64,
                "request_sha256": "3" * 64,
                "ack_sha256": "4" * 64,
                "candidate_sha256": "5" * 64,
                "candidate_size_bytes": 101,
                "validator_contract_sha256": "6" * 64,
                "outer_raw_item_and_call_ids_pairwise_distinct": True,
                "inner_dynamic_item_started": True,
                "inner_submit_invocation_exact": True,
                "inner_submit_only_nested_tool_call": True,
                "captured_at_monotonic_ns": 10,
                "raw_response_observed_at_monotonic_ns": 11,
                "request_published_at_monotonic_ns": 12,
                "raw_response_completed_before_boundary_publication": True,
                "submission_event_order": (
                    "inner_dynamic_call_before_raw_response_completed"
                ),
                "dynamic_call_observed_before_raw_response_completed": True,
                "raw_response_completed_before_dynamic_call_observed": False,
                "retained_read_only": True,
            },
            "artifacts": artifacts,
        }

    def render(self, suffix: str = "report") -> dict[str, object]:
        return report.build_report(
            self.fixture.benchmark,
            self.fixture.results,
            Path(self.temporary.name) / suffix,
            compile_pdf=False,
        )

    def _canary_binding_kwargs(self) -> dict[str, object]:
        config = report.read_json(self.fixture.metadata / "config.json")
        environment = report.read_json(self.fixture.metadata / "environment.json")
        prompt_protocol, execution_components = run_matrix.production_freeze_bindings(
            config, environment
        )
        return {
            "prompt_protocol": prompt_protocol,
            "execution_components": execution_components,
        }

    def _tamper_canary_production_freeze(
        self, descriptor_value: dict[str, object], *, field: str
    ) -> None:
        evidence_path = self.fixture.project / str(descriptor_value["path"])
        evidence = report.read_json(evidence_path)
        artifact_root = self.fixture.project / str(evidence["artifact_root"])
        freeze_descriptor = evidence["artifacts"]["freeze_check"]
        freeze_path = artifact_root / str(freeze_descriptor["path"])
        freeze = report.read_json(freeze_path)
        if field == "prompt_protocol":
            freeze["prompt_protocol"] = {
                **freeze["prompt_protocol"],
                "version": "stale-production-prompt",
            }
        elif field == "execution_components":
            freeze["execution_components"] = {
                **freeze["execution_components"],
                run_matrix.EXECUTION_COMPONENT_FIELDS[0]: "f" * 64,
            }
        else:  # pragma: no cover - fixture helper contract
            raise AssertionError(field)
        write_json(freeze_path, freeze)
        freeze_descriptor["sha256"] = report.file_sha256(freeze_path)
        write_json(evidence_path, evidence)
        descriptor_value["sha256"] = report.file_sha256(evidence_path)

    def test_valid_18_run_fixture_generates_private_standalone_report(self) -> None:
        value = self.render()
        self.assertEqual(value["final_scored_record_count"], 18)
        self.assertFalse(value["public_release"])
        output = Path(self.temporary.name) / "report"
        tex = (output / "HighamBench_P01_Checkpoint_Report.tex").read_text(encoding="utf-8")
        self.assertIn("PRIVATE / NOT FOR PUBLIC RELEASE", tex)
        self.assertIn("actual measured records", tex)
        self.assertIn("tikzpicture", tex)
        self.assertIn("longtable", tex)
        summary = report.read_json(output / "summary.json")
        self.assertTrue(summary["uncertainty"]["whole_paper_resampling_degenerate"])
        self.assertEqual(report.read_json(output / "validation.json")["submission_boundary_count"], 18)
        self.assertEqual(
            set(summary["uncertainty"]["metrics"]),
            {
                "pass_rate_difference",
                "median_scored_seconds_difference",
                "median_model_tokens_difference",
            },
        )
        self.assertIn("P02 T1, T2, and T3 construction proofs passed", tex)
        self.assertIn("no P02 benchmark measurements", tex)
        self.assertIn("signposted-library-v1", tex)
        self.assertIn("private unseeded repetitions", tex)
        self.assertIn("READY, GO, and RELEASED", tex)
        self.assertIn("immediately before the exact", tex)
        self.assertIn("separate frozen 120-second timeout", tex)
        self.assertIn("post-submission validation reserve", tex)
        self.assertIn("synthetic Token V8 provider-gate", tex)
        self.assertIn("Ultra V12 orchestration probe", tex)
        self.assertIn("Authenticated provider-gate endpoint", tex)
        self.assertIn(r"accepted\_provider\_gate\_close", tex)
        self.assertIn("CLI flag present=\\texttt{true}", tex)
        self.assertIn("effective source=", tex)
        self.assertIn("thread\\_start\\_config", tex)
        self.assertNotIn("observational", tex.lower())
        provenance = value["provenance"]
        self.assertEqual(
            provenance["canaries"]["token_control"]["artifact_count"],
            len(token_canary.ARTIFACT_LABELS),
        )
        self.assertEqual(
            provenance["canaries"]["ultra_orchestration"]["artifact_count"],
            len(ultra_canary.ARTIFACT_LABELS),
        )
        self.assertTrue(
            provenance["canaries"]["ultra_orchestration"]["dependency_audit"][
                "complete"
            ]
        )
        self.assertEqual(
            provenance["prompt_release_authentication"][
                "retained_artifact_file_count"
            ],
            54,
        )
        self.assertTrue(
            provenance["matrix_record_authentication"][
                "all_selected_final_records_authenticated"
            ]
        )
        self.assertEqual(
            provenance["matrix_incident_authentication"][
                "resolved_pre_prompt_retry_count"
            ],
            0,
        )
        self.assertIn("No resolved pre-prompt startup retries", tex)
        self.assertIn("schema-v5", tex)
        self.assertIn("XOR", tex)
        self.assertEqual(
            {
                row["proof"]["submission_boundary"]["submission_event_order"]
                for row in value["runs"]
            },
            {
                "inner_dynamic_call_before_raw_response_completed",
                "raw_response_completed_before_inner_dynamic_call",
            },
        )
        hardware = provenance["hardware_records"][0]
        self.assertEqual(hardware["allocated_gpu_count"], 0)
        self.assertEqual(hardware["alloc_tres"], "billing=4,cpu=4,mem=32G,node=1")
        self.assertEqual(
            hardware["gpu_environment"],
            {
                "SLURM_GPUS_ON_NODE": "0",
                "SLURM_JOB_GPUS": None,
                "CUDA_VISIBLE_DEVICES": "",
            },
        )
        self.assertIn("GPU=0", tex)
        self.assertIn("exact GPU environment", tex)

    def test_token_canary_rejects_compaction_as_its_below_cap_call(self) -> None:
        with self.assertRaisesRegex(
            construction_report.ReportError, "Token V8 gate shape"
        ):
            construction_report._validate_token_canary_provider_gate_shape(
                {
                    "endpoint": "sanitized_provider_gate_crossing",
                    "response_count": 2,
                    "request_kinds": ["compaction", "compaction"],
                    "release_kinds": [
                        "byte_identity",
                        runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
                    ],
                    "superseded_by_collaboration_message_response_count": 0,
                    "superseded_by_collaboration_message_response_ids": [],
                    "discarded_after_explicit_child_interrupt_response_count": 0,
                    "discarded_after_explicit_child_interrupt_response_ids": [],
                    "first_crossing": {
                        "request_kind": "compaction",
                        "release_kind": (
                            runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
                        ),
                    },
                },
                "P01 token canary",
            )

    def test_canary_uses_current_delivery_and_usage_reconciliation_fields(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor = config["frozen_environment"]["token_control_canary"]
        summary = report._authenticate_canary(
            self.fixture.benchmark,
            descriptor,
            name="token-control canary",
            benchmark_id=self.fixture.benchmark_id,
            agent=report._expected_canary_agent(config),
            token_limit=self.fixture.token_limit,
            **self._canary_binding_kwargs(),
        )
        self.assertTrue(
            summary["accounting_projection"][
                "provider_gate_deliveries_reconciled"
            ]
        )
        self.assertIn(
            "provider_usage_reconciliation", summary["accounting_projection"]
        )
        reconciliation = summary["accounting_projection"][
            "provider_usage_reconciliation"
        ]
        self.assertEqual(
            reconciliation[
                "discarded_after_explicit_child_interrupt_response_count"
            ],
            0,
        )
        self.assertEqual(
            reconciliation["discarded_after_explicit_child_interrupt_evidence"],
            [],
        )

        evidence_path = self.fixture.project / descriptor["path"]
        evidence = report.read_json(evidence_path)
        projection = evidence["outcome"]["accounting_projection"]
        projection["provider_gate_appserver_deliveries_reconciled"] = projection.pop(
            "provider_gate_deliveries_reconciled"
        )
        projection["projection_payload_sha256"] = report.document_sha256(
            {
                key: value
                for key, value in projection.items()
                if key != "projection_payload_sha256"
            }
        )
        write_json(evidence_path, evidence)
        descriptor["sha256"] = report.file_sha256(evidence_path)
        with self.assertRaisesRegex(report.ReportError, "provider-gate crossing"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor,
                name="token-control canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_alloc_tres_zero_gpu_parser_rejects_gpu_and_malformed_tokens(self) -> None:
        self.assertEqual(
            report._validate_zero_gpu_alloc_tres(
                "billing=4,cpu=4,mem=32G,node=1", "synthetic AllocTRES"
            ),
            "billing=4,cpu=4,mem=32G,node=1",
        )
        self.assertEqual(
            report._validate_zero_gpu_alloc_tres(
                "cpu=4,gres/gpu=0,gres/gpu:a100=0", "synthetic AllocTRES"
            ),
            "cpu=4,gres/gpu=0,gres/gpu:a100=0",
        )
        invalid = (
            "cpu=4,gres/gpu=1",
            "cpu=4,gres/gpu:a100=2",
            "cpu=4,gres/gpu=none",
            "cpu=4,gres/gpu:=0",
            "cpu=4,GRES/GPU=0",
            "cpu=4,gres/gpu=00",
            "cpu=4,gres/gpu",
            "cpu=4,,node=1",
            "cpu=4,cpu=4",
        )
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(report.ReportError):
                report._validate_zero_gpu_alloc_tres(value, "synthetic AllocTRES")

    def test_gpu_environment_requires_exact_zero_gpu_snapshot(self) -> None:
        valid = {
            "SLURM_GPUS_ON_NODE": "0",
            "SLURM_JOB_GPUS": None,
            "CUDA_VISIBLE_DEVICES": "",
        }
        self.assertEqual(
            report._validate_zero_gpu_environment(valid, "synthetic GPU environment"),
            valid,
        )
        invalid_snapshots = (
            {**valid, "SLURM_GPUS_ON_NODE": "1"},
            {**valid, "SLURM_JOB_GPUS": "0"},
            {**valid, "CUDA_VISIBLE_DEVICES": "0"},
            {**valid, "SLURM_GPUS_ON_NODE": 0},
            {key: value for key, value in valid.items() if key != "SLURM_JOB_GPUS"},
            {**valid, "EXTRA_GPU_FIELD": None},
        )
        for value in invalid_snapshots:
            with self.subTest(value=value), self.assertRaises(report.ReportError):
                report._validate_zero_gpu_environment(
                    value, "synthetic GPU environment"
                )

    def test_schema_v5_submission_event_orders_are_exact_and_timestamp_bound(self) -> None:
        dynamic_first = {
            "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
            "inner_dynamic_item_started_at_monotonic_ns": 10,
            "captured_at_monotonic_ns": 11,
            "raw_response_observed_at_monotonic_ns": 12,
            "request_published_at_monotonic_ns": 13,
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": (
                "inner_dynamic_call_before_raw_response_completed"
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
        }
        response_first = {
            **dynamic_first,
            "inner_dynamic_item_started_at_monotonic_ns": 11,
            "captured_at_monotonic_ns": 12,
            "raw_response_observed_at_monotonic_ns": 10,
            "submission_event_order": (
                "raw_response_completed_before_inner_dynamic_call"
            ),
            "dynamic_call_observed_before_raw_response_completed": False,
            "raw_response_completed_before_dynamic_call_observed": True,
        }
        self.assertEqual(
            report._validate_submission_event_order(
                dynamic_first, "dynamic-first", require_event_timestamps=True
            ),
            "inner_dynamic_call_before_raw_response_completed",
        )
        self.assertEqual(
            report._validate_submission_event_order(
                response_first, "response-first", require_event_timestamps=True
            ),
            "raw_response_completed_before_inner_dynamic_call",
        )
        invalid = (
            {**dynamic_first, "schema_version": 1},
            {**dynamic_first, "schema_version": 2},
            {**dynamic_first, "schema_version": 3},
            {**dynamic_first, "schema_version": 4},
            {
                **dynamic_first,
                "dynamic_call_observed_before_raw_response_completed": True,
                "raw_response_completed_before_dynamic_call_observed": True,
            },
            {
                **dynamic_first,
                "dynamic_call_observed_before_raw_response_completed": False,
                "raw_response_completed_before_dynamic_call_observed": False,
            },
            {
                **dynamic_first,
                "submission_event_order": (
                    "raw_response_completed_before_inner_dynamic_call"
                ),
            },
            {
                **dynamic_first,
                "raw_response_observed_at_monotonic_ns": 9,
            },
            {
                **dynamic_first,
                "request_published_at_monotonic_ns": 11,
            },
            {
                **dynamic_first,
                "raw_response_completed_before_boundary_publication": False,
            },
        )
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(report.ReportError):
                report._validate_submission_event_order(
                    value, "invalid-order", require_event_timestamps=True
                )

    def test_library_uptake_denominator_is_passing_l_only(self) -> None:
        failed = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        value = self.render("library-denominator")
        l = value["analysis"]["by_condition"]["L"]
        self.assertEqual(l["library_use_denominator_passing_l"], 8)
        self.assertLessEqual(l["library_use_numerator_among_passing_l"], 8)
        self.assertIsNone(
            next(row for row in value["runs"] if row["run_id"] == failed)["library_use"]
        )

    def test_bootstrap_uses_median_for_time_and_tokens(self) -> None:
        pairs = [
            {
                "l_minus_n_pass": 0,
                "l_minus_n_scored_seconds": value,
                "l_minus_n_model_tokens": int(value),
            }
            for value in (0, 0, 0, 0, 0, 0, 0, 0, 900)
        ]
        uncertainty = report._bootstrap(pairs, "whole-paper-seed")
        self.assertEqual(
            uncertainty["metrics"]["median_scored_seconds_difference"]["estimate"], 0
        )
        self.assertEqual(
            uncertainty["metrics"]["median_model_tokens_difference"]["estimate"], 0
        )

    def test_agent_command_prompt_path_tamper_is_rejected(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        index = record["agent_command"].index("--prompt-file") + 1
        record["agent_command"][index] = str((self.fixture.results / "wrong.md").resolve())
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "wrong staged common prompt"):
            self.render("prompt-path-tamper")

    def test_matrix_record_content_tamper_without_reseal_is_rejected(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["agent_exit_code"] = 77
        self.fixture._replace_record(record, reseal_matrix_record=False)
        with self.assertRaisesRegex(
            report.ReportError, "matrix final-record authentication"
        ):
            self.render("matrix-content-tamper")

    def test_resealed_nonclean_adapter_exit_is_rejected(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        original = report.read_json(path)
        for invalid_exit in (2, False, 0.0, None):
            with self.subTest(agent_exit_code=invalid_exit):
                record = json.loads(json.dumps(original))
                record["agent_exit_code"] = invalid_exit
                self.fixture._replace_record(record)
                with self.assertRaisesRegex(
                    report.ReportError, "clean adapter exit"
                ):
                    self.render(f"nonclean-exit-{invalid_exit!r}")

    def test_swapped_final_assignment_with_valid_self_hash_is_rejected(self) -> None:
        paths = sorted((self.fixture.results / "records").glob("*.json"))
        first = report.read_json(paths[0])
        second = next(
            report.read_json(path)
            for path in paths[1:]
            if report.read_json(path)["task_id"] != first["task_id"]
        )
        first["task_id"] = second["task_id"]
        self.fixture._replace_record(first)
        with self.assertRaisesRegex(report.ReportError, "has task_id="):
            self.render("swapped-assignment")

    def test_prompt_release_file_byte_tamper_is_rejected(self) -> None:
        record = report.read_json(
            sorted((self.fixture.results / "records").glob("*.json"))[0]
        )
        released = Path(str(record["prompt_release"]["released"]["path"]))
        payload = released.read_bytes()
        released.chmod(0o644)
        released.write_bytes(payload + b" ")
        released.chmod(0o444)
        with self.assertRaisesRegex(
            report.ReportError, "RELEASED retained file failed exact authentication"
        ):
            self.render("prompt-release-byte-tamper")

    def test_swapped_prompt_artifact_is_rejected(self) -> None:
        paths = sorted((self.fixture.results / "records").glob("*.json"))
        first = report.read_json(paths[0])
        second = report.read_json(paths[1])
        replacement = second["prompt_release"]["ready"]
        first["prompt_release"]["ready"] = replacement
        first["prompt_release"]["artifact_paths"]["ready"] = replacement["path"]
        option = first["agent_command"].index("--prompt-ready-output") + 1
        first["agent_command"][option] = replacement["path"]
        self.fixture._replace_record(first)
        with self.assertRaisesRegex(
            report.ReportError, "not command/usage bound|usage-derived"
        ):
            self.render("swapped-prompt-artifact")

    def test_prompt_release_timeout_tamper_is_rejected(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["prompt_release"]["startup_timeout_seconds"] = 119.0
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(
            report.ReportError, "inexact authenticated prompt-release summary"
        ):
            self.render("prompt-timeout-tamper")

    def test_prompt_release_protocol_verification_is_required(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["protocol"]["verified"]["authenticated_prompt_release"] = False
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(
            report.ReportError, "authenticated_prompt_release"
        ):
            self.render("prompt-protocol-tamper")

    def test_first_valid_time_cannot_use_dynamic_call_capture(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["first_valid_seconds"] = 5.0
        record["scored_elapsed_seconds"] = 5.0
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(
            report.ReportError, "authenticated request publication"
        ):
            self.render("captured-at-is-not-endpoint")

    def test_l_supplement_must_contain_search_paths_and_permission(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        environment = report.read_json(self.fixture.metadata / "environment.json")
        supplement = self.fixture.benchmark / "condition_prompts" / "L.md"
        write_text(supplement, "Use a library.\n")
        descriptor_value = config["frozen_environment"]["prompt_protocol"][
            "condition_supplements"
        ]["L"]
        descriptor_value["sha256"] = report.file_sha256(supplement)
        descriptor_value["bytes"] = supplement.stat().st_size
        with self.assertRaisesRegex(report.ReportError, "search/use instructions"):
            report._signposted_protocol_check(self.fixture.benchmark, config, environment)

    def test_user_directed_identical_prompt_departure_is_required(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        environment = report.read_json(self.fixture.metadata / "environment.json")
        environment["known_reference_protocol_deviations"] = []
        with self.assertRaisesRegex(report.ReportError, "PDF section 3"):
            report._signposted_protocol_check(self.fixture.benchmark, config, environment)

    def test_p02_construction_failure_is_rejected(self) -> None:
        certificate = self.fixture.metadata / "evidence" / "construction_validation_full_current.json"
        value = report.read_json(certificate)
        result = next(item for item in value["results"] if item["task_id"] == "P02-T1")
        result["pass"] = False
        write_json(certificate, value)
        manifest = report.read_json(self.fixture.metadata / "manifest.json")
        with self.assertRaisesRegex(report.ReportError, "duplicate or failed result"):
            report._construction_check(self.fixture.benchmark, manifest)

    def test_self_contained_construction_proof_needs_no_helper_build(self) -> None:
        certificate = self.fixture.metadata / "evidence" / "construction_validation_full_current.json"
        value = report.read_json(certificate)
        result = next(
            item
            for item in value["results"]
            if item["task_id"] == "P01-T3" and item["condition"] == "N"
        )
        result["helpers"] = []
        write_json(certificate, value)
        certificate_sha = report.file_sha256(certificate)
        for filename in ("condition_n_preflight.json", "library_dependency_probe.json"):
            pointer_path = self.fixture.metadata / "evidence" / filename
            pointer = report.read_json(pointer_path)
            pointer["current_evidence_sha256"] = certificate_sha
            write_json(pointer_path, pointer)
        manifest = report.read_json(self.fixture.metadata / "manifest.json")
        summary = report._construction_check(self.fixture.benchmark, manifest)
        self.assertEqual(summary["passed"], 120)

    def test_backend_seed_must_be_explicitly_null(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        config["repetitions"][0]["backend_seed"] = 17
        manifest = report.read_json(self.fixture.metadata / "manifest.json")
        run_order = report.read_json(self.fixture.metadata / "run_order.json")
        tasks = report._manifest_tasks(self.fixture.benchmark, manifest)
        with self.assertRaisesRegex(report.ReportError, "backend_seed=null"):
            report._expected_assignments(config, run_order, tasks)

    def test_ultra_canary_without_blocked_boundary_is_rejected(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["ultra_orchestration_canary"]
        evidence_path = self.fixture.project / descriptor_value["path"]
        evidence = report.read_json(evidence_path)
        evidence["outcome"].update(
            {
                "submission_boundary_exact": False,
                "drain_complete": True,
                "root_active_at_boundary": False,
            }
        )
        write_json(evidence_path, evidence)
        descriptor_value["sha256"] = report.file_sha256(evidence_path)
        with self.assertRaisesRegex(report.ReportError, "blocked boundary"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="Ultra orchestration canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_token_canary_must_use_canonical_synthetic_v5_identity(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["token_control_canary"]
        evidence_path = self.fixture.project / descriptor_value["path"]
        evidence = report.read_json(evidence_path)
        evidence["canary_id"] = "P01-T1"
        write_json(evidence_path, evidence)
        descriptor_value["sha256"] = report.file_sha256(evidence_path)
        with self.assertRaisesRegex(report.ReportError, "root-only provider crossing"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="token-control canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_token_canary_rejects_stale_production_prompt_binding(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["token_control_canary"]
        self._tamper_canary_production_freeze(
            descriptor_value, field="prompt_protocol"
        )
        with self.assertRaisesRegex(report.ReportError, "prompt protocol is stale"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="token-control canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_token_canary_rejects_stale_execution_component_binding(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["token_control_canary"]
        self._tamper_canary_production_freeze(
            descriptor_value, field="execution_components"
        )
        with self.assertRaisesRegex(report.ReportError, "execution components are stale"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="token-control canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_ultra_canary_rejects_stale_production_prompt_binding(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["ultra_orchestration_canary"]
        self._tamper_canary_production_freeze(
            descriptor_value, field="prompt_protocol"
        )
        with self.assertRaisesRegex(report.ReportError, "prompt protocol is stale"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="Ultra orchestration canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_ultra_canary_rejects_stale_execution_component_binding(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["ultra_orchestration_canary"]
        self._tamper_canary_production_freeze(
            descriptor_value, field="execution_components"
        )
        with self.assertRaisesRegex(report.ReportError, "execution components are stale"):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="Ultra orchestration canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_canary_prompt_release_summaries_are_fail_closed(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        agent = report._expected_canary_agent(config)

        token_descriptor = config["frozen_environment"]["token_control_canary"]
        token_evidence = report.read_json(
            self.fixture.project / token_descriptor["path"]
        )
        token_summary = self._verify_fixture_token_canary(
            token_evidence,
            project_root=self.fixture.project,
            expected_benchmark_id=self.fixture.benchmark_id,
            expected_agent=agent,
            expected_frozen_token_limit=self.fixture.token_limit,
        )
        token_summary["prompt_release"]["startup_timeout_seconds"] = 119  # type: ignore[index]
        with mock.patch.object(
            token_canary,
            "validate_attestation_document",
            return_value=token_summary,
        ), self.assertRaisesRegex(report.ReportError, "prompt release"):
            report._authenticate_canary(
                self.fixture.benchmark,
                token_descriptor,
                name="token-control canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=agent,
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

        ultra_descriptor = config["frozen_environment"]["ultra_orchestration_canary"]
        ultra_summary = self._verify_fixture_ultra_canary(
            self.fixture.project,
            ultra_descriptor,
            expected_benchmark_id=self.fixture.benchmark_id,
            expected_agent=agent,
            expected_token_limit=self.fixture.token_limit,
            expected_prompt_protocol=self._canary_binding_kwargs()[
                "prompt_protocol"
            ],
            expected_execution_components=self._canary_binding_kwargs()[
                "execution_components"
            ],
        )
        ultra_summary["prompt_release"]["request_publication_timing_verified"] = False  # type: ignore[index]
        with mock.patch.object(
            ultra_canary,
            "verify_frozen_attestation",
            return_value=ultra_summary,
        ), self.assertRaisesRegex(report.ReportError, "request publication"):
            report._authenticate_canary(
                self.fixture.benchmark,
                ultra_descriptor,
                name="Ultra orchestration canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=agent,
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_ultra_canary_requires_19_artifacts_and_dependency_audit(self) -> None:
        config = report.read_json(self.fixture.metadata / "config.json")
        descriptor_value = config["frozen_environment"]["ultra_orchestration_canary"]
        evidence_path = self.fixture.project / descriptor_value["path"]
        evidence = report.read_json(evidence_path)
        evidence["controls"]["dependency_audit_complete_required"] = False
        evidence["artifacts"].pop("dependency_audit_helper")
        write_json(evidence_path, evidence)
        descriptor_value["sha256"] = report.file_sha256(evidence_path)
        with self.assertRaisesRegex(
            report.ReportError, "production dependency audit|artifact set"
        ):
            report._authenticate_canary(
                self.fixture.benchmark,
                descriptor_value,
                name="Ultra orchestration canary",
                benchmark_id=self.fixture.benchmark_id,
                agent=report._expected_canary_agent(config),
                token_limit=self.fixture.token_limit,
                **self._canary_binding_kwargs(),
            )

    def test_tampered_accepted_proof_is_rejected(self) -> None:
        accepted = next((self.fixture.results / "logs").glob("*.accepted.lean"))
        accepted.write_text("tampered\n", encoding="utf-8")
        with self.assertRaisesRegex(report.ReportError, "accepted proof hash|immutable candidate"):
            self.render("tampered-report")

    def test_partial_checkpoint_is_rejected(self) -> None:
        record = next((self.fixture.results / "records").glob("*.json"))
        record.unlink()
        with self.assertRaisesRegex(report.ReportError, "exactly the 18"):
            self.render("partial-report")

    def test_symlinked_final_record_is_rejected(self) -> None:
        record_path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        run_id = record_path.stem
        attempt_path = self.fixture.results / "attempts" / f"{run_id}.attempt-1.json"
        record_path.unlink()
        record_path.symlink_to(attempt_path)
        with self.assertRaisesRegex(report.ReportError, "symlinked JSON"):
            self.render("symlinked-final-record")

    def test_symlinked_attempt_record_is_rejected(self) -> None:
        attempt_path = sorted((self.fixture.results / "attempts").glob("*.json"))[0]
        run_id = attempt_path.name.removesuffix(".attempt-1.json")
        record_path = self.fixture.results / "records" / f"{run_id}.json"
        attempt_path.unlink()
        attempt_path.symlink_to(record_path)
        with self.assertRaisesRegex(report.ReportError, "attempt record.*symlinked"):
            self.render("symlinked-attempt-record")

    def test_symlinked_incident_record_is_rejected(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        incident_path = self.fixture.results / "incidents" / f"{run_id}.attempt-1.json"
        source_path = self.fixture.results / "attempts" / f"{run_id}.attempt-1.json"
        incident_path.unlink()
        incident_path.symlink_to(source_path)
        with self.assertRaisesRegex(report.ReportError, "incident record.*symlinked"):
            self.render("symlinked-incident-record")

    def test_any_p02_record_is_rejected(self) -> None:
        source = report.read_json(next((self.fixture.results / "records").glob("*.json")))
        source["run_id"] = "P02-T1-rep-01-N"
        source["paper_id"] = "P02"
        write_json(self.fixture.results / "attempts" / "P02-T1-rep-01-N.attempt-1.json", source)
        with self.assertRaisesRegex(report.ReportError, r"P02\+"):
            self.render("p02-report")

    def test_scored_l_no_submission_allows_unknown_library_use(self) -> None:
        no_submission = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        value = self.render("charged-failures-report")
        rows = {item["run_id"]: item for item in value["runs"]}
        self.assertIsNone(rows[no_submission]["library_use"])
        self.assertEqual(value["analysis"]["overall"]["failures"], 1)

    def test_resealed_ultra_time_limit_is_not_a_scored_final(self) -> None:
        self.fixture.make_l_failure(0, "TIME_LIMIT")
        with self.assertRaisesRegex(
            report.ReportError, "TIME_LIMIT cannot be an exact natural-drain final"
        ):
            self.render("resealed-time-limit-report")

    def test_network_rule_failure_retains_authenticated_accepted_proof(self) -> None:
        run_id = self.fixture.make_network_rule_failure()
        value = self.render("network-failure-report")
        row = next(item for item in value["runs"] if item["run_id"] == run_id)
        self.assertFalse(row["pass"])
        self.assertEqual(row["failure_code"], "RULE_VIOLATION")
        self.assertIsNotNone(row["proof"])

    def test_valid_request_before_cap_may_finish_validation_after_cap(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        request_elapsed = self.fixture.wall_limit - 1.0
        reserve_boundary = (
            request_elapsed + report.POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
        )
        self.fixture.retime_accepted_record(
            record,
            request_elapsed=request_elapsed,
            validator_elapsed=reserve_boundary,
            actual_stop=reserve_boundary,
        )
        value = self.render("late-hidden-validation")
        row = next(item for item in value["runs"] if item["run_id"] == record["run_id"])
        self.assertTrue(row["pass"])
        self.assertLess(row["scored_elapsed_seconds"], self.fixture.wall_limit)
        self.assertGreater(row["actual_stop_seconds"], self.fixture.wall_limit)

    def test_post_submission_validation_cannot_exceed_frozen_reserve(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["actual_stop_seconds"] = (
            float(record["first_valid_seconds"])
            + report.POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
            + 0.001
        )
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "post-submission validation reserve"):
            self.render("post-submission-validation-over-reserve")

    def test_scored_call_time_cannot_exceed_authenticated_validator_time(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["first_valid_seconds"] = 100.0
        record["scored_elapsed_seconds"] = 100.0
        record["actual_stop_seconds"] = 100.0
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "not monotonically bound"):
            self.render("scored-time-tamper")

    def test_no_submission_keeps_priority_over_authenticated_network_event(self) -> None:
        run_id = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        path = self.fixture.results / "records" / f"{run_id}.json"
        record = report.read_json(path)
        marker = self.fixture.results / "logs" / f"{run_id}.network-violation.marker"
        write_text(marker, "socket syscall denied\n")
        record["network_violation"] = {
            "detected": True,
            "integrity_ok": True,
            "event_count": 1,
            "saved_marker_log": str(marker.resolve()),
            "marker_sha256": report.file_sha256(marker),
        }
        self.fixture._replace_record(record)
        value = self.render("no-submission-network")
        row = next(item for item in value["runs"] if item["run_id"] == run_id)
        self.assertEqual(row["failure_code"], "NO_SUBMISSION")

    def test_validation_task_binding_tamper_is_rejected(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        validation_path = Path(str(record["validation_log"]))
        validation = report.read_json(validation_path)
        validation.pop("record_sha256")
        validation["authentication"]["task_id"] = "P01-T3"
        validation["record_sha256"] = report.document_sha256(validation)
        write_json(validation_path, validation)
        record["validation_log_sha256"] = report.file_sha256(validation_path)
        record["validation_record_sha256"] = validation["record_sha256"]
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "not bound to its task"):
            self.render("validation-binding-tamper")

    def test_passing_validation_requires_all_five_controlled_checkpoints(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])

        def tamper(validation: dict[str, object]) -> None:
            validation["controlled_after_expected_compile"]["verified"] = 1

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "controlled-file findings"):
            self.render("validation-controlled-checkpoint-tamper")

    def test_hidden_validation_commands_are_derived_from_the_frozen_contract(self) -> None:
        record = report.read_json(
            sorted((self.fixture.results / "records").glob("*.json"))[0]
        )

        def tamper(validation: dict[str, object]) -> None:
            for field in ("compile", "expected_statement_compile", "dependency_audit"):
                validation[field]["command"] = ["/usr/bin/true"]
                validation[field]["display"] = "/usr/bin/true"

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(
            report.ReportError, "generated checked source|command is not contract-derived"
        ):
            self.render("validation-command-contract-tamper")

    def test_passing_validation_requires_complete_candidate_inventory_and_static_scan(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])
        finding = {"path": "Helper.lean", "kind": "forbidden import"}

        def tamper(validation: dict[str, object]) -> None:
            validation["candidate_inventory"]["findings"] = [finding]

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "omits candidate-inventory findings"):
            self.render("validation-inventory-tamper")

    def test_candidate_olean_without_source_requires_derived_finding(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])

        def tamper(validation: dict[str, object]) -> None:
            validation["candidate_inventory"]["candidate_oleans"] = ["Backdoor.olean"]

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "unmatched-olean finding"):
            self.render("validation-unmatched-olean-tamper")

    def test_passing_validation_requires_both_successful_compiles(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])

        def tamper(validation: dict[str, object]) -> None:
            validation["expected_statement_compile"].update(
                {"exit_code": None, "timed_out": True}
            )

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "accepted validation failed"):
            self.render("validation-expected-compile-tamper")

    def test_passing_validation_requires_unchanged_trusted_side_channel(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])

        def tamper(validation: dict[str, object]) -> None:
            validation["local_modules_side_channel"]["unchanged_after_audit"] = False

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "accepted validation failed"):
            self.render("validation-side-channel-tamper")

    def test_passing_validation_reparses_dependency_audit_output(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])

        def tamper(validation: dict[str, object]) -> None:
            validation["dependency_audit"]["parsed"]["format_version"] = 1

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "disagrees with its output"):
            self.render("validation-dependency-parse-tamper")

    def test_passing_validation_requires_semantic_type_equality(self) -> None:
        record = report.read_json(sorted((self.fixture.results / "records").glob("*.json"))[0])

        def tamper(validation: dict[str, object]) -> None:
            audit = validation["dependency_audit"]
            audit["output"] = audit["output"].replace("\ttrue\n", "\tfalse\n", 1)
            parsed = validator.parse_dependency_audit(audit["output"])
            parsed["expected_helper_modules"] = []
            parsed["missing_helper_modules"] = []
            audit["parsed"] = parsed
            validation["semantic_statement_check"] = parsed["type_check"]

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "accepted validation failed at semantic"):
            self.render("validation-semantic-tamper")

    def test_rejected_validation_failure_is_derived_from_first_failed_stage(self) -> None:
        run_id = self.fixture.make_rejected_l_validation_failure()
        value = self.render("derived-rejected-validation")
        row = next(item for item in value["runs"] if item["run_id"] == run_id)
        semantics = row["validation_authentication"]["hidden_validation_semantics"]
        self.assertEqual(semantics["derived_failure_code"], "PROOF_ERROR")
        self.assertEqual(semantics["first_failed_stage"], "candidate_compile_rejection")

    def test_rejected_validation_cannot_misclassify_first_failed_stage(self) -> None:
        self.fixture.make_rejected_l_validation_failure(validation_code="SYNTAX_OR_ELAB")
        with self.assertRaisesRegex(report.ReportError, "first failed stage"):
            self.render("misclassified-rejected-validation")

    def test_rejected_validation_rejects_impossible_command_tristate(self) -> None:
        run_id = self.fixture.make_rejected_l_validation_failure()
        record = report.read_json(self.fixture.results / "records" / f"{run_id}.json")

        def tamper(validation: dict[str, object]) -> None:
            validation["compile"].update(
                {"exit_code": None, "timed_out": False, "system_error": None}
            )

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "impossible command outcome tri-state"):
            self.render("rejected-impossible-command-tristate")

    def test_rejected_validation_requires_unpopulated_later_stages(self) -> None:
        run_id = self.fixture.make_rejected_l_validation_failure()
        record = report.read_json(self.fixture.results / "records" / f"{run_id}.json")

        def tamper(validation: dict[str, object]) -> None:
            validation["expected_statement_compile"] = {"forged": True}
            validation["controlled_after_expected_compile"] = {"forged": True}
            validation["local_modules_side_channel"] = {"forged": True}

        self.fixture.mutate_validation(record, tamper)
        with self.assertRaisesRegex(report.ReportError, "impossible post-candidate_compile"):
            self.render("rejected-populated-later-stages")

    def test_n_preflight_requires_authenticated_complete_staging(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        record["n_preflight"]["controlled_task_staging"]["manifest_sha256"] = "0" * 64
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "complete controlled task staging"):
            self.render("n-staging-tamper")

    def test_n_preflight_requires_full_leak_free_filesystem_scan(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        record["n_preflight"]["filesystem_scan"]["symlink_count"] = 1
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "filesystem scan is incomplete"):
            self.render("n-filesystem-tamper")

    def test_n_preflight_requires_the_exact_frozen_marker_set(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        record["n_preflight"]["filesystem_scan"]["markers"] = ["NumStability"]
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "filesystem scan is incomplete"):
            self.render("n-marker-set-tamper")

    def test_n_preflight_requires_the_frozen_lean_isolated_probe_shape(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        record["n_preflight"]["import_probe"]["command"] = ["true"]
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "reliable failed NumStability import"):
            self.render("n-probe-command-tamper")

    def test_n_preflight_probe_is_bound_to_the_agent_execution_roots(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        probe_command = record["n_preflight"]["import_probe"]["command"]
        probe_command[0] = "/tmp/python-forged"
        probe_command[8] = "/tmp/forged-toolchain"
        probe_command[10] = "/tmp/forged-packages"
        probe_command[12] = "/tmp/forged-shared"
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "reliable failed NumStability import"):
            self.render("n-probe-provenance-tamper")

    def test_n_probe_and_agent_command_cannot_two_sided_forge_execution_roots(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        forged = {
            0: "/tmp/python-forged",
            8: "/tmp/forged-toolchain",
            10: "/tmp/forged-packages",
            12: "/tmp/forged-shared",
        }
        probe_command = record["n_preflight"]["import_probe"]["command"]
        for index, value in forged.items():
            probe_command[index] = value
        agent_command = record["agent_command"]
        agent_command[0] = forged[0]
        for option, value in (
            ("--toolchain-root", forged[8]),
            ("--packages-root", forged[10]),
            ("--shared-olean-root", forged[12]),
        ):
            agent_command[agent_command.index(option) + 1] = value
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "Python executable is not freeze-bound"):
            self.render("n-probe-two-sided-root-forgery")

    def test_n_preflight_requires_recognizable_missing_module_probe(self) -> None:
        record = next(
            report.read_json(path)
            for path in sorted((self.fixture.results / "records").glob("*.json"))
            if report.read_json(path).get("condition") == "N"
        )
        record["n_preflight"]["import_probe"]["output"] = "compiler exited with error"
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "reliable failed NumStability import"):
            self.render("n-import-probe-tamper")

    def test_unsealed_barrier_artifact_is_rejected(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        challenge = Path(
            str(record["ultra_submission_boundary"]["artifacts"]["challenge"]["path"])
        )
        challenge.chmod(0o644)
        with self.assertRaisesRegex(report.ReportError, "not sealed mode 0444"):
            self.render("unsealed-barrier")

    def test_boundary_usage_requires_exact_appserver_response_projection(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        usage_path = Path(
            str(report._option(record["agent_command"], "--usage-output", "fixture"))
        )
        paths = codex_isolated.submission_barrier_paths(usage_path, 1)
        original_request = report.read_json(paths["request"])
        original_ack = report.read_json(paths["ack"])

        def assert_rejected(mutate: object) -> None:
            request = json.loads(json.dumps(original_request))
            request.pop("request_sha256")
            assert callable(mutate)
            mutate(request["boundary_usage"])
            request = codex_isolated.authenticated_record(request, "request_sha256")
            ack = json.loads(json.dumps(original_ack))
            ack.pop("ack_sha256")
            ack["request_sha256"] = request["request_sha256"]
            ack = codex_isolated.authenticated_record(ack, "ack_sha256")
            for name, value in (("request", request), ("ack", ack)):
                paths[name].chmod(0o644)
                write_json(paths[name], value)
                paths[name].chmod(0o444)
            usage = json.loads(json.dumps(record["token_usage"]))
            usage["submission_boundary"]["request_sha256"] = request[
                "request_sha256"
            ]
            usage["submission_boundary"]["ack_sha256"] = ack["ack_sha256"]
            with self.assertRaisesRegex(
                report.ReportError,
                "request usage snapshot differs from the final proof boundary",
            ):
                report._authenticated_barrier_artifacts(
                    self.fixture.results,
                    usage_path,
                    record,
                    usage,
                    Path(str(record["accepted_submission_log"])),
                )

        cases = {
            "missing": lambda value: value.pop("appserver_response_count"),
            "extra": lambda value: value.__setitem__("unexpected", True),
            "tampered": lambda value: value.__setitem__(
                "appserver_response_ids", ["forged-response"]
            ),
        }
        for name, mutate in cases.items():
            with self.subTest(name=name):
                assert_rejected(mutate)

    def test_hardware_self_hash_tamper_is_rejected(self) -> None:
        path = next((self.fixture.results / "allocation_hardware").glob("*.json"))
        hardware = report.read_json(path)
        hardware["scheduler_sharing"]["partition_oversubscribe"] = "NO"
        write_json(path, hardware)
        with self.assertRaisesRegex(report.ReportError, "stale canonical self-hash"):
            self.render("hardware-tamper")

    def test_per_run_hardware_link_is_required(self) -> None:
        path = sorted((self.fixture.results / "records").glob("*.json"))[0]
        record = report.read_json(path)
        record["allocation_hardware"]["job_id"] = "999"
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "not linked"):
            self.render("hardware-link-tamper")

    def test_l_failure_still_requires_the_frozen_library_mounts(self) -> None:
        run_id = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        record = report.read_json(self.fixture.results / "records" / f"{run_id}.json")
        command = record["agent_command"]
        for option, forged in (
            ("--library-source", "/tmp/forged-library-source"),
            ("--library-root-file", "/tmp/forged-library-root.lean"),
            ("--library-olean", "/tmp/forged-library-olean"),
        ):
            command[command.index(option) + 1] = forged
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(
            report.ReportError, "does not expose the frozen NumStability source paths"
        ):
            self.render("l-failure-forged-library-mounts")

    def test_failure_code_priority_is_enforced(self) -> None:
        run_id = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        path = self.fixture.results / "records" / f"{run_id}.json"
        record = report.read_json(path)
        record["failure_code"] = "PROOF_ERROR"
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "violates priority"):
            self.render("failure-priority")

    def test_failure_note_must_be_nonempty_and_bounded(self) -> None:
        run_id = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        path = self.fixture.results / "records" / f"{run_id}.json"
        record = report.read_json(path)
        record["failure_note"] = ""
        self.fixture._replace_record(record)
        with self.assertRaisesRegex(report.ReportError, "failure is not nonempty"):
            self.render("empty-failure-note")

    def test_natural_failure_requires_complete_projection(self) -> None:
        run_id = self.fixture.make_l_failure(0, "NO_SUBMISSION")
        record = report.read_json(self.fixture.results / "records" / f"{run_id}.json")
        usage_path = Path(
            str(report._option(record["agent_command"], "--usage-output", "fixture"))
        )
        usage = report.read_json(usage_path)
        usage["threads"][0]["cumulative_projection_match"] = False
        write_json(usage_path, usage)
        with self.assertRaisesRegex(report.ReportError, "usage ledger|accounting"):
            self.render("inexact-failure")

    def test_unmatched_attempt_is_rejected(self) -> None:
        write_json(self.fixture.results / "attempts" / "orphan.attempt-1.json", {})
        write_text(self.fixture.results / "attempts" / "orphan.attempt-1.jsonl", "{}\n")
        with self.assertRaisesRegex(report.ReportError, "unmatched"):
            self.render("orphan-attempt")

    def test_one_pre_useful_startup_retry_is_allowed(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        value = self.render("startup-retry")
        self.assertIn(run_id, {row["run_id"] for row in value["runs"]})
        evidence = value["provenance"]["matrix_incident_authentication"]
        self.assertEqual(evidence["resolved_pre_prompt_retry_count"], 1)
        self.assertEqual(evidence["incidents"][0]["planned_run_id"], run_id)
        self.assertRegex(evidence["incidents"][0]["matrix_incident_sha256"], r"^[0-9a-f]{64}$")

    def test_useful_work_startup_retry_is_rejected(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        source_path = self.fixture.results / "attempts" / f"{run_id}.attempt-1.json"
        incident_path = self.fixture.results / "incidents" / f"{run_id}.attempt-1.json"
        source = report.read_json(source_path)
        source["useful_work_started"] = True
        write_json(source_path, source)
        incident = report.read_json(incident_path)
        incident["useful_work_started"] = True
        incident["incident_provenance"]["source_attempt"]["sha256"] = report.file_sha256(
            source_path
        )
        incident.pop("matrix_incident_sha256")
        incident["matrix_incident_sha256"] = report.document_sha256(incident)
        write_json(incident_path, incident)
        with self.assertRaisesRegex(report.ReportError, "pre-prompt no-work"):
            self.render("bad-startup-retry")

    def test_startup_incident_requires_canonical_self_hash(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        path = self.fixture.results / "incidents" / f"{run_id}.attempt-1.json"
        incident = report.read_json(path)
        incident["failure_note"] = "tampered incident reason"
        write_json(path, incident)
        with self.assertRaisesRegex(report.ReportError, "stale canonical self-hash"):
            self.render("startup-incident-self-hash-tamper")

    def test_startup_incident_authenticates_source_attempt_and_transcript(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        transcript = self.fixture.results / "attempts" / f"{run_id}.attempt-1.jsonl"
        write_text(transcript, transcript.read_text(encoding="utf-8") + "{}\n")
        with self.assertRaisesRegex(report.ReportError, "source attempt/transcript"):
            self.render("startup-incident-transcript-tamper")

    def test_startup_incident_rejects_two_sided_log_tamper(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        source = report.read_json(
            self.fixture.results / "attempts" / f"{run_id}.attempt-1.json"
        )
        incident = report.read_json(
            self.fixture.results / "incidents" / f"{run_id}.attempt-1.json"
        )
        tampered = b"same forged bytes on both sides\n"
        (self.fixture.results / source["agent_log"]).write_bytes(tampered)
        (self.fixture.results / incident["agent_log"]).write_bytes(tampered)
        with self.assertRaisesRegex(report.ReportError, "source agent_log digest"):
            self.render("startup-incident-two-sided-log-tamper")

    def test_terminal_startup_incident_cannot_coexist_with_checkpoint(self) -> None:
        run_id = self.fixture.add_qualifying_startup_retry()
        path = self.fixture.results / "incidents" / f"{run_id}.attempt-1.json"
        incident = report.read_json(path)
        incident["matrix_incident"].update(
            {"status": "terminal_pre_prompt_system_error", "retry_allowed": False}
        )
        incident.pop("matrix_incident_sha256")
        incident["matrix_incident_sha256"] = report.document_sha256(incident)
        write_json(path, incident)
        with self.assertRaisesRegex(report.ReportError, "terminal startup incident"):
            self.render("terminal-startup-incident")

    def test_active_run_marker_blocks_checkpoint_report(self) -> None:
        write_json(self.fixture.results / "active_run.json", {"kind": "unfinished"})
        with self.assertRaisesRegex(report.ReportError, "active-run marker"):
            self.render("active-run-marker")

    @unittest.skipUnless(
        shutil.which("pdflatex") and shutil.which("gs"),
        "pdflatex/Ghostscript unavailable",
    )
    def test_two_pass_pdf_compile_and_raster_have_no_overfull_boxes(self) -> None:
        output = Path(self.temporary.name) / "compiled-success"
        report.build_report(
            self.fixture.benchmark,
            self.fixture.results,
            output,
            compile_pdf=True,
        )
        log = (output / "pdflatex.log.txt").read_text(encoding="utf-8")
        self.assertNotIn("Overfull", log)
        pdf = output / "HighamBench_P01_Checkpoint_Report.pdf"
        self.assertTrue(pdf.is_file())
        subprocess.run(
            [
                str(shutil.which("gs")),
                "-q",
                "-dSAFER",
                "-dBATCH",
                "-dNOPAUSE",
                "-sDEVICE=png16m",
                "-r96",
                f"-sOutputFile={output / 'raster-%02d.png'}",
                str(pdf),
            ],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        raster_pages = sorted(output.glob("raster-*.png"))
        self.assertGreaterEqual(len(raster_pages), 1)
        self.assertTrue(all(path.stat().st_size > 1_000 for path in raster_pages))
        self.assertTrue(all(path.read_bytes().startswith(b"\x89PNG\r\n\x1a\n") for path in raster_pages))

    @unittest.skipUnless(shutil.which("pdflatex"), "pdflatex unavailable")
    def test_rule_violation_failure_pdf_compiles_without_overlap(self) -> None:
        self.fixture.make_network_rule_failure()
        output = Path(self.temporary.name) / "compiled-failure"
        report.build_report(
            self.fixture.benchmark,
            self.fixture.results,
            output,
            compile_pdf=True,
        )
        log = (output / "pdflatex.log.txt").read_text(encoding="utf-8")
        self.assertNotIn("Overfull", log)
        tex = (output / "HighamBench_P01_Checkpoint_Report.tex").read_text(
            encoding="utf-8"
        )
        self.assertIn(r"RULE\_\allowbreak{}VIOLATION", tex)


if __name__ == "__main__":
    unittest.main()
