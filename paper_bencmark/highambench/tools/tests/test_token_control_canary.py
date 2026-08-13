from __future__ import annotations

import copy
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import time
import unittest

from paper_bencmark.highambench.tools.common import (
    BenchmarkToolError,
    sha256_file,
    write_json,
)
from paper_bencmark.highambench.tools.hashes import create_manifest
from paper_bencmark.highambench.tools import codex_isolated, provider_token_gate, runner
from paper_bencmark.highambench.tools import run_token_control_canary as canary
from paper_bencmark.highambench.tools.tests.test_runner import (
    _seal_synthetic_gate,
    synthetic_provider_gate,
)


ROOT = "root-thread"
TURN = "root-turn"
COMPACTION_TURN = "root-compaction-turn"
FIRST_RESPONSE = "resp-fixture-0"
RESPONSE = "resp-fixture-1"
HANDSHAKE_NONCE = "c" * 64
CANARY_LIMIT = canary.DEFAULT_CANARY_TOKEN_LIMIT
FIRST_RESPONSE_TOKENS = 160_000
CROSSING_RESPONSE_TOKENS = 100_000
CROSSING_TOTAL_TOKENS = FIRST_RESPONSE_TOKENS + CROSSING_RESPONSE_TOKENS


def set_authenticated_upstream_sse(
    call: dict,
    *,
    response_id: str,
    raw_usage: dict,
    request_kind: str,
) -> bytes:
    events: list[dict] = []
    output: list[dict] = []
    if request_kind == "compaction":
        item = {
            "type": "compaction",
            "encrypted_content": "opaque-compaction-fixture",
        }
        output.append(item)
        events.append(
            {
                "type": "response.output_item.done",
                "output_index": 0,
                "item": item,
            }
        )
    events.append(
        {
            "type": "response.completed",
            "response": {"id": response_id, "usage": raw_usage, "output": output},
        }
    )
    body = "".join(
        "event: "
        + event["type"]
        + "\ndata: "
        + json.dumps(event, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n\n"
        for event in events
    ).encode("utf-8")
    digest = hashlib.sha256(body).hexdigest()
    call.update(
        {
            "upstream_status": 200,
            "upstream_body_sha256": digest,
            "upstream_body_bytes": len(body),
            "upstream_sse_authentication": {
                "schema_version": 1,
                "protocol": runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT[
                    "protocol"
                ],
                "parser": runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT["parser"],
                "complete": True,
                "content_type_basis": "declared_text_event_stream",
                "content_encoding_basis": "declared_identity",
                "json_event_count": len(events),
                "completed_event_index": len(events) - 1,
                "done_count": 0,
                "body_sha256": digest,
                "body_bytes": len(body),
                "response_id": response_id,
                "downstream_content_type_synthesized": False,
            },
            "response_output_manifest": provider_token_gate._response_output_manifest(
                response_id, output
            ),
        }
    )
    return body


def usage_breakdown(total: int) -> dict[str, int]:
    output = 1_500 if total == FIRST_RESPONSE_TOKENS else 1_000
    cached = 50_000 if total == FIRST_RESPONSE_TOKENS else 40_000
    cache_write = 200
    reasoning = 300
    return {
        "inputTokens": total - output,
        "cachedInputTokens": cached,
        "cacheWriteInputTokens": cache_write,
        "outputTokens": output,
        "reasoningOutputTokens": reasoning,
        "totalTokens": total,
    }


def exact_compaction_log_events() -> list[dict]:
    first = usage_breakdown(FIRST_RESPONSE_TOKENS)
    crossing = usage_breakdown(CROSSING_RESPONSE_TOKENS)
    return [
        {
            "method": "turn/started",
            "params": {
                "threadId": ROOT,
                "turn": {"id": TURN, "status": "inProgress"},
            },
        },
        {
            "method": "item/completed",
            "params": {
                "threadId": ROOT,
                "turnId": TURN,
                "item": {
                    "type": "agentMessage",
                    "text": canary.DIRECT_FINAL_ANSWER,
                },
            },
        },
        {
            "method": canary.TOKEN_NOTIFICATION,
            "params": {
                "threadId": ROOT,
                "turnId": TURN,
                "responseId": FIRST_RESPONSE,
                "usage": first,
            },
        },
        {
            "method": "turn/completed",
            "params": {
                "threadId": ROOT,
                "turn": {"id": TURN, "status": "completed"},
            },
        },
        {
            "method": "turn/started",
            "params": {
                "threadId": ROOT,
                "turn": {"id": COMPACTION_TURN, "status": "inProgress"},
            },
        },
        {
            "method": "item/started",
            "params": {
                "threadId": ROOT,
                "turnId": COMPACTION_TURN,
                "item": {"type": "contextCompaction", "id": "compact-item"},
            },
        },
        {"id": codex_isolated.THREAD_COMPACT_REQUEST_ID, "result": {}},
        {
            "method": canary.TOKEN_NOTIFICATION,
            "params": {
                "threadId": ROOT,
                "turnId": COMPACTION_TURN,
                "responseId": RESPONSE,
                "usage": crossing,
            },
        },
    ]


def write_log(path: Path, events: list[dict]) -> None:
    path.write_text(
        "$ synthetic-adapter\n\n"
        + "".join(json.dumps(event, sort_keys=True) + "\n" for event in events),
        encoding="utf-8",
    )


def usage_from_events(
    path: Path, events: list[dict], limit: int = CANARY_LIMIT
) -> dict:
    ledger = codex_isolated.AttemptUsageLedger(
        path,
        limit,
        ROOT,
        fork_policy=codex_isolated.ultra_fork_policy_static_record(),
    )
    compaction_start = next(
        index
        for index, event in enumerate(events)
        if event.get("method") == "turn/started"
        and event.get("params", {}).get("turn", {}).get("id") == COMPACTION_TURN
    )
    for event in events[:compaction_start]:
        ledger.observe(event)
    # The fixture attaches the independently sealed gate below; authorize the
    # same one-shot lifecycle state without installing a fake transport here.
    ledger.compaction_canary_authorized = True
    for event in events[compaction_start:]:
        ledger.observe(event)
    return ledger.snapshot(drain_complete=False)


def valid_record(
    usage: dict, runner_freeze: dict, *, limit: int = CANARY_LIMIT
) -> dict:
    # The provider-call crossbindings are attached after prompt-release
    # authentication; retain the raw ledger provisionally and normalize it only
    # after that exact gate has been installed.
    normalized = copy.deepcopy(usage)
    total = usage["total_tokens"]
    first = usage["first_crossing"]["tokens"]
    return {
        "schema_version": "highambench-0.1",
        "kind": "highambench-run",
        "run_id": canary.CANARY_ID,
        "task_id": canary.CANARY_ID,
        "paper_id": "SYNTHETIC",
        "condition": "N",
        "tier": "T1",
        "repetition_id": "canary",
        "environment_id": "fixture-environment",
        "pass": False,
        "useful_work_started": True,
        "scored": True,
        "agent_exit_code": 0,
        "failure_code": "TOKEN_LIMIT",
        "failure_note": "exact synthetic threshold crossing",
        "actual_stop_seconds": 3.25,
        "first_valid_seconds": None,
        "token_usage": normalized,
        "token_measurement": {
            "source": canary.TOKEN_MEASUREMENT_SOURCE,
            "provider_cumulative_total_exact": True,
            "cached_input_counted_once": True,
            "measurement_error": None,
            "trusted_usage_path_outside_workspace": True,
            "post_submission_usage_established": False,
            "usage_scope": canary.TOKEN_USAGE_SCOPE,
            "thread_count": 1,
            "response_count": 2,
            "tree_drain_complete": False,
            "limit_enforcement": {
                "mode": canary.TOKEN_ENFORCEMENT_MODE,
                "notification": canary.TOKEN_NOTIFICATION,
                "configured_limit_tokens": limit,
                "triggered": True,
                "observed_tokens": first,
                "overshoot_tokens": first - limit,
                "first_crossing_tokens": first,
                "first_crossing_overshoot_tokens": first - limit,
                "final_endpoint_tokens": total,
                "final_overshoot_tokens": total - limit,
                "checked_before_submission_validation": True,
                "one_response_overshoot_possible": True,
                "concurrent_inflight_overshoot_possible": False,
            },
        },
        "library_use": False,
        "library_declarations": [],
        "submission_sha256": None,
        "final_submission_sha256": None,
        "network_violation": {"detected": False, "integrity_ok": True},
        "protocol": {
            "complete": True,
            "claims": {"token_limit_enforced_by_agent": True},
            "verified": {
                "authenticated_prompt_release": True,
                "authenticated_provider_token_gate": True,
                "provider_gate_appserver_deliveries_reconciled": True,
                "provider_gate_terminal_endpoint": True,
            },
        },
        "ultra_submission_boundary": {"verified": False},
        "frozen_run_verification": {
            "freeze_check": runner_freeze,
            "freeze_check_sha256": canary._canonical_sha256(runner_freeze),
        },
        "prompt_provenance": canary.synthetic_prompt_provenance_record(),
        "agent_command": [
            "adapter",
            "--condition",
            "N",
            "--controlled-relative",
            "task",
            "--prompt-file",
            "/tmp/workspace/task/prompt.md",
            "--context-file",
            "/tmp/workspace/task/context.md",
            "--target-file",
            "/tmp/workspace/task/SyntheticTarget.lean",
            "--usage-output",
            "/tmp/placeholder.usage.json",
            "--provider-gate-live-output",
            "/tmp/placeholder.provider-token-gate.live.json",
            "--provider-gate-output",
            "/tmp/placeholder.provider-token-gate.json",
            "--model-catalog-sha256",
            "2" * 64,
            "--model-entry-sha256",
            "3" * 64,
            "--provider-response-bound",
            "272000",
            "--provider-token-gate-compaction-canary",
            "--token-limit",
            str(limit),
            "--advisory-rollout-budget-limit",
            "5000000",
            "--model",
            "gpt-5.6-sol",
            "--reasoning-effort",
            "ultra",
        ],
    }


def attach_prompt_release(record: dict, usage: dict, usage_path: Path) -> None:
    paths = {
        key: value.resolve()
        for key, value in canary._prompt_handshake_paths(usage_path.resolve()).items()
    }
    prompt = canary.synthetic_effective_prompt()
    prompt_bytes = prompt.encode("utf-8")
    release_mono = time.monotonic_ns() - 1_000_000_000
    ready_mono = release_mono - 2_000_000
    go_mono = release_mono - 1_000_000
    flush_mono = release_mono + 1_000
    crossing_unix = usage["first_crossing"]["observed_at_unix_ns"]
    release_unix = crossing_unix - 1_000_000
    ready_unix = release_unix - 2_000_000
    go_unix = release_unix - 1_000_000
    flush_unix = release_unix + 1_000
    common = {
        "schema_version": canary.PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": canary.PROMPT_RELEASE_PROTOCOL_VERSION,
        "handshake_nonce": HANDSHAKE_NONCE,
        "run_id": canary.CANARY_RUN_ID,
        "condition": "N",
        "model": "gpt-5.6-sol",
        "reasoning_effort": "ultra",
        "root_thread_id": ROOT,
        "turn_start_request_id": canary.TURN_START_REQUEST_ID,
        "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "effective_prompt_bytes": len(prompt_bytes),
        "adapter_name": canary.PROMPT_RELEASE_ADAPTER_NAME,
        "adapter_version": canary.PROMPT_RELEASE_ADAPTER_VERSION,
        "app_server_client_name": canary.APP_SERVER_CLIENT_NAME,
        "app_server_client_version": canary.APP_SERVER_CLIENT_VERSION,
        "elapsed_clock": "CLOCK_MONOTONIC",
    }
    ready = codex_isolated.write_authenticated_record_atomic(
        paths["ready"],
        {
            **common,
            "kind": "highambench_prompt_ready",
            "turn_start_write_state": "not_started",
            "ready_at_monotonic_ns": ready_mono,
            "ready_at_unix_ns": ready_unix,
        },
        "ready_sha256",
    )
    go = codex_isolated.write_authenticated_record_atomic(
        paths["go"],
        {
            **common,
            "kind": "highambench_prompt_go",
            "ready_sha256": ready["ready_sha256"],
            "turn_start_write_authorized": True,
            "authorized_at_monotonic_ns": go_mono,
            "authorized_at_unix_ns": go_unix,
        },
        "go_sha256",
    )
    request = codex_isolated.prompt_turn_start_request(
        prompt=prompt,
        root_thread_id=ROOT,
        model="gpt-5.6-sol",
        reasoning_effort="ultra",
    )
    wire = codex_isolated.canonical_protocol_wire(request)
    released = codex_isolated.write_authenticated_record_atomic(
        paths["release"],
        {
            **common,
            "kind": "highambench_prompt_released",
            "ready_sha256": ready["ready_sha256"],
            "go_sha256": go["go_sha256"],
            "turn_start_write_state": "flushed",
            "timestamp_capture_point": "immediately_before_turn_start_write",
            "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
            "turn_start_request_bytes": len(wire),
            "released_at_monotonic_ns": release_mono,
            "released_at_unix_ns": release_unix,
            "turn_start_flushed_at_monotonic_ns": flush_mono,
            "turn_start_flushed_at_unix_ns": flush_unix,
        },
        "release_sha256",
    )

    def descriptor(path: Path, value: dict, field: str) -> dict:
        return {
            "path": str(path),
            "file_sha256": sha256_file(path),
            "record_sha256": value[field],
            "record": value,
        }

    record["prompt_release"] = {
        "schema_version": canary.PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": canary.PROMPT_RELEASE_PROTOCOL_VERSION,
        "required": True,
        "status": "released_authenticated",
        "authenticated": True,
        "timing_exact": True,
        "useful_work_basis": "authenticated_release",
        "startup_timeout_seconds": canary.PROMPT_STARTUP_TIMEOUT_SECONDS,
        "startup_timeout_triggered": False,
        "go_minimum_release_window_seconds": (
            canary.PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS
        ),
        "handshake_nonce": HANDSHAKE_NONCE,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "artifact_paths": {key: str(value) for key, value in paths.items()},
        "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "effective_prompt_bytes": len(prompt_bytes),
        "ready": descriptor(paths["ready"], ready, "ready_sha256"),
        "go": descriptor(paths["go"], go, "go_sha256"),
        "released": descriptor(paths["release"], released, "release_sha256"),
        "stale_artifacts_removed": [],
        "error": None,
    }


def attach_provider_gate(
    record: dict,
    usage: dict,
    usage_path: Path,
    *,
    token_limit: int = CANARY_LIMIT,
) -> None:
    """Attach an exact two-call turn/compaction gate and runner summary."""

    gate_paths = runner.provider_gate_paths(usage_path.resolve())
    gate_record, _gate_usage, expected = synthetic_provider_gate(
        gate_paths["final"],
        close_reason="token_limit",
        token_limit=token_limit,
        request_kind="compaction",
    )

    def normalized(raw: dict[str, int]) -> dict[str, int]:
        return {
            "input_tokens": raw["inputTokens"],
            "cached_input_tokens": raw["cachedInputTokens"],
            "cache_write_input_tokens": raw["cacheWriteInputTokens"],
            "output_tokens": raw["outputTokens"],
            "reasoning_output_tokens": raw["reasoningOutputTokens"],
            "total_tokens": raw["totalTokens"],
        }

    def provider_raw(raw: dict[str, int]) -> dict[str, object]:
        return {
            "input_tokens": raw["inputTokens"],
            "input_tokens_details": {
                "cached_tokens": raw["cachedInputTokens"],
                "cache_write_tokens": raw["cacheWriteInputTokens"],
            },
            "output_tokens": raw["outputTokens"],
            "output_tokens_details": {
                "reasoning_tokens": raw["reasoningOutputTokens"]
            },
            "total_tokens": raw["totalTokens"],
        }

    first_raw = usage_breakdown(FIRST_RESPONSE_TOKENS)
    crossing_raw = usage_breakdown(CROSSING_RESPONSE_TOKENS)
    first_normalized = normalized(first_raw)
    crossing_normalized = normalized(crossing_raw)
    crossing_call = copy.deepcopy(gate_record["calls"][0])
    first_call = copy.deepcopy(crossing_call)
    first_call.update(
        {
            "sequence": 3,
            "call_id": "provider-call-00000003",
            "request_body_sha256": hashlib.sha256(b"initial request").hexdigest(),
            "request_bytes": len(b"initial request"),
            "request_metadata": {
                **first_call["request_metadata"],
                "turn_id": TURN,
                "request_kind": "turn",
            },
            "completed_before": 0,
            "open_before": 0,
            "reserved_before": 0,
            "reservation_after": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
            "admitted_unix_ns": 10_250,
            "admitted_monotonic_ns": 1_250,
            "upstream_start_unix_ns": 10_300,
            "upstream_start_monotonic_ns": 1_300,
            "response_id": FIRST_RESPONSE,
            "usage": provider_raw(first_raw),
            "normalized_usage": first_normalized,
            "previous_total": 0,
            "committed_total": FIRST_RESPONSE_TOKENS,
            "commit_unix_ns": 10_350,
            "commit_monotonic_ns": 1_350,
            "crossed_cap": False,
            "release_kind": "byte_identity",
            "released_body_sha256": first_call["upstream_body_sha256"],
            "released_body_bytes": first_call["upstream_body_bytes"],
            "released_sanitized_event": None,
            "released_sanitized_events": None,
            "released_sanitized_body_utf8": None,
            "appserver_crossbind": {
                "thread_id": ROOT,
                "turn_id": TURN,
                "event_sequence": 1,
                "normalized_usage": first_normalized,
                "bind_unix_ns": 10_360,
                "bind_monotonic_ns": 1_360,
            },
        }
    )
    first_call["appserver_delivery"] = {
        "kind": "direct_raw_response",
        "successor_call_id": None,
        "successor_response_id": None,
        "bind_unix_ns": first_call["appserver_crossbind"]["bind_unix_ns"],
        "bind_monotonic_ns": first_call["appserver_crossbind"][
            "bind_monotonic_ns"
        ],
    }
    first_body = set_authenticated_upstream_sse(
        first_call,
        response_id=FIRST_RESPONSE,
        raw_usage=provider_raw(first_raw),
        request_kind="turn",
    )
    first_call["released_body_sha256"] = hashlib.sha256(first_body).hexdigest()
    first_call["released_body_bytes"] = len(first_body)
    completed_event = {
        "type": "response.completed",
        "response": {
            "id": RESPONSE,
            "usage": provider_raw(crossing_raw),
            "end_turn": True,
            "output": [],
        },
    }
    compaction_event = {
        "type": "response.output_item.done",
        "item": {
            "type": "compaction",
            "encrypted_content": "opaque-compaction-fixture",
        },
    }
    sanitized_events = [compaction_event, completed_event]
    released_body = b"".join(
        b"event: "
        + event["type"].encode("ascii")
        + b"\ndata: "
        + json.dumps(
            event, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
        + b"\n\n"
        for event in sanitized_events
    )
    crossing_call.update(
        {
            "sequence": 4,
            "call_id": "provider-call-00000004",
            "request_metadata": {
                **crossing_call["request_metadata"],
                "turn_id": COMPACTION_TURN,
                "request_kind": "compaction",
            },
            "completed_before": FIRST_RESPONSE_TOKENS,
            "open_before": 0,
            "reserved_before": FIRST_RESPONSE_TOKENS,
            "reservation_after": (
                FIRST_RESPONSE_TOKENS + runner.PROVIDER_RESPONSE_TOKEN_BOUND
            ),
            "admitted_unix_ns": 10_400,
            "admitted_monotonic_ns": 1_400,
            "upstream_start_unix_ns": 10_450,
            "upstream_start_monotonic_ns": 1_450,
            "response_id": RESPONSE,
            "usage": provider_raw(crossing_raw),
            "normalized_usage": crossing_normalized,
            "previous_total": FIRST_RESPONSE_TOKENS,
            "committed_total": CROSSING_TOTAL_TOKENS,
            "crossed_cap": True,
            "release_kind": runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            "released_body_sha256": hashlib.sha256(released_body).hexdigest(),
            "released_body_bytes": len(released_body),
            "released_sanitized_event": completed_event,
            "released_sanitized_events": sanitized_events,
            "released_sanitized_body_utf8": released_body.decode("utf-8"),
            "appserver_crossbind": {
                "thread_id": ROOT,
                "turn_id": COMPACTION_TURN,
                "event_sequence": 2,
                "normalized_usage": crossing_normalized,
                "bind_unix_ns": 10_550,
                "bind_monotonic_ns": 1_550,
            },
        }
    )
    crossing_call["appserver_delivery"] = {
        "kind": "direct_raw_response",
        "successor_call_id": None,
        "successor_response_id": None,
        "bind_unix_ns": crossing_call["appserver_crossbind"]["bind_unix_ns"],
        "bind_monotonic_ns": crossing_call["appserver_crossbind"][
            "bind_monotonic_ns"
        ],
    }
    set_authenticated_upstream_sse(
        crossing_call,
        response_id=RESPONSE,
        raw_usage=provider_raw(crossing_raw),
        request_kind="compaction",
    )
    crossing = gate_record["state"]["crossing"]
    crossing.update(
        {
            "call_id": crossing_call["call_id"],
            "response_id": RESPONSE,
            "sequence": 5,
            "previous_total": FIRST_RESPONSE_TOKENS,
            "response_tokens": CROSSING_RESPONSE_TOKENS,
            "completed_tokens": CROSSING_TOTAL_TOKENS,
            "overshoot_tokens": CROSSING_TOTAL_TOKENS - token_limit,
            "release_kind": runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
            "request_kind": "compaction",
        }
    )
    gate_record["calls"] = [first_call, crossing_call]
    gate_record["state"]["completed_tokens"] = CROSSING_TOTAL_TOKENS
    gate_record["state"]["sequence"] = 6
    gate_record["transitions"][-1].update(
        {
            "sequence": 6,
            "call_id": crossing_call["call_id"],
        }
    )
    released = record["prompt_release"]["released"]["record"]
    gate_record["bindings"].update(
        {
            "run_id": canary.CANARY_ID,
            "root_thread_id": ROOT,
            "prompt_release_sha256": runner._provider_gate_prompt_release_sha256(
                released
            ),
            "prompt_release_protocol": canary.PROMPT_RELEASE_PROTOCOL_VERSION,
            "prompt_sha256": record["prompt_release"]["effective_prompt_sha256"],
        }
    )
    _seal_synthetic_gate(gate_paths["final"], gate_record)
    response_ledger = usage["response_ledger"]
    if [item["response_id"] for item in response_ledger] != [
        FIRST_RESPONSE,
        RESPONSE,
    ]:
        raise AssertionError("fixture response ledger changed order")
    response_ledger[0]["provider_gate_call"] = first_call
    response_ledger[1]["provider_gate_call"] = crossing_call
    usage_fields = (
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    )
    zero_usage = {field: 0 for field in usage_fields}
    usage.update(
        {
            "measurement_exact": True,
            "provider_usage_reconciliation": {
                "schema_version": (
                    codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
                ),
                "provider_response_count": 2,
                "appserver_response_count": 2,
                "suppressed_collaboration_wait_response_count": 0,
                "provider_usage": {
                    field: usage[field] for field in usage_fields
                },
                "appserver_usage": {
                    field: usage[field] for field in usage_fields
                },
                "suppressed_collaboration_wait_usage": zero_usage,
                "provider_response_ids": [FIRST_RESPONSE, RESPONSE],
                "appserver_response_ids": [FIRST_RESPONSE, RESPONSE],
                "suppressed_collaboration_wait_response_ids": [],
                "suppressed_collaboration_wait_evidence": [],
                "superseded_by_collaboration_message_response_count": 0,
                "superseded_by_collaboration_message_usage": copy.deepcopy(
                    zero_usage
                ),
                "superseded_by_collaboration_message_response_ids": [],
                "superseded_by_collaboration_message_evidence": [],
                "discarded_after_explicit_child_interrupt_response_count": 0,
                "discarded_after_explicit_child_interrupt_usage": copy.deepcopy(
                    zero_usage
                ),
                "discarded_after_explicit_child_interrupt_response_ids": [],
                "discarded_after_explicit_child_interrupt_evidence": [],
            },
            "provider_token_gate": {
                "enabled": True,
                "response_token_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                "artifact_path": str(gate_paths["final"]),
                "record_sha256": gate_record["record_sha256"],
                "final_attached": True,
                "exact_for_usage": True,
                "live": gate_record["state"],
                "terminal": gate_record["state"],
            },
            "adapter_teardown": {
                "process_group_isolated": True,
                "immediate": True,
                "stdin_closed": True,
                "signal": "SIGTERM",
                "returncode": 0,
                "completed": True,
                "started_at_unix_ns": 10_900,
                "started_at_monotonic_ns": 1_900,
                "completed_at_unix_ns": 11_000,
                "completed_at_monotonic_ns": 2_000,
            },
        }
    )
    record["token_usage"] = runner._read_ultra_token_usage(usage)
    command = record["agent_command"]
    replacements = {
        "--usage-output": str(usage_path.resolve()),
        "--provider-gate-live-output": str(gate_paths["live"]),
        "--provider-gate-output": str(gate_paths["final"]),
    }
    for option, value in replacements.items():
        position = command.index(option)
        command[position + 1] = value
    authenticated = runner.authenticate_provider_gate_artifact(
        gate_paths["final"],
        token_limit=token_limit,
        run_id=canary.CANARY_ID,
        model="gpt-5.6-sol",
        reasoning_effort="ultra",
        root_thread_id=ROOT,
        prompt_release_sha256=runner._provider_gate_prompt_release_sha256(released),
        prompt_release_protocol=canary.PROMPT_RELEASE_PROTOCOL_VERSION,
        prompt_sha256=record["prompt_release"]["effective_prompt_sha256"],
        model_catalog_sha256=expected["model_catalog_sha256"],
        model_entry_sha256=expected["model_entry_sha256"],
        expected_transport_provenance=expected["expected_transport_provenance"],
        usage=record["token_usage"],
        expected_source_sha256=expected["expected_source_sha256"],
    )
    record["agent"] = {"model": "gpt-5.6-sol", "reasoning_effort": "ultra"}
    record["limits"] = {"model_tokens": token_limit}
    record["provider_token_gate"] = {
        "required": True,
        "status": "final_artifact_authenticated",
        "protocol": runner.PROVIDER_GATE_PROTOCOL,
        "cleanup_grace_seconds": runner.PROVIDER_GATE_CLEANUP_GRACE_SECONDS,
        "implementation_source_sha256": expected["expected_source_sha256"],
        "model_catalog": {
            "catalog_sha256": expected["model_catalog_sha256"],
            "entry_sha256": expected["model_entry_sha256"],
            "response_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        },
        "transport_provenance": expected["expected_transport_provenance"],
        "live": {
            "scoreable": False,
            "file": runner._provider_gate_file_status(gate_paths["live"]),
            "authenticated_crossing": None,
        },
        "final": {
            "scoreable": True,
            "file": runner._provider_gate_file_status(gate_paths["final"]),
            "authentication": authenticated,
        },
        "error": None,
    }


def complete_crossing_fixture(
    root: Path, runner_freeze: dict | None = None
) -> tuple[list[dict], Path, Path, dict, dict]:
    events = exact_compaction_log_events()
    log = root / "agent.log"
    write_log(log, events)
    usage_path = root / "usage.json"
    usage = usage_from_events(root / "ledger.json", events)
    record = valid_record(usage, {} if runner_freeze is None else runner_freeze)
    attach_prompt_release(record, usage, usage_path)
    attach_provider_gate(record, usage, usage_path)
    write_json(usage_path, usage)
    return events, log, usage_path, usage, record


def make_benchmark_fixture(project: Path) -> tuple[Path, dict]:
    benchmark = project / "paper_bencmark" / "highambench"
    (benchmark / "metadata").mkdir(parents=True)
    (benchmark / "condition_prompts").mkdir()
    task = benchmark / "tasks" / "P01" / "T1"
    task.mkdir(parents=True)
    shared = benchmark / "shared" / "HighamBench"
    shared.mkdir(parents=True)
    (benchmark / "agent_prompt.md").write_text(
        "CONTROLLED_AGENT_PROMPT_SENTINEL_731920\n", encoding="utf-8"
    )
    (benchmark / "condition_prompts" / "L.md").write_text(
        "CONTROLLED_L_SUPPLEMENT_SENTINEL_812743\n", encoding="utf-8"
    )
    (task / "Target.lean").write_text(
        "theorem controlledP01Sentinel : (731927 : Nat) = 731927 := rfl\n",
        encoding="utf-8",
    )
    (task / "context.md").write_text(
        "CONTROLLED_P01_CONTEXT_SENTINEL_318927\n", encoding="utf-8"
    )
    write_json(
        task / "task.json",
        {"task_id": "P01-T1", "sentinel": "CONTROLLED_TASK_JSON_918273"},
    )
    shared_path = shared / "Core.lean"
    shared_path.write_text(
        "def controlledSharedSentinel : Nat := 718293\n", encoding="utf-8"
    )
    manifest = {
        "benchmark_id": "fixture-benchmark",
        "controlled_shared_files": [
            {
                "path": shared_path.relative_to(project).as_posix(),
                "sha256": sha256_file(shared_path),
            }
        ],
        "papers": [],
    }
    write_json(benchmark / "metadata" / "manifest.json", manifest)
    return benchmark, manifest


def make_evidence_fixture(project: Path) -> tuple[dict, dict, Path, dict]:
    benchmark, benchmark_manifest = make_benchmark_fixture(project)
    results = project / "results"
    for name in ("logs", "attempts"):
        (results / name).mkdir(parents=True, exist_ok=True)
    inputs = results / "inputs"
    prompt, context, target = canary._write_synthetic_inputs(inputs)
    controlled = inputs / "controlled.json"
    write_json(
        controlled,
        create_manifest(
            inputs,
            requested=["prompt.md", "context.md", "SyntheticTarget.lean"],
            label="synthetic-token-control-canary",
        ),
    )
    source = canary.audit_benchmark_source_separation(
        project_root=project,
        benchmark_root=benchmark,
        manifest=benchmark_manifest,
        generated_sources={
            "common_prompt": prompt.read_bytes(),
            "context": context.read_bytes(),
            "synthetic_target": target.read_bytes(),
            "effective_prompt": canary.synthetic_effective_prompt().encode("utf-8"),
        },
    )
    source_path = results / "logs" / "benchmark_source_audit.json"
    write_json(source_path, source)
    provenance = canary._self_hashed(
        {
            "schema_version": 1,
            "kind": "highambench-synthetic-token-canary-prompt-provenance",
            "computed_before_prompt_release": True,
            "prompt": canary.prompt_record(),
            "source_separation_audit_sha256": source["audit_sha256"],
            "controlled_manifest_sha256": sha256_file(controlled),
            "condition": "N",
            "condition_supplement": None,
            "library_paths": [],
            "benchmark_task_bytes_used": False,
        }
    )
    provenance_path = results / "logs" / "synthetic_prompt_provenance.json"
    write_json(provenance_path, provenance)
    production_freeze = {
        "schema_version": "highambench-0.1",
        "kind": "highambench-frozen-run-verification",
        "ok": True,
        "benchmark_id": "fixture-benchmark",
        "environment_id": "fixture-environment",
        "agent": {
            "id": "codex-cli",
            "version": "fixture",
            "binary_sha256": "a" * 64,
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "ultra_orchestration": canary.run_matrix.ultra_orchestration_record(),
        },
        "prompt_protocol": {"version": "signposted-library-v1"},
        "execution_components": {"adapter": "b" * 64},
    }
    runner_freeze = canary._runner_freeze_record(production_freeze)
    freeze_path = results / "logs" / "freeze_check.json"
    runner_freeze_path = results / "logs" / "runner_freeze_check.json"
    write_json(freeze_path, production_freeze)
    write_json(runner_freeze_path, runner_freeze)
    events = exact_compaction_log_events()
    agent_log = results / "logs" / "agent.log"
    write_log(agent_log, events)
    usage_path = results / "logs" / "usage.json"
    usage = usage_from_events(results / "logs" / "ledger.tmp.json", events)
    write_json(usage_path, usage)
    record = valid_record(usage, runner_freeze)
    record_path = results / "attempts" / "record.json"
    raw_path = results / "attempts" / "record.jsonl"
    provider = [
        "adapter",
        "--condition",
        "N",
        "--controlled-relative",
        "task",
        "--prompt-file",
        "{workspace}/task/prompt.md",
        "--context-file",
        "{workspace}/task/context.md",
        "--target-file",
        "{workspace}/task/SyntheticTarget.lean",
        "--usage-output",
        "{usage_output}",
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
        "--provider-gate-live-output",
        "{provider_gate_live_output}",
        "--provider-gate-output",
        "{provider_gate_output}",
        "--model-catalog-sha256",
        "{model_catalog_sha256}",
        "--model-entry-sha256",
        "{model_entry_sha256}",
        "--provider-response-bound",
        "{provider_response_bound}",
        "--provider-token-gate-compaction-canary",
        "--token-limit",
        str(CANARY_LIMIT),
        "--advisory-rollout-budget-limit",
        "5000000",
        "--model",
        "gpt-5.6-sol",
        "--reasoning-effort",
        "ultra",
    ]
    prompt_paths = {
        key: value.resolve()
        for key, value in canary._prompt_handshake_paths(usage_path.resolve()).items()
    }
    substitutions = {
        "{usage_output}": str(usage_path.resolve()),
        "{prompt_ready_output}": str(prompt_paths["ready"]),
        "{prompt_go_input}": str(prompt_paths["go"]),
        "{prompt_release_output}": str(prompt_paths["release"]),
        "{prompt_handshake_nonce}": HANDSHAKE_NONCE,
        "{run_id}": canary.CANARY_RUN_ID,
        "{provider_gate_live_output}": str(
            runner.provider_gate_paths(usage_path.resolve())["live"]
        ),
        "{provider_gate_output}": str(
            runner.provider_gate_paths(usage_path.resolve())["final"]
        ),
        "{model_catalog_sha256}": "2" * 64,
        "{model_entry_sha256}": "3" * 64,
        "{provider_response_bound}": "272000",
    }
    record["agent_command"] = [
        substitutions.get(item, item.replace("{workspace}", "/tmp/workspace"))
        for item in provider
    ]
    attach_prompt_release(record, usage, usage_path)
    attach_provider_gate(record, usage, usage_path)
    write_json(usage_path, usage)
    write_json(record_path, record)
    raw_path.write_text(json.dumps(record, sort_keys=True) + "\n", encoding="utf-8")
    outer = [
        "runner",
        "--condition",
        "N",
        "--task-id",
        canary.CANARY_ID,
        "--paper-id",
        "SYNTHETIC",
        "--token-limit",
        str(CANARY_LIMIT),
        "--prompt-startup-timeout-seconds",
        "120",
        "--task-root",
        str(inputs.resolve()),
        "--controlled-manifest",
        str(controlled.resolve()),
        "--canonical-relative",
        "task/SyntheticTarget.lean",
        "--prompt-relative",
        "task/prompt.md",
        "--usage-output",
        str(usage_path.resolve()),
        "--raw-jsonl",
        str(raw_path.resolve()),
        "--output",
        str(record_path.resolve()),
        "--agent-command-json",
        json.dumps(provider, separators=(",", ":")),
    ]
    invocation = canary._self_hashed(
        {
            "schema_version": 1,
            "kind": "highambench-synthetic-token-canary-invocation",
            "argv": outer,
            "prompt_protocol": canary.PROMPT_PROTOCOL,
            "prompt_provenance_sha256": sha256_file(provenance_path),
            "benchmark_source_audit_sha256": sha256_file(source_path),
            "benchmark_task_bytes_used": False,
            "provider_input_role": "synthetic_prompt_context_target_only",
        }
    )
    invocation_path = results / "logs" / "invocation.json"
    write_json(invocation_path, invocation)
    outcome = canary.validate_canary_record(
        record,
        canary_limit=CANARY_LIMIT,
        agent_log=agent_log,
        usage_artifact=usage,
    )
    outcome["prompt_release"] = canary.authenticate_prompt_release(
        record,
        usage_artifact=usage,
        usage_path=usage_path,
        provider_command=record["agent_command"],
        wall_time_seconds=300,
    )
    paths = {
        "record": record_path,
        "agent_log": agent_log,
        "usage": usage_path,
        "provider_gate": runner.provider_gate_paths(usage_path.resolve())["final"],
        "raw_jsonl": raw_path,
        "common_prompt": prompt,
        "context": context,
        "synthetic_target": target,
        "controlled_manifest": controlled,
        "benchmark_source_audit": source_path,
        "synthetic_prompt_provenance": provenance_path,
        "freeze_check": freeze_path,
        "runner_freeze_check": runner_freeze_path,
        "invocation": invocation_path,
    }
    evidence = canary.build_attestation(
        production_freeze_check=production_freeze,
        runner_freeze_check=runner_freeze,
        frozen_token_limit=5_000_000,
        canary_token_limit=CANARY_LIMIT,
        canary_time_limit_seconds=300,
        result_root=results,
        project_root=project,
        paths=paths,
        outcome=outcome,
        source_separation=source,
    )
    expected_agent = canary._attestation_agent(production_freeze)
    return evidence, expected_agent, results, production_freeze


class TokenControlCanaryTests(unittest.TestCase):
    def test_adapter_command_has_no_empty_argument_and_uses_existing_task_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = argparse.Namespace(
                benchmark_root=root / "benchmark",
                codex=root / "codex",
                auth_file=root / "auth.json",
                offline_shell=root / "offline-shell",
                toolchain_root=root / "toolchain",
                packages_runtime_root=root / "packages",
                model="gpt-5.6-sol",
                reasoning_effort="ultra",
                canary_token_limit=CANARY_LIMIT,
                token_limit=5_000_000,
            )
            command = canary._adapter_command(args, state_parent=root / "state")
            self.assertNotIn("", command)
            position = command.index("--shared-root-relative")
            self.assertEqual(command[position + 1], "task")
            self.assertIsNotNone(
                runner.parse_command_json(
                    json.dumps(command), option="--agent-command-json"
                )
            )

    def test_synthetic_prompt_is_deterministic_large_and_non_matrix(self) -> None:
        first = canary.prompt_record()
        second = canary.prompt_record()
        self.assertEqual(first, second)
        self.assertGreater(first["context_bytes"], 250_000)
        self.assertGreater(first["effective_prompt_bytes"], first["context_bytes"])
        self.assertTrue(first["inert_payload_bytes_at_least_250000"])
        self.assertFalse(first["benchmark_task_bytes_used"])
        self.assertNotIn("P01-T1", canary.synthetic_effective_prompt())
        self.assertNotIn("NumStability", canary.synthetic_effective_prompt())

    def test_synthetic_protocol_uses_production_signposted_composition(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            task = Path(raw) / "task"
            prompt, context, target = canary._write_synthetic_inputs(task)
            manifest = create_manifest(
                task,
                requested=["prompt.md", "context.md", "SyntheticTarget.lean"],
                label="synthetic-token-control-canary",
            )
            command = [
                "adapter",
                "--condition",
                "N",
                "--prompt-file",
                str(prompt),
                "--context-file",
                str(context),
                "--target-file",
                str(target),
            ]
            provenance = runner.build_prompt_provenance(
                condition="N",
                freeze_check={
                    "prompt_protocol": canary.synthetic_signposted_prompt_protocol()
                },
                agent_command=command,
                task_root=task,
                task_destination=task,
                controlled_manifest=manifest,
                canonical_target=target,
            )
            self.assertEqual(provenance, canary.synthetic_prompt_provenance_record())
            self.assertIsNone(provenance["condition_supplement"])

    def test_deterministic_first_response_crossing_and_projection_v6(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            runner_freeze = {"fixture": True}
            _events, log, _usage_path, usage, record = complete_crossing_fixture(
                root, runner_freeze
            )
            outcome = canary.validate_canary_record(
                record,
                canary_limit=CANARY_LIMIT,
                agent_log=log,
                usage_artifact=usage,
            )
            self.assertEqual(outcome["first_crossing_tokens"], CROSSING_TOTAL_TOKENS)
            self.assertEqual(outcome["final_endpoint_tokens"], CROSSING_TOTAL_TOKENS)
            self.assertEqual(outcome["response_count"], 2)
            self.assertEqual(outcome["thread_count"], 1)
            self.assertEqual(outcome["observed_child_thread_count"], 0)
            self.assertFalse(outcome["natural_completion"])
            self.assertFalse(outcome["accounting_projection"]["accounting_complete"])
            self.assertEqual(
                outcome["event_order"]["observed_order"],
                "below_cap_direct_final_then_compaction_item_then_crossing_"
                "rawResponse_completed_then_no_model_activity",
            )

    def test_live_compaction_notification_order_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            events, _log, _usage_path, usage, record = complete_crossing_fixture(root)
            rpc_index = next(
                index
                for index, event in enumerate(events)
                if event.get("id") == codex_isolated.THREAD_COMPACT_REQUEST_ID
                and "method" not in event
            )
            compact_rpc_reply = events.pop(rpc_index)
            compaction_turn_index = next(
                index
                for index, event in enumerate(events)
                if event.get("method") == "turn/started"
                and event.get("params", {}).get("turn", {}).get("id")
                == COMPACTION_TURN
            )
            events.insert(compaction_turn_index, compact_rpc_reply)
            events.extend(
                [
                    {
                        "method": "thread/tokenUsage/updated",
                        "params": {
                            "threadId": ROOT,
                            "turnId": COMPACTION_TURN,
                            "tokenUsage": {"total": {}, "last": {}},
                        },
                    },
                    {
                        "method": "account/rateLimits/updated",
                        "params": {"rateLimits": {}},
                    },
                    {
                        "method": "item/completed",
                        "params": {
                            "threadId": ROOT,
                            "turnId": COMPACTION_TURN,
                            "item": {
                                "type": "contextCompaction",
                                "id": "compact-item",
                            },
                        },
                    },
                    {
                        "method": "thread/status/changed",
                        "params": {"threadId": ROOT, "status": {"type": "idle"}},
                    },
                    {
                        "method": "turn/completed",
                        "params": {
                            "threadId": ROOT,
                            "turn": {
                                "id": COMPACTION_TURN,
                                "status": "completed",
                            },
                        },
                    },
                ]
            )
            live_order_log = root / "compact-rpc-before-notifications.log"
            write_log(live_order_log, events)

            outcome = canary.validate_canary_record(
                record,
                canary_limit=CANARY_LIMIT,
                agent_log=live_order_log,
                usage_artifact=usage,
            )
            self.assertEqual(outcome["response_count"], 2)
            self.assertEqual(outcome["final_endpoint_tokens"], CROSSING_TOTAL_TOKENS)

    def test_split_hook_trust_fields_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _events, log, _usage_path, usage, record = complete_crossing_fixture(root)
            authentication = record["provider_token_gate"]["final"]["authentication"]
            mutations = {
                "hook_trust_bypass_cli_flag_present": False,
                "hook_trust_bypass_thread_config": {
                    "bypass_hook_trust": False
                },
                "hook_trust_bypass_effective_source": "cli_flag",
            }
            for field, replacement in mutations.items():
                with self.subTest(field=field):
                    tampered = copy.deepcopy(usage)
                    tampered["fork_policy"][field] = replacement
                    with self.assertRaisesRegex(
                        BenchmarkToolError, "fork policy|fork_policy|fork-policy"
                    ):
                        canary.validate_usage_and_log(
                            tampered,
                            log,
                            token_limit=CANARY_LIMIT,
                            gate_authentication=authentication,
                        )

    def test_token_canary_requires_clean_adapter_exit(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _events, log, _usage_path, usage, record = complete_crossing_fixture(root)
            for invalid_exit in (2, False, 0.0, None):
                with self.subTest(agent_exit_code=invalid_exit):
                    invalid = copy.deepcopy(record)
                    invalid["agent_exit_code"] = invalid_exit
                    with self.assertRaisesRegex(
                        BenchmarkToolError, "runner outcome is invalid"
                    ):
                        canary.validate_canary_record(
                            invalid,
                            canary_limit=CANARY_LIMIT,
                            agent_log=log,
                            usage_artifact=usage,
                        )

    def test_exact_crossing_and_action_quarantine_are_mandatory(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            events, log, _usage_path, usage, record = complete_crossing_fixture(root)
            usage["drain_complete"] = True
            usage["measurement_exact"] = False
            invalid = copy.deepcopy(record)
            invalid["token_usage"] = runner._read_ultra_token_usage(usage)
            with self.assertRaises(BenchmarkToolError):
                canary.validate_canary_record(
                    invalid,
                    canary_limit=CANARY_LIMIT,
                    agent_log=log,
                    usage_artifact=usage,
                )
            usage["drain_complete"] = False
            usage["measurement_exact"] = True

            contaminated = copy.deepcopy(events)
            contaminated.append(
                {
                    "method": "item/completed",
                    "params": {
                        "threadId": ROOT,
                        "turnId": TURN,
                        "item": {"type": "agentMessage", "text": "leaked"},
                    },
                }
            )
            bad_log = root / "contaminated.log"
            write_log(bad_log, contaminated)
            with self.assertRaisesRegex(
                BenchmarkToolError, "action|assistant|provider answer content|first turn"
            ):
                canary.validate_canary_record(
                    record,
                    canary_limit=CANARY_LIMIT,
                    agent_log=bad_log,
                    usage_artifact=usage,
                )

            post_crossing_content = (
                {
                    "method": "rawResponseItem/completed",
                    "params": {
                        "threadId": ROOT,
                        "turnId": COMPACTION_TURN,
                        "item": {"type": "reasoning", "text": "late"},
                    },
                },
                {
                    "method": "item/completed",
                    "params": {
                        "threadId": ROOT,
                        "turnId": COMPACTION_TURN,
                        "item": {"type": "agentMessage", "text": "late"},
                    },
                },
            )
            for index, late_event in enumerate(post_crossing_content):
                with self.subTest(post_crossing_content=index):
                    late_log = root / f"post-crossing-{index}.log"
                    write_log(late_log, [*events, late_event])
                    with self.assertRaisesRegex(
                        BenchmarkToolError, "post-crossing model activity"
                    ):
                        canary.validate_canary_record(
                            record,
                            canary_limit=CANARY_LIMIT,
                            agent_log=late_log,
                            usage_artifact=usage,
                        )

    def test_tool_call_or_second_response_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            events, _log, _usage_path, usage, record = complete_crossing_fixture(root)
            events.insert(
                2,
                {
                    "method": "item/started",
                    "params": {
                        "threadId": ROOT,
                        "turnId": TURN,
                        "item": {"type": "commandExecution", "id": "tool"},
                    },
                },
            )
            log = root / "agent.log"
            write_log(log, events)
            with self.assertRaisesRegex(BenchmarkToolError, "forbidden tool"):
                canary.validate_usage_and_log(
                    usage,
                    log,
                    token_limit=CANARY_LIMIT,
                    gate_authentication=record["provider_token_gate"]["final"][
                        "authentication"
                    ],
                )

    def test_source_audit_rejects_benchmark_embedding_and_p01_identity(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            benchmark, manifest = make_benchmark_fixture(project)
            p01 = benchmark / "tasks" / "P01" / "T1" / "Target.lean"
            p01_bytes = p01.read_bytes()
            otherwise = {
                "common_prompt": b"synthetic-common-unique",
                "context": b"synthetic-context-unique",
                "synthetic_target": b"synthetic-target-unique",
                "effective_prompt": b"synthetic-effective-unique",
            }
            identity = dict(otherwise)
            identity["synthetic_target"] = p01_bytes
            with self.assertRaisesRegex(BenchmarkToolError, "P01/T1/Target.lean"):
                canary.audit_benchmark_source_separation(
                    project_root=project,
                    benchmark_root=benchmark,
                    manifest=manifest,
                    generated_sources=identity,
                )
            embedded = dict(otherwise)
            embedded["effective_prompt"] = b"prefix\n" + p01_bytes + b"\nsuffix"
            with self.assertRaisesRegex(BenchmarkToolError, "contains or equals"):
                canary.audit_benchmark_source_separation(
                    project_root=project,
                    benchmark_root=benchmark,
                    manifest=manifest,
                    generated_sources=embedded,
                )

    def test_attestation_authenticates_synthetic_sources_and_tamper(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, _freeze = make_evidence_fixture(project)
            summary = canary.validate_attestation_document(
                evidence,
                project_root=project,
                expected_benchmark_id="fixture-benchmark",
                expected_agent=agent,
                expected_frozen_token_limit=5_000_000,
            )
            self.assertTrue(summary["synthetic_input"])
            self.assertFalse(summary["matrix_assignment"])
            self.assertFalse(summary["benchmark_task_bytes_used"])
            self.assertEqual(summary["response_count"], 2)
            self.assertTrue(summary["prompt_release"]["artifact_content_verified"])
            self.assertEqual(
                summary["prompt_release"]["measurement_time_origin"],
                "RELEASED.released_at_monotonic_ns",
            )
            self.assertEqual(
                len(evidence["artifacts"]), len(canary.ARTIFACT_LABELS)
            )

            (results / "inputs" / "context.md").write_text(
                canary.SYNTHETIC_CONTEXT + "tamper", encoding="utf-8"
            )
            with self.assertRaisesRegex(BenchmarkToolError, "failed authentication"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

    def test_freeze_provenance_requires_promoted_ultra_agent(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, production_freeze = make_evidence_fixture(
                project
            )
            production_freeze = copy.deepcopy(production_freeze)
            production_freeze["agent"].pop("ultra_orchestration")
            runner_freeze = canary._runner_freeze_record(production_freeze)
            freeze_path = results / "logs" / "freeze_check.json"
            runner_freeze_path = results / "logs" / "runner_freeze_check.json"
            write_json(freeze_path, production_freeze)
            write_json(runner_freeze_path, runner_freeze)
            evidence["artifacts"]["freeze_check"]["sha256"] = sha256_file(
                freeze_path
            )
            evidence["artifacts"]["runner_freeze_check"]["sha256"] = sha256_file(
                runner_freeze_path
            )
            evidence["pre_canary_freeze_check_sha256"] = canary._canonical_sha256(
                production_freeze
            )
            evidence["runner_freeze_check_sha256"] = canary._canonical_sha256(
                runner_freeze
            )
            evidence["freeze_check_sha256"] = canary._canonical_sha256(
                runner_freeze
            )
            with self.assertRaisesRegex(BenchmarkToolError, "freeze provenance"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

    def test_prompt_release_artifact_and_self_hash_tamper_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, _freeze = make_evidence_fixture(project)
            release_path = next((results / "logs").glob("*.prompt-release.json"))
            payload = release_path.read_bytes()
            os.chmod(release_path, 0o644)
            release_path.write_bytes(payload.replace(b'"flushed"', b'"tampered"'))
            os.chmod(release_path, 0o444)
            with self.assertRaisesRegex(BenchmarkToolError, "file hash"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, _freeze = make_evidence_fixture(project)
            ready_path = next((results / "logs").glob("*.prompt-ready.json"))
            ready = json.loads(ready_path.read_text(encoding="utf-8"))
            ready["ready_sha256"] = "e" * 64
            os.chmod(ready_path, 0o644)
            ready_path.write_text(
                json.dumps(
                    ready,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                + "\n",
                encoding="utf-8",
            )
            os.chmod(ready_path, 0o444)
            record_path = results / "attempts" / "record.json"
            record = json.loads(record_path.read_text(encoding="utf-8"))
            descriptor = record["prompt_release"]["ready"]
            descriptor["file_sha256"] = sha256_file(ready_path)
            descriptor["record_sha256"] = ready["ready_sha256"]
            descriptor["record"] = ready
            write_json(record_path, record)
            evidence["artifacts"]["record"]["sha256"] = sha256_file(record_path)
            with self.assertRaisesRegex(BenchmarkToolError, "self hash"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

    def test_prompt_release_command_nonce_and_deadline_fail_closed(self) -> None:
        def rewrite_record(evidence: dict, results: Path, record: dict) -> None:
            path = results / "attempts" / "record.json"
            write_json(path, record)
            evidence["artifacts"]["record"]["sha256"] = sha256_file(path)

        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, _freeze = make_evidence_fixture(project)
            record_path = results / "attempts" / "record.json"
            record = json.loads(record_path.read_text(encoding="utf-8"))
            position = record["agent_command"].index("--prompt-handshake-nonce")
            record["agent_command"][position + 1] = "d" * 64
            rewrite_record(evidence, results, record)
            with self.assertRaisesRegex(BenchmarkToolError, "handshake binding"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, _freeze = make_evidence_fixture(project)
            record_path = results / "attempts" / "record.json"
            record = json.loads(record_path.read_text(encoding="utf-8"))
            record["actual_stop_seconds"] = 300.0
            rewrite_record(evidence, results, record)
            with self.assertRaisesRegex(BenchmarkToolError, "measured from"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

    def test_source_summary_contamination_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, _results, _freeze = make_evidence_fixture(project)
            evidence = copy.deepcopy(evidence)
            evidence["source_separation"]["benchmark_task_bytes_used"] = True
            with self.assertRaisesRegex(BenchmarkToolError, "source summary"):
                canary.validate_attestation_document(
                    evidence,
                    project_root=project,
                    expected_benchmark_id="fixture-benchmark",
                    expected_agent=agent,
                    expected_frozen_token_limit=5_000_000,
                )

    def test_promoter_validation_and_legacy_startup_surface(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            project = Path(raw)
            evidence, agent, results, freeze = make_evidence_fixture(project)
            evidence_path = results / "token_control_canary_attestation.json"
            write_json(evidence_path, evidence)
            promoted = canary.validate_attestation_document(
                evidence,
                project_root=project,
                expected_benchmark_id="fixture-benchmark",
                expected_agent=agent,
                expected_frozen_token_limit=5_000_000,
            )
            self.assertEqual(promoted["status"], "passed")
            # Keep every legacy startup field while adding the synthetic schema.
            for key in (
                "freeze_check_sha256",
                "pre_canary_environment_id",
                "assignment",
                "agent",
                "controls",
                "outcome",
                "artifacts",
            ):
                self.assertIn(key, evidence)
            self.assertEqual(
                evidence["controls"]["nested_advisory_rollout_budget_limit"],
                5_000_000,
            )
            self.assertEqual(
                evidence["outcome"]["notification_count_in_audit_log"], 2
            )
            self.assertEqual(
                freeze["prompt_protocol"]["version"], "signposted-library-v1"
            )


if __name__ == "__main__":
    unittest.main()
