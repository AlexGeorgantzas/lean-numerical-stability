from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

from paper_bencmark.highambench.tools.common import (
    BenchmarkToolError,
    sha256_file,
    write_json,
)
from paper_bencmark.highambench.tools.hashes import create_manifest
from paper_bencmark.highambench.tools import codex_isolated, provider_token_gate
from paper_bencmark.highambench.tools import run_matrix
from paper_bencmark.highambench.tools import runner
from paper_bencmark.highambench.tools import (
    run_ultra_orchestration_canary as canary,
)
from paper_bencmark.highambench.tools.tests.test_runner import (
    _seal_synthetic_gate,
    synthetic_provider_gate,
)


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


def attach_accepted_provider_gate(
    usage: dict,
    usage_path: Path,
    *,
    released: dict,
    prompt_sha256: str,
    token_limit: int,
) -> tuple[dict, dict]:
    """Attach and authenticate a v6 byte-identity gate for every response row."""

    gate_path = runner.provider_gate_paths(usage_path.resolve())["final"]
    gate_record, _single_usage, expected = synthetic_provider_gate(
        gate_path,
        close_reason="accepted_submission",
        token_limit=token_limit,
    )
    base_call = gate_record["calls"][0]
    completed = 0
    calls = []
    for index, response in enumerate(usage["response_ledger"], start=1):
        normalized = copy.deepcopy(response["usage"])
        raw_usage = {
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
        call = copy.deepcopy(base_call)
        committed = completed + normalized["total_tokens"]
        unix_offset = (index - 1) * 1_000
        monotonic_offset = (index - 1) * 1_000
        call.update(
            {
                "sequence": index + 2,
                "call_id": f"provider-call-{index + 2:08d}",
                "request_metadata": {
                    **call["request_metadata"],
                    "thread_id": response["thread_id"],
                    "turn_id": response["turn_id"],
                    "request_kind": "turn",
                },
                "completed_before": completed,
                "open_before": 0,
                "reserved_before": completed,
                "reservation_after": completed + runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                "admitted_unix_ns": 10_300 + unix_offset,
                "admitted_monotonic_ns": 1_300 + monotonic_offset,
                "upstream_start_unix_ns": 10_400 + unix_offset,
                "upstream_start_monotonic_ns": 1_400 + monotonic_offset,
                "response_id": response["response_id"],
                "usage": raw_usage,
                "normalized_usage": normalized,
                "previous_total": completed,
                "committed_total": committed,
                "commit_unix_ns": 10_500 + unix_offset,
                "commit_monotonic_ns": 1_500 + monotonic_offset,
                "crossed_cap": False,
                "release_kind": "byte_identity",
                "released_sanitized_event": None,
                "released_sanitized_events": None,
                "released_sanitized_body_utf8": None,
                "appserver_crossbind": {
                    "thread_id": response["thread_id"],
                    "turn_id": response["turn_id"],
                    "event_sequence": index,
                    "normalized_usage": normalized,
                    "bind_unix_ns": 10_550 + unix_offset,
                    "bind_monotonic_ns": 1_550 + monotonic_offset,
                },
            }
        )
        call["appserver_delivery"] = {
            "kind": "direct_raw_response",
            "successor_call_id": None,
            "successor_response_id": None,
            "bind_unix_ns": call["appserver_crossbind"]["bind_unix_ns"],
            "bind_monotonic_ns": call["appserver_crossbind"][
                "bind_monotonic_ns"
            ],
        }
        upstream_body = set_authenticated_upstream_sse(
            call,
            response_id=response["response_id"],
            raw_usage=raw_usage,
            request_kind="turn",
        )
        call["released_body_sha256"] = hashlib.sha256(upstream_body).hexdigest()
        call["released_body_bytes"] = len(upstream_body)
        response["provider_gate_call"] = call
        calls.append(call)
        completed = committed

    usage_fields = (
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    )
    zero_usage = {field: 0 for field in usage_fields}
    usage["provider_usage_reconciliation"] = {
        "schema_version": codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        "provider_response_count": usage["response_count"],
        "appserver_response_count": usage["response_count"],
        "suppressed_collaboration_wait_response_count": 0,
        "provider_usage": {field: usage[field] for field in usage_fields},
        "appserver_usage": {field: usage[field] for field in usage_fields},
        "suppressed_collaboration_wait_usage": zero_usage,
        "provider_response_ids": list(usage["response_ids"]),
        "appserver_response_ids": list(usage["response_ids"]),
        "suppressed_collaboration_wait_response_ids": [],
        "suppressed_collaboration_wait_evidence": [],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_usage": copy.deepcopy(zero_usage),
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_usage": copy.deepcopy(zero_usage),
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_evidence": [],
    }

    terminal_sequence = len(calls) + 3
    gate_record["calls"] = calls
    gate_record["state"].update(
        {
            "completed_tokens": completed,
            "sequence": terminal_sequence,
        }
    )
    gate_record["transitions"][-1].update(
        {
            "sequence": terminal_sequence,
            "call_id": None,
            "unix_ns": 10_600 + len(calls) * 1_000,
            "monotonic_ns": 1_600 + len(calls) * 1_000,
        }
    )
    gate_record["lifecycle"].update(
        {
            "stopped_unix_ns": 10_700 + len(calls) * 1_000,
            "stopped_monotonic_ns": 1_700 + len(calls) * 1_000,
            "finalized_unix_ns": 10_800 + len(calls) * 1_000,
            "finalized_monotonic_ns": 1_800 + len(calls) * 1_000,
        }
    )
    gate_record["bindings"].update(
        {
            "run_id": canary.CANARY_ID,
            "root_thread_id": usage["root_thread_id"],
            "prompt_release_sha256": runner._provider_gate_prompt_release_sha256(
                released
            ),
            "prompt_release_protocol": "highambench-prompt-release-v1",
            "prompt_sha256": prompt_sha256,
        }
    )
    boundary = usage["submission_boundary"]
    boundary["provider_gate_close"] = {
        "won": True,
        "requested_reason": "accepted_submission",
        "effective_reason": "accepted_submission",
        "phase": "CLOSED",
        "sequence": terminal_sequence,
    }
    _seal_synthetic_gate(gate_path, gate_record)
    usage["provider_token_gate"] = {
        "enabled": True,
        "response_token_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
        "artifact_path": str(gate_path),
        "record_sha256": gate_record["record_sha256"],
        "final_attached": True,
        "exact_for_usage": True,
        "live": copy.deepcopy(gate_record["state"]),
        "terminal": copy.deepcopy(gate_record["state"]),
    }
    usage["adapter_teardown"] = {
        "process_group_isolated": True,
        "immediate": True,
        "stdin_closed": True,
        "signal": "SIGTERM",
        "returncode": 0,
        "completed": True,
        "started_at_unix_ns": 30_000,
        "started_at_monotonic_ns": 3_000,
        "completed_at_unix_ns": 31_000,
        "completed_at_monotonic_ns": 4_000,
    }
    _seal_synthetic_gate(gate_path, gate_record)
    normalized_usage = runner._read_ultra_token_usage(usage)
    authentication = runner.authenticate_provider_gate_artifact(
        gate_path,
        token_limit=token_limit,
        run_id=canary.CANARY_ID,
        model="gpt-5.6-sol",
        reasoning_effort="ultra",
        root_thread_id=usage["root_thread_id"],
        prompt_release_sha256=runner._provider_gate_prompt_release_sha256(released),
        prompt_release_protocol="highambench-prompt-release-v1",
        prompt_sha256=prompt_sha256,
        model_catalog_sha256=expected["model_catalog_sha256"],
        model_entry_sha256=expected["model_entry_sha256"],
        expected_transport_provenance=expected["expected_transport_provenance"],
        usage=normalized_usage,
        expected_source_sha256=expected["expected_source_sha256"],
    )
    summary = {
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
            "file": runner._provider_gate_file_status(
                runner.provider_gate_paths(usage_path.resolve())["live"]
            ),
            "authenticated_crossing": None,
        },
        "final": {
            "scoreable": True,
            "file": runner._provider_gate_file_status(gate_path),
            "authentication": authentication,
        },
        "error": None,
    }
    return authentication, summary


def validate_usage_fixture(
    usage: dict,
    agent_log: Path,
    *,
    token_limit: int,
    normalized_usage: dict | None = None,
) -> dict:
    """Reauthenticate the attached gate before invoking the public verifier."""

    gate = usage["provider_token_gate"]
    gate_path = Path(gate["artifact_path"])
    record = json.loads(gate_path.read_text(encoding="utf-8"))
    configuration = record["configuration"]
    bindings = record["bindings"]
    authentication = runner.authenticate_provider_gate_artifact(
        gate_path,
        token_limit=token_limit,
        run_id=bindings["run_id"],
        model=bindings["model"],
        reasoning_effort=bindings["reasoning_effort"],
        root_thread_id=bindings["root_thread_id"],
        prompt_release_sha256=bindings["prompt_release_sha256"],
        prompt_release_protocol=bindings["prompt_release_protocol"],
        prompt_sha256=bindings["prompt_sha256"],
        model_catalog_sha256=configuration["model_catalog_sha256"],
        model_entry_sha256=configuration["model_entry_sha256"],
        expected_transport_provenance=configuration["transport_provenance"],
        usage=runner._read_ultra_token_usage(usage),
        expected_source_sha256=record["implementation"]["source_sha256"],
    )
    return canary.validate_usage_and_log(
        usage,
        agent_log,
        token_limit=token_limit,
        normalized_usage=normalized_usage,
        gate_authentication=authentication,
    )


def turn_event(method: str, thread_id: str, turn_id: str, status: str) -> dict:
    return {
        "method": method,
        "params": {
            "threadId": thread_id,
            "turn": {"id": turn_id, "status": status},
        },
    }


def raw_event(
    response_id: str,
    thread_id: str,
    turn_id: str,
    input_tokens: int,
    output_tokens: int,
) -> dict:
    return {
        "method": codex_isolated.ULTRA_USAGE_NOTIFICATION,
        "params": {
            "responseId": response_id,
            "threadId": thread_id,
            "turnId": turn_id,
            "usage": {
                "inputTokens": input_tokens,
                "cachedInputTokens": input_tokens // 2,
                "cacheWriteInputTokens": 0,
                "outputTokens": output_tokens,
                "reasoningOutputTokens": output_tokens,
                "totalTokens": input_tokens + output_tokens,
            },
        },
    }


def cumulative_event(
    thread_id: str,
    turn_id: str,
    input_tokens: int,
    output_tokens: int,
) -> dict:
    total = {
        "inputTokens": input_tokens,
        "cachedInputTokens": input_tokens // 2,
        "cacheWriteInputTokens": 0,
        "outputTokens": output_tokens,
        "reasoningOutputTokens": output_tokens,
        "totalTokens": input_tokens + output_tokens,
    }
    return {
        "method": "thread/tokenUsage/updated",
        "params": {
            "threadId": thread_id,
            "turnId": turn_id,
            "tokenUsage": {"last": total, "total": total},
        },
    }


def initial_root_action() -> dict:
    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": "root",
            "turnId": "root-turn",
            "item": {
                "type": "function_call",
                "id": "initial-pwd-item",
                "name": "exec_command",
                "call_id": "initial-pwd-call",
                "arguments": json.dumps({"cmd": "pwd"}),
            },
        },
    }


def prior_outer_exec_item() -> dict:
    """A completed call whose output is delivered before the later submit response."""

    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": "root",
            "turnId": "root-turn",
            "item": {
                "type": "custom_tool_call",
                "id": "prior-outer-item",
                "status": "completed",
                "call_id": "prior-outer-call",
                "name": "exec",
                "input": "const r = await tools.exec_command({});\n",
            },
        },
    }


def delayed_prior_exec_output() -> dict:
    """Match the leading carryover ordering observed in the real app-server log."""

    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": "root",
            "turnId": "root-turn",
            "item": {
                "type": "custom_tool_call_output",
                "id": "prior-output-item",
                "call_id": "prior-outer-call",
                "output": "prior trusted output",
                "internal_chat_message_metadata_passthrough": {
                    "turn_id": "root-turn"
                },
            },
        },
    }


def spawn_item(
    *,
    call_id: str,
    item_id: str,
    parent: str,
    turn_id: str,
    fork_turns: str,
    task_name: str,
    message: str,
) -> dict:
    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": parent,
            "turnId": turn_id,
            "item": {
                "type": "function_call",
                "id": item_id,
                "name": "spawn_agent",
                "namespace": "collaboration",
                "call_id": call_id,
                "arguments": json.dumps(
                    {
                        "task_name": task_name,
                        "fork_turns": fork_turns,
                        "message": message,
                    },
                    sort_keys=True,
                ),
            },
        },
    }


def child_started(
    parent: str, turn_id: str, child: str, call_id: str
) -> dict:
    return {
        "method": "item/completed",
        "params": {
            "threadId": parent,
            "turnId": turn_id,
            "item": {
                "type": "subAgentActivity",
                "kind": "started",
                "id": call_id,
                "agentThreadId": child,
                "agentPath": "root/canary-child",
            },
        },
    }


def fork_policy_hook_event(
    method: str,
    *,
    call_id: str,
    thread_id: str,
    turn_id: str,
    blocked: bool,
    started_at: int,
) -> dict:
    source_path = codex_isolated.ultra_fork_policy_static_record()["source_path"]
    started = method == codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION
    reason = codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
        call_id=call_id
    )
    return {
        "method": method,
        "params": {
            "threadId": thread_id,
            "turnId": turn_id,
            "run": {
                "id": f"pre-tool-use:0:{source_path}:{call_id}",
                "eventName": codex_isolated.ULTRA_FORK_POLICY_HOOK_EVENT_NAME,
                "executionMode": codex_isolated.ULTRA_FORK_POLICY_EXECUTION_MODE,
                "handlerType": codex_isolated.ULTRA_FORK_POLICY_HANDLER_TYPE,
                "scope": codex_isolated.ULTRA_FORK_POLICY_SCOPE,
                "source": codex_isolated.ULTRA_FORK_POLICY_SOURCE,
                "sourcePath": source_path,
                "displayOrder": codex_isolated.ULTRA_FORK_POLICY_DISPLAY_ORDER,
                "statusMessage": None,
                "status": (
                    "running"
                    if started
                    else (
                        codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
                        if blocked
                        else codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
                    )
                ),
                "entries": (
                    []
                    if started or not blocked
                    else [{"kind": "feedback", "text": reason}]
                ),
                "startedAt": started_at,
                "completedAt": None if started else started_at + 1,
                "durationMs": None if started else 1,
            },
        },
    }


def submission_item() -> dict:
    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": "root",
            "turnId": "root-turn",
            "item": {
                "type": "custom_tool_call",
                "id": "outer-submit-item",
                "name": "exec",
                "status": "completed",
                "call_id": "outer-exec-call",
                "input": codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
            },
        },
    }


def dynamic_started() -> dict:
    return {
        "method": "item/started",
        "params": {
            "threadId": "root",
            "turnId": "root-turn",
            "item": {
                "type": "dynamicToolCall",
                "id": "submit-call",
                "tool": codex_isolated.SUBMISSION_TOOL_NAME,
                "namespace": None,
                "status": "inProgress",
                "arguments": {"candidate_path": "Candidate.lean"},
            },
        },
    }


def dynamic_call() -> dict:
    return {
        "id": 7,
        "method": "item/tool/call",
        "params": {
            "tool": codex_isolated.SUBMISSION_TOOL_NAME,
            "namespace": None,
            "threadId": "root",
            "turnId": "root-turn",
            "callId": "submit-call",
            "arguments": {"candidate_path": "Candidate.lean"},
        },
    }


def outer_exec_progress_output() -> dict:
    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": "root",
            "turnId": "root-turn",
            "item": {
                "type": "custom_tool_call_output",
                "id": "outer-submit-progress",
                "call_id": "outer-exec-call",
                "output": (
                    "Script running with cell ID 4\n"
                    "Wall time 11.0 seconds\nOutput:\n"
                ),
            },
        },
    }


def exact_boundary_events(
    child_count: int = 1,
    *,
    submission_event_order: str = (
        codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
    ),
) -> list[dict]:
    if child_count != 1:
        raise ValueError("the V9 canary has exactly one allowed child")
    events = [
        turn_event("turn/started", "root", "root-turn", "inProgress"),
        initial_root_action(),
        prior_outer_exec_item(),
        raw_event("root-response-1", "root", "root-turn", 100, 10),
        cumulative_event("root", "root-turn", 100, 10),
        delayed_prior_exec_output(),
    ]
    root_blocked = "call_blocked_root"
    root_allowed = "call_allowed_root"
    child_blocked = "call_blocked_child"
    child = "child-0"
    child_turn = "child-turn-0"
    events.extend(
        (
            spawn_item(
                call_id=root_blocked,
                item_id="spawn-item-blocked-root",
                parent="root",
                turn_id="root-turn",
                fork_turns="3",
                task_name="forbidden-root-child",
                message="Return HIGHAMBENCH_FORBIDDEN_ROOT_CHILD.",
            ),
            raw_event("root-blocked-response", "root", "root-turn", 20, 2),
            cumulative_event("root", "root-turn", 120, 12),
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                call_id=root_blocked,
                thread_id="root",
                turn_id="root-turn",
                blocked=True,
                started_at=100,
            ),
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                call_id=root_blocked,
                thread_id="root",
                turn_id="root-turn",
                blocked=True,
                started_at=100,
            ),
            spawn_item(
                call_id=root_allowed,
                item_id="spawn-item-allowed-root",
                parent="root",
                turn_id="root-turn",
                fork_turns="all",
                task_name="canary-child",
                message="Probe fork3 denial, then return HIGHAMBENCH_ULTRA_CHILD_OK.",
            ),
            raw_event("root-spawn-response", "root", "root-turn", 40, 4),
            cumulative_event("root", "root-turn", 160, 16),
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                call_id=root_allowed,
                thread_id="root",
                turn_id="root-turn",
                blocked=False,
                started_at=200,
            ),
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                call_id=root_allowed,
                thread_id="root",
                turn_id="root-turn",
                blocked=False,
                started_at=200,
            ),
            child_started("root", "root-turn", child, root_allowed),
            turn_event("turn/started", child, child_turn, "inProgress"),
            spawn_item(
                call_id=child_blocked,
                item_id="spawn-item-blocked-child",
                parent=child,
                turn_id=child_turn,
                fork_turns="3",
                task_name="forbidden-grandchild",
                message="Return HIGHAMBENCH_FORBIDDEN_GRANDCHILD.",
            ),
            raw_event("child-blocked-response", child, child_turn, 20, 2),
            cumulative_event(child, child_turn, 140, 14),
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                call_id=child_blocked,
                thread_id=child,
                turn_id=child_turn,
                blocked=True,
                started_at=300,
            ),
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                call_id=child_blocked,
                thread_id=child,
                turn_id=child_turn,
                blocked=True,
                started_at=300,
            ),
            raw_event("child-final-response", child, child_turn, 80, 5),
            cumulative_event(child, child_turn, 220, 19),
            turn_event("turn/completed", child, child_turn, "completed"),
        )
    )
    response = raw_event("root-submit-response", "root", "root-turn", 60, 4)
    if submission_event_order == codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE:
        submission_events = (submission_item(), dynamic_started(), dynamic_call(), response)
    elif submission_event_order == codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER:
        submission_events = (submission_item(), response, dynamic_started(), dynamic_call())
    else:
        raise ValueError("unsupported fixture submission event order")
    events.extend(
        (
            *submission_events,
            {
                "method": "thread/status/changed",
                "params": {
                    "threadId": "root",
                    "status": {"type": "shutdown"},
                },
            },
        )
    )
    return events


class UltraOrchestrationCanaryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.project = Path(self.temporary.name)
        self.artifact_root = self.project / "artifacts"
        self.artifact_root.mkdir()
        self.benchmark_root = self.project / "benchmark"
        (self.benchmark_root / "tools").mkdir(parents=True)
        source_helper = (
            Path(__file__).resolve().parents[1] / "dependency_audit.lean"
        )
        shutil.copyfile(
            source_helper,
            self.benchmark_root / "tools" / "dependency_audit.lean",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def expected_agent(self) -> dict:
        return {
            "id": "codex-cli",
            "version": "fixture",
            "binary_sha256": "a" * 64,
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "ultra_orchestration": run_matrix.ultra_orchestration_record(),
        }

    def expected_prompt_protocol(self) -> dict:
        return {"version": "fixture-production-prompt-v1"}

    def expected_execution_components(self) -> dict:
        return {
            field: format(index, "064x")
            for index, field in enumerate(
                canary.PRODUCTION_EXECUTION_COMPONENT_FIELDS, start=1
            )
        }

    def runner_args(self, token_limit: int) -> argparse.Namespace:
        return argparse.Namespace(
            benchmark_root=self.benchmark_root,
            project_root=self.project,
            codex=self.project / "codex",
            auth_file=self.project / "auth.json",
            offline_shell=self.project / "offline-shell",
            toolchain_root=self.project / "toolchain",
            packages_runtime_root=self.project / "packages-runtime",
            agent_id="codex-cli",
            agent_version="fixture",
            model="gpt-5.6-sol",
            reasoning_effort="ultra",
            token_limit=token_limit,
            environment_id="fixture-environment",
            canary_time_limit_seconds=300,
        )

    def evidence_fixture(
        self,
        child_count: int = 1,
        *,
        submission_event_order: str = (
            codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
        ),
    ) -> tuple[dict, dict, Path]:
        token_limit = 10_000
        inputs = self.artifact_root / "inputs"
        prompt_path, context_path, target_path = canary._write_synthetic_inputs(inputs)
        audit_helper_path = inputs / "dependency_audit.lean"
        shutil.copyfile(
            self.benchmark_root / "tools" / "dependency_audit.lean",
            audit_helper_path,
        )
        controlled_path = inputs / "controlled.json"
        write_json(
            controlled_path,
            create_manifest(
                inputs,
                requested=["prompt.md", "context.md", "SyntheticTarget.lean"],
                label="synthetic-ultra-submission-canary",
            ),
        )

        freeze = {
            "schema_version": 1,
            "kind": "highambench-frozen-run-verification",
            "ok": True,
            "benchmark_id": "fixture-benchmark",
            "environment_id": "fixture-environment",
            "agent": self.expected_agent(),
            "prompt_protocol": self.expected_prompt_protocol(),
            "execution_components": self.expected_execution_components(),
            "agent_session_isolation": {
                "ephemeral_thread": False,
                "fresh_state_directory": True,
                "memories_disabled": True,
                "resume_or_fork_used": False,
                "state_directory_reused": False,
            },
        }
        freeze_path = self.artifact_root / "freeze.json"
        runner_freeze_path = self.artifact_root / "runner-freeze.json"
        write_json(freeze_path, freeze)
        runner_freeze = canary._runner_freeze_record(freeze)
        write_json(runner_freeze_path, runner_freeze)

        usage_path = self.artifact_root / "usage.json"
        runner_record_path = self.artifact_root / "runner-record.json"
        raw_jsonl_path = self.artifact_root / "runner-record.jsonl"
        command = canary._runner_command(
            self.runner_args(token_limit),
            result_root=self.artifact_root,
            task_root=inputs,
            controlled_manifest=controlled_path,
            runner_freeze_check=runner_freeze,
            usage_output=usage_path,
            runner_record=runner_record_path,
            raw_jsonl=raw_jsonl_path,
            state_parent=self.artifact_root / "state",
        )
        invocation_path = self.artifact_root / "invocation.json"
        write_json(
            invocation_path,
            {
                "schema_version": 1,
                "kind": "highambench-ultra-orchestration-canary-invocation",
                "argv": command,
                "network_evidence_role": "production_runner_marker_and_monitor",
                "submission_evidence_role": (
                    "production_runner_authenticated_nested_submit_proof_boundary"
                ),
            },
        )

        compile_command = json.loads(
            str(canary._option_value(command, "--compile-command-json"))
        )
        audit_command = json.loads(
            str(canary._option_value(command, "--audit-command-json"))
        )
        contract = {
            "condition": "N",
            "submission_relative": "Submission.lean",
            "canonical_relative": "task/SyntheticTarget.lean",
            "target_theorem": canary.SYNTHETIC_TARGET_THEOREM,
            "compile_command": compile_command,
            "audit_command": audit_command,
            "controlled_manifest_sha256": sha256_file(controlled_path),
            "reject_workspace_local_module_imports": True,
        }
        contract_sha = canary._canonical_sha256(contract)
        candidate = canary.SYNTHETIC_TARGET.encode("utf-8")
        candidate_sha = hashlib.sha256(candidate).hexdigest()

        events = exact_boundary_events(
            child_count, submission_event_order=submission_event_order
        )
        ledger = codex_isolated.AttemptUsageLedger(
            self.artifact_root / "scratch-usage.json",
            token_limit,
            "root",
            fork_policy=codex_isolated.ultra_fork_policy_static_record(),
        )
        for event in events:
            if event.get("method") in ("item/tool/call", "thread/status/changed"):
                continue
            ledger.observe(event)
        pre_boundary = ledger.snapshot(drain_complete=False)
        boundary_usage = ledger.provider_boundary_usage()

        challenge = codex_isolated.authenticated_record(
            {
                "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_challenge",
                "run_id": canary.CANARY_ID,
                "attempt_nonce": "fixture-nonce",
                "validator_contract_sha256": contract_sha,
                **codex_isolated.nested_submission_exec_yield_record(),
                "published_at_unix_ns": 1,
                "published_at_monotonic_ns": 1,
            },
            "challenge_sha256",
        )
        snapshot_path = self.artifact_root / "submission-1.lean"
        snapshot_path.write_bytes(candidate)
        nested_wire = {
            "submission_transport": codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
            "outer_raw_item_id": "outer-submit-item",
            "outer_raw_item_type": "custom_tool_call",
            "outer_exec_name": "exec",
            "outer_exec_call_id": "outer-exec-call",
            "outer_exec_program": codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
            "outer_exec_program_bytes": (
                codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
            ),
            "outer_exec_program_sha256": (
                codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
            ),
            **codex_isolated.nested_submission_exec_yield_record(),
            "outer_raw_item_observed_at_monotonic_ns": 1_050_000_000,
            "inner_dynamic_item_started_at_monotonic_ns": 1_200_000_000,
            "outer_raw_item_observed_before_inner_dynamic_call": True,
            "inner_dynamic_call_id": "submit-call",
            "inner_dynamic_tool_name": codex_isolated.SUBMISSION_TOOL_NAME,
            "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
        }
        dynamic_before_response = (
            submission_event_order
            == codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
        )
        captured_monotonic_ns = 1_200_000_000 if dynamic_before_response else 1_300_000_000
        raw_response_monotonic_ns = 1_300_000_000 if dynamic_before_response else 1_100_000_000
        call = codex_isolated.authenticated_record(
            {
                "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_call",
                "sequence": 1,
                "challenge_sha256": challenge["challenge_sha256"],
                "attempt_nonce": "fixture-nonce",
                "run_id": canary.CANARY_ID,
                "validator_contract_sha256": contract_sha,
                "jsonrpc_request_id": 7,
                "call_id": "submit-call",
                **nested_wire,
                "thread_id": "root",
                "turn_id": "root-turn",
                "candidate_path": "Candidate.lean",
                "candidate_sha256": candidate_sha,
                "candidate_size_bytes": len(candidate),
                "snapshot_name": snapshot_path.name,
                "captured_at_unix_ns": 10,
                "captured_at_monotonic_ns": captured_monotonic_ns,
            },
            "call_sha256",
        )
        request = codex_isolated.authenticated_record(
            {
                "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_request",
                "sequence": 1,
                "challenge_sha256": challenge["challenge_sha256"],
                "call_sha256": call["call_sha256"],
                "attempt_nonce": "fixture-nonce",
                "run_id": canary.CANARY_ID,
                "validator_contract_sha256": contract_sha,
                "jsonrpc_request_id": 7,
                "call_id": "submit-call",
                **nested_wire,
                "thread_id": "root",
                "turn_id": "root-turn",
                "response_id": "root-submit-response",
                "raw_response_notification_sequence": pre_boundary[
                    "notification_sequence"
                ],
                "raw_response_observed_at_unix_ns": 20,
                "raw_response_observed_at_monotonic_ns": raw_response_monotonic_ns,
                "candidate_path": "Candidate.lean",
                "candidate_sha256": candidate_sha,
                "candidate_size_bytes": len(candidate),
                "snapshot_name": snapshot_path.name,
                "captured_at_unix_ns": 10,
                "captured_at_monotonic_ns": captured_monotonic_ns,
                "request_published_at_unix_ns": 2_600_000_000,
                "request_published_at_monotonic_ns": 1_600_000_000,
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
                "sequence": 1,
                "request_sha256": request["request_sha256"],
                "candidate_sha256": candidate_sha,
                "decision": "accept",
                "note": "accepted",
                "validator_accepted_at_unix_ns": 40,
                "validator_accepted_elapsed_seconds": 0.25,
                "published_at_unix_ns": 40,
                "published_at_monotonic_ns": 40,
            },
            "ack_sha256",
        )
        boundary = {
            "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
            "authenticated": True,
            "status": "accepted",
            "exact": True,
            "sequence": 1,
            "challenge_sha256": challenge["challenge_sha256"],
            "call_sha256": call["call_sha256"],
            "attempt_nonce": "fixture-nonce",
            "run_id": canary.CANARY_ID,
            "validator_contract_sha256": contract_sha,
            "request_sha256": request["request_sha256"],
            "ack_sha256": ack["ack_sha256"],
            "jsonrpc_request_id": 7,
            "call_id": "submit-call",
            **nested_wire,
            "thread_id": "root",
            "turn_id": "root-turn",
            "response_id": "root-submit-response",
            "raw_response_notification_sequence": pre_boundary[
                "notification_sequence"
            ],
            "candidate_path": "Candidate.lean",
            "candidate_sha256": candidate_sha,
            "candidate_size_bytes": len(candidate),
            "request_published_at_unix_ns": 2_600_000_000,
            "request_published_at_monotonic_ns": 1_600_000_000,
            "validator_accepted_at_unix_ns": 40,
            "validator_accepted_elapsed_seconds": 0.25,
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": submission_event_order,
            "dynamic_call_observed_before_raw_response_completed": (
                dynamic_before_response
            ),
            "raw_response_completed_before_dynamic_call_observed": (
                not dynamic_before_response
            ),
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
        }
        ledger.accept_submission_boundary(boundary)
        usage = ledger.snapshot(drain_complete=False)
        write_json(usage_path, usage)

        log_path = self.artifact_root / "agent.log"
        log_path.write_text(
            "".join(json.dumps(event, sort_keys=True) + "\n" for event in events),
            encoding="utf-8",
        )
        challenge_path = self.artifact_root / "challenge.json"
        call_path = self.artifact_root / "call.json"
        request_path = self.artifact_root / "request.json"
        ack_path = self.artifact_root / "ack.json"
        for path, value in (
            (challenge_path, challenge),
            (call_path, call),
            (request_path, request),
            (ack_path, ack),
        ):
            write_json(path, value)

        accepted_path = self.artifact_root / "accepted.lean"
        accepted_path.write_bytes(candidate)
        validation_path = self.artifact_root / "validation.json"
        validation = runner._authenticate_validation_result(
            {
                "pass": True,
                "failure_code": None,
                "reject_workspace_local_module_imports": True,
                "library_audit_complete": True,
                "library_use": False,
                "library_declarations": [],
                "dependency_audit": {
                    "system_error": None,
                    "timed_out": False,
                    "exit_code": 0,
                    "parsed": {
                        "ok": True,
                        "format_version": 2,
                        "target_seen": True,
                        "type_check": {
                            "candidate": canary.SYNTHETIC_TARGET_THEOREM,
                            "expected": "HighamBenchExpected.highamBenchUltraCanary_expected",
                            "equal": True,
                        },
                        "local_modules": [],
                        "expected_helper_modules": [],
                        "missing_helper_modules": [],
                        "library_declarations": [],
                        "forbidden_dependencies": [],
                        "malformed_lines": [],
                    },
                },
            },
            run_id=canary.CANARY_ID,
            task_id=canary.CANARY_ID,
            candidate_sha256=candidate_sha,
            target_theorem=canary.SYNTHETIC_TARGET_THEOREM,
            controlled_manifest_sha256=sha256_file(controlled_path),
            validator_contract_sha256=contract_sha,
            submission_request_sha256=request["request_sha256"],
            submission_sequence=1,
        )
        write_json(validation_path, validation)
        retained_paths = {
            "challenge": challenge_path,
            "call": call_path,
            "request": request_path,
            "ack": ack_path,
            "snapshot": snapshot_path,
        }
        retained_hashes = {
            "challenge": challenge["challenge_sha256"],
            "call": call["call_sha256"],
            "request": request["request_sha256"],
            "ack": ack["ack_sha256"],
        }
        retained = {}
        for label, path in retained_paths.items():
            retained[label] = {
                "path": str(path.resolve()),
                "file_sha256": sha256_file(path),
                **(
                    {"record_sha256": retained_hashes[label]}
                    if label != "snapshot"
                    else {"size_bytes": len(candidate)}
                ),
            }
            path.chmod(0o444)

        normalized_usage = runner.read_token_usage(usage_path)
        assert normalized_usage is not None
        prompt_paths = codex_isolated.prompt_handshake_paths(usage_path)
        prompt_nonce = "f" * 64
        effective_prompt = canary.synthetic_effective_prompt()
        effective_bytes = effective_prompt.encode("utf-8")
        prompt_common = {
            "schema_version": 1,
            "protocol_version": "highambench-prompt-release-v1",
            "handshake_nonce": prompt_nonce,
            "run_id": canary.CANARY_ID,
            "condition": "N",
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "root_thread_id": "root",
            "turn_start_request_id": 3,
            "effective_prompt_sha256": hashlib.sha256(effective_bytes).hexdigest(),
            "effective_prompt_bytes": len(effective_bytes),
            "adapter_name": "codex_isolated.py",
            "adapter_version": "1",
            "app_server_client_name": "highambench-isolated",
            "app_server_client_version": "1",
            "elapsed_clock": "CLOCK_MONOTONIC",
        }

        def prompt_record(value: dict, hash_field: str, path: Path) -> dict:
            authenticated = codex_isolated.authenticated_record(value, hash_field)
            payload = (
                json.dumps(
                    authenticated,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                + "\n"
            ).encode("utf-8")
            path.write_bytes(payload)
            path.chmod(0o444)
            return authenticated

        ready = prompt_record(
            {
                **prompt_common,
                "kind": "highambench_prompt_ready",
                "turn_start_write_state": "not_started",
                "ready_at_monotonic_ns": 998_000_000,
                "ready_at_unix_ns": 1_998_000_000,
            },
            "ready_sha256",
            prompt_paths["ready"],
        )
        go = prompt_record(
            {
                **prompt_common,
                "kind": "highambench_prompt_go",
                "ready_sha256": ready["ready_sha256"],
                "turn_start_write_authorized": True,
                "authorized_at_monotonic_ns": 999_000_000,
                "authorized_at_unix_ns": 1_999_000_000,
            },
            "go_sha256",
            prompt_paths["go"],
        )
        turn_start = codex_isolated.prompt_turn_start_request(
            prompt=effective_prompt,
            root_thread_id="root",
            model="gpt-5.6-sol",
            reasoning_effort="ultra",
        )
        wire = codex_isolated.canonical_protocol_wire(turn_start)
        released = prompt_record(
            {
                **prompt_common,
                "kind": "highambench_prompt_released",
                "ready_sha256": ready["ready_sha256"],
                "go_sha256": go["go_sha256"],
                "turn_start_write_state": "flushed",
                "timestamp_capture_point": "immediately_before_turn_start_write",
                "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
                "turn_start_request_bytes": len(wire),
                "released_at_monotonic_ns": 1_000_000_000,
                "released_at_unix_ns": 2_000_000_000,
                "turn_start_flushed_at_monotonic_ns": 1_000_000_001,
                "turn_start_flushed_at_unix_ns": 2_000_000_001,
            },
            "release_sha256",
            prompt_paths["release"],
        )
        descriptors = {}
        for name, prompt_artifact_path, prompt_value, hash_field in (
            ("ready", prompt_paths["ready"], ready, "ready_sha256"),
            ("go", prompt_paths["go"], go, "go_sha256"),
            ("released", prompt_paths["release"], released, "release_sha256"),
        ):
            descriptors[name] = {
                "path": str(prompt_artifact_path.resolve()),
                "file_sha256": sha256_file(prompt_artifact_path),
                "record_sha256": prompt_value[hash_field],
                "record": prompt_value,
            }
        gate_authentication, gate_summary = attach_accepted_provider_gate(
            usage,
            usage_path,
            released=released,
            prompt_sha256=hashlib.sha256(effective_bytes).hexdigest(),
            token_limit=token_limit,
        )
        write_json(usage_path, usage)
        normalized_usage = runner.read_token_usage(usage_path)
        assert normalized_usage is not None
        adapter_template = json.loads(
            str(canary._option_value(command, "--agent-command-json"))
        )
        rendered_agent_command = runner.render_command(
            adapter_template,
            {
                "workspace": self.artifact_root / "workspace",
                "submission": self.artifact_root / "workspace" / "Submission.lean",
                "condition": "N",
                "seed": "",
                "prompt_file": self.artifact_root / "workspace" / "task" / "prompt.md",
                "time_limit": 300,
                "token_limit": token_limit,
                "usage_output": usage_path,
                "network_violation_marker": self.artifact_root / "network.marker",
                "prompt_ready_output": prompt_paths["ready"],
                "prompt_go_input": prompt_paths["go"],
                "prompt_release_output": prompt_paths["release"],
                "prompt_handshake_nonce": prompt_nonce,
                "run_id": canary.CANARY_ID,
                "provider_gate_live_output": runner.provider_gate_paths(
                    usage_path.resolve()
                )["live"],
                "provider_gate_output": runner.provider_gate_paths(
                    usage_path.resolve()
                )["final"],
                "model_catalog_sha256": gate_summary["model_catalog"][
                    "catalog_sha256"
                ],
                "model_entry_sha256": gate_summary["model_catalog"][
                    "entry_sha256"
                ],
                "provider_response_bound": runner.PROVIDER_RESPONSE_TOKEN_BOUND,
            },
        )
        runner_record = {
            "schema_version": 1,
            "kind": "highambench-run",
            "run_id": canary.CANARY_ID,
            "task_id": canary.CANARY_ID,
            "condition": "N",
            "agent": self.expected_agent(),
            "pass": True,
            "scored": True,
            "failure_code": None,
            "first_valid_seconds": 0.6,
            "actual_stop_seconds": 0.7,
            "scored_elapsed_seconds": 0.6,
            "limits": {"model_tokens": token_limit},
            "time_measurement": (
                "authenticated CLOCK_MONOTONIC turn/start write to authenticated "
                "nested submission-boundary publication after outer exec raw-response "
                "completion with inner submit_proof blocked; hidden validation certifies "
                "the immutable requested bytes"
            ),
            "token_usage": normalized_usage,
            "provider_token_gate": gate_summary,
            "prompt_provenance": canary.synthetic_runner_prompt_provenance(),
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
                "handshake_nonce": prompt_nonce,
                "elapsed_clock": "CLOCK_MONOTONIC",
                "artifact_paths": {
                    "ready": str(prompt_paths["ready"].resolve()),
                    "go": str(prompt_paths["go"].resolve()),
                    "release": str(prompt_paths["release"].resolve()),
                },
                "effective_prompt_sha256": hashlib.sha256(effective_bytes).hexdigest(),
                "effective_prompt_bytes": len(effective_bytes),
                **descriptors,
                "stale_artifacts_removed": [],
                "error": None,
            },
            "agent_command": rendered_agent_command,
            "agent_exit_code": 0,
            "validation_log": str(validation_path.resolve()),
            "validation_log_sha256": sha256_file(validation_path),
            "validation_record_sha256": validation["record_sha256"],
            "accepted_submission_log": str(accepted_path.resolve()),
            "agent_log": str(log_path.resolve()),
            "submission_sha256": candidate_sha,
            "final_submission_sha256": candidate_sha,
            "submission_changed_after_acceptance": False,
            "ultra_submission_boundary": {
                "verified": True,
                "sequence": 1,
                "request_sha256": request["request_sha256"],
                "ack_sha256": ack["ack_sha256"],
                "artifacts": retained,
            },
            "protocol": {
                "complete": True,
                "verified": {
                    "authenticated_prompt_release": True,
                    "authenticated_first_valid_proof_boundary": True,
                    "authenticated_provider_token_gate": True,
                    "provider_gate_appserver_deliveries_reconciled": True,
                    "provider_gate_terminal_endpoint": True,
                },
            },
            "n_preflight": {"ok": True, "complete": True},
            "network_violation": {"detected": False, "integrity_ok": True},
        }
        write_json(runner_record_path, runner_record)
        raw_jsonl_path.write_text(
            json.dumps(runner_record, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )

        artifacts = {
            label: {
                "path": path.relative_to(self.artifact_root).as_posix(),
                "sha256": sha256_file(path),
            }
            for label, path in {
                "agent_log": log_path,
                "usage": usage_path,
                "freeze_check": freeze_path,
                "runner_freeze_check": runner_freeze_path,
                "invocation": invocation_path,
                "common_prompt": prompt_path,
                "context": context_path,
                "synthetic_target": target_path,
                "controlled_manifest": controlled_path,
                "dependency_audit_helper": audit_helper_path,
                "runner_record": runner_record_path,
                "raw_jsonl": raw_jsonl_path,
                "validation": validation_path,
                "accepted_candidate": accepted_path,
                "barrier_challenge": challenge_path,
                "barrier_call": call_path,
                "barrier_request": request_path,
                "barrier_ack": ack_path,
                "barrier_snapshot": snapshot_path,
                "provider_gate": runner.provider_gate_paths(
                    usage_path.resolve()
                )["final"],
            }.items()
        }
        outcome = canary.validate_usage_and_log(
            usage,
            log_path,
            token_limit=token_limit,
            gate_authentication=gate_authentication,
        )
        outcome["prompt_release"] = canary._verify_prompt_release(
            runner_record,
            usage_path=usage_path,
            request_path=request_path,
            artifact_root=self.artifact_root,
            wall_time_seconds=300,
        )
        evidence = {
            "schema_version": 1,
            "kind": canary.EVIDENCE_KIND,
            "status": "passed",
            "public_release": False,
            "scored": False,
            "matrix_assignment": False,
            "synthetic_input": True,
            "canary_id": canary.CANARY_ID,
            "benchmark_id": "fixture-benchmark",
            "pre_canary_environment_id": "fixture-environment",
            "freeze_check_sha256": canary._canonical_sha256(freeze),
            "agent": self.expected_agent(),
            "prompt": canary.prompt_record(),
            "artifact_root": "artifacts",
            "controls": canary.controls_record(token_limit, 300),
            "outcome": outcome,
            "artifacts": artifacts,
        }
        return evidence, usage, log_path

    def test_prompt_requires_completed_root_response_then_fork_all(self) -> None:
        prompt = canary.synthetic_effective_prompt()
        self.assertIn("first task action MUST be exactly one `exec_command`", prompt)
        self.assertIn("root has completed one model response", prompt)
        self.assertIn('`fork_turns="3"`', prompt)
        self.assertIn("frozen policy hook must deny", prompt)
        self.assertIn("`fork_turns=\"all\"`", prompt)
        self.assertIn("Candidate.lean", prompt)
        self.assertIn("submit_proof", prompt)
        self.assertIn("exactly one model tool call: code-mode", prompt)
        self.assertIn('// @exec: {"yield_time_ms": 2400000}', prompt)
        self.assertIn(codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE.rstrip(), prompt)
        self.assertIn("Never create, modify, rename, or copy to `Submission.lean`", prompt)
        self.assertNotIn("P01-T1", prompt)
        self.assertEqual(canary.prompt_record()["protocol"], canary.PROMPT_PROTOCOL)

    def test_authenticated_boundary_with_positive_usage_child_is_accepted(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        summary = canary.verify_evidence_document(
            evidence,
            project_root=self.project,
            expected_benchmark_id="fixture-benchmark",
            expected_agent=self.expected_agent(),
            expected_token_limit=10_000,
            expected_prompt_protocol=self.expected_prompt_protocol(),
            expected_execution_components=self.expected_execution_components(),
        )
        self.assertEqual(summary["thread_count"], 2)
        self.assertEqual(summary["positive_usage_descendant_thread_count"], 1)
        self.assertTrue(summary["measurement_exact"])
        self.assertTrue(summary["submission_boundary_exact"])
        self.assertTrue(summary["prompt_release"]["authenticated"])
        self.assertTrue(
            summary["prompt_release"]["request_publication_timing_verified"]
        )
        projection = summary["accounting_projection"]
        self.assertEqual(
            projection["accounting_projection_schema_version"],
            canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION,
        )

        self.assertTrue(projection["raw_call_activity_id_match"])
        self.assertTrue(projection["completed_root_response_before_spawn"])
        self.assertEqual(projection["activity_spawn_call_ids"], ["call_allowed_root"])
        self.assertEqual(projection["resolved_spawn_call_ids"], ["call_allowed_root"])
        self.assertEqual(
            projection["policy_blocked_spawn_call_ids"],
            ["call_blocked_child", "call_blocked_root"],
        )
        self.assertEqual(
            projection["hook_observed_spawn_call_ids"],
            projection["raw_spawn_call_ids"],
        )
        self.assertEqual(
            projection["nonzero_inherited_baseline_child_thread_ids"], ["child-0"]
        )
        child_accounting = next(
            thread
            for thread in projection["thread_accounting"]
            if thread["thread_id"] == "child-0"
        )
        self.assertEqual(
            child_accounting["expected_cumulative_baseline"]["total_tokens"],
            132,
        )
        self.assertEqual(
            child_accounting["last_cumulative"],
            child_accounting["expected_cumulative_projection"],
        )
        self.assertEqual(
            projection["pre_spawn_completed_root_response_counts"],
            {"call_allowed_root": 2},
        )
        self.assertTrue(projection["fork_policy_complete"])
        self.assertTrue(projection["accounting_complete"])
        self.assertTrue(summary["validation_authentication"]["authenticated"])
        self.assertTrue(summary["dependency_audit"]["complete"])
        self.assertFalse(summary["dependency_audit"]["library_use"])
        self.assertEqual(
            summary["dependency_audit"]["helper_sha256"],
            sha256_file(self.benchmark_root / "tools" / "dependency_audit.lean"),
        )
        self.assertFalse(summary["drain_complete"])
        self.assertTrue(summary["barrier"]["root_blocked_at_boundary"])
        self.assertEqual(
            summary["barrier"]["outer_exec_yield_time_ms"], 2_400_000
        )
        self.assertEqual(
            summary["barrier"]["outer_exec_yield_envelope_ms"], 2_169_000
        )
        self.assertEqual(
            summary["barrier"]["outer_exec_yield_margin_ms"], 231_000
        )
        self.assertTrue(
            summary["barrier"][
                "dynamic_call_observed_before_raw_response_completed"
            ]
        )

    def test_response_before_inner_schema_v5_notification_order_is_accepted(self) -> None:
        order = codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
        evidence, usage, log = self.evidence_fixture(
            submission_event_order=order
        )
        validate_usage_fixture(usage, log, token_limit=10_000)
        summary = canary.verify_evidence_document(
            evidence,
            project_root=self.project,
            expected_benchmark_id="fixture-benchmark",
            expected_agent=self.expected_agent(),
            expected_token_limit=10_000,
            expected_prompt_protocol=self.expected_prompt_protocol(),
            expected_execution_components=self.expected_execution_components(),
        )
        barrier = summary["barrier"]
        self.assertEqual(barrier["submission_event_order"], order)
        self.assertIs(
            barrier["dynamic_call_observed_before_raw_response_completed"], False
        )
        self.assertIs(
            barrier["raw_response_completed_before_dynamic_call_observed"], True
        )
        self.assertFalse(summary["drain_complete"])
        self.assertTrue(summary["barrier"]["root_blocked_at_boundary"])

    def test_prompt_release_artifact_tamper_fails_closed(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        runner_path = self.artifact_root / evidence["artifacts"]["runner_record"]["path"]
        record = json.loads(runner_path.read_text(encoding="utf-8"))
        released = Path(record["prompt_release"]["released"]["path"])
        released.chmod(0o644)
        released.write_bytes(released.read_bytes() + b" ")
        with self.assertRaisesRegex(
            BenchmarkToolError, "prompt released artifact"
        ):
            canary.verify_evidence_document(
                evidence,
                project_root=self.project,
                expected_benchmark_id="fixture-benchmark",
                expected_agent=self.expected_agent(),
                expected_token_limit=10_000,
                expected_prompt_protocol=self.expected_prompt_protocol(),
                expected_execution_components=self.expected_execution_components(),
            )

    def test_v6_fixture_requires_exactly_one_allowed_child(self) -> None:
        with self.assertRaisesRegex(ValueError, "exactly one allowed child"):
            exact_boundary_events(child_count=2)

    def test_production_freeze_binding_rejects_stale_prompt_and_components(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        common = {
            "project_root": self.project,
            "expected_benchmark_id": "fixture-benchmark",
            "expected_agent": self.expected_agent(),
            "expected_token_limit": 10_000,
        }
        with self.assertRaisesRegex(
            BenchmarkToolError, "freeze check is inconsistent"
        ):
            canary.verify_evidence_document(
                evidence,
                **common,
                expected_prompt_protocol={"version": "stale"},
                expected_execution_components=self.expected_execution_components(),
            )

        stale_components = self.expected_execution_components()
        stale_components["runner_sha256"] = "f" * 64
        with self.assertRaisesRegex(
            BenchmarkToolError, "freeze check is inconsistent"
        ):
            canary.verify_evidence_document(
                evidence,
                **common,
                expected_prompt_protocol=self.expected_prompt_protocol(),
                expected_execution_components=stale_components,
            )

        freeze_path = self.artifact_root / evidence["artifacts"]["freeze_check"]["path"]
        freeze_path.write_bytes(freeze_path.read_bytes() + b" ")
        with self.assertRaisesRegex(BenchmarkToolError, "failed authentication"):
            canary.verify_evidence_document(
                evidence,
                **common,
                expected_prompt_protocol=self.expected_prompt_protocol(),
                expected_execution_components=self.expected_execution_components(),
            )

    def test_verify_only_forwards_current_production_freeze(self) -> None:
        evidence_path = self.project / "verify-only.json"
        write_json(evidence_path, {"kind": "fixture"})
        freeze = {
            "benchmark_id": "fixture-benchmark",
            "agent": self.expected_agent(),
            "prompt_protocol": self.expected_prompt_protocol(),
            "execution_components": self.expected_execution_components(),
        }
        args = argparse.Namespace(
            benchmark_root=self.benchmark_root,
            project_root=self.project,
            verify_only=evidence_path,
            token_limit=10_000,
        )
        with mock.patch.object(
            run_matrix, "verify_frozen_run_environment", return_value=freeze
        ), mock.patch.object(
            canary,
            "verify_evidence_document",
            return_value={"status": "passed"},
        ) as verifier:
            self.assertEqual(canary._verify_only(args), 0)
        self.assertEqual(
            verifier.call_args.kwargs["expected_prompt_protocol"],
            self.expected_prompt_protocol(),
        )
        self.assertEqual(
            verifier.call_args.kwargs["expected_execution_components"],
            self.expected_execution_components(),
        )
    def test_root_only_tree_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "exactly one allowed child"):
            self.evidence_fixture(child_count=0)

    def test_post_boundary_raw_activity_is_rejected_but_shutdown_status_is_allowed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        # The fixture already contains a harmless root shutdown status and passes.
        validate_usage_fixture(usage, log, token_limit=10_000)
        with log.open("a", encoding="utf-8") as stream:
            stream.write(
                json.dumps(
                    raw_event("late-response", "root", "root-turn", 1, 1),
                    sort_keys=True,
                )
                + "\n"
            )
        with self.assertRaisesRegex(BenchmarkToolError, "post-boundary model activity"):
            validate_usage_fixture(usage, log, token_limit=10_000)

    def test_outer_exec_progress_output_is_forbidden(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        with log.open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(outer_exec_progress_output(), sort_keys=True) + "\n")
        with self.assertRaisesRegex(BenchmarkToolError, "post-boundary model activity"):
            validate_usage_fixture(usage, log, token_limit=10_000)

    def test_old_schema_transport_and_yield_tamper_fail_closed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        for changes in (
            {"schema_version": 3},
            {"submission_transport": "functions_exec_dynamic_submit_proof_v1"},
            {"outer_exec_yield_time_ms": 10_000},
            {"outer_exec_yield_margin_ms": 0},
            {"outer_exec_timer_starts_at_or_after_prompt_release": False},
        ):
            with self.subTest(changes=changes):
                malformed = json.loads(json.dumps(usage))
                malformed["submission_boundary"].update(changes)
                with self.assertRaises(BenchmarkToolError):
                    validate_usage_fixture(
                        malformed, log, token_limit=10_000
                    )

    def test_factual_dynamic_call_order_fails_closed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        usage = json.loads(json.dumps(usage))
        usage["submission_boundary"][
            "dynamic_call_observed_before_raw_response_completed"
        ] = False
        with self.assertRaisesRegex(BenchmarkToolError, "event order"):
            validate_usage_fixture(usage, log, token_limit=10_000)

    def test_schema_v5_event_order_enum_xor_and_timestamps_fail_closed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        for changes in (
            {"submission_event_order": "invalid-order"},
            {"raw_response_completed_before_dynamic_call_observed": True},
            {
                "dynamic_call_observed_before_raw_response_completed": False,
                "raw_response_completed_before_dynamic_call_observed": False,
            },
        ):
            malformed = json.loads(json.dumps(usage))
            malformed["submission_boundary"].update(changes)
            with self.assertRaisesRegex(BenchmarkToolError, "event.order"):
                validate_usage_fixture(malformed, log, token_limit=10_000)

        request_path = self.artifact_root / "request.json"
        request = json.loads(request_path.read_text(encoding="utf-8"))
        request["captured_at_monotonic_ns"] = request[
            "raw_response_observed_at_monotonic_ns"
        ] + 1
        with self.assertRaisesRegex(BenchmarkToolError, "timestamps"):
            canary._validated_submission_event_order(
                request,
                label="tampered request",
                derive_from_timestamps=True,
            )

    def test_spawn_call_activity_identity_mismatch_fails_closed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        messages = [json.loads(line) for line in log.read_text().splitlines()]
        activity = next(
            message
            for message in messages
            if isinstance(message.get("params", {}).get("item"), dict)
            and message["params"]["item"].get("type") == "subAgentActivity"
        )
        activity["params"]["item"]["id"] = "different-spawn-call"
        log.write_text(
            "".join(json.dumps(message, sort_keys=True) + "\n" for message in messages),
            encoding="utf-8",
        )
        with self.assertRaises(BenchmarkToolError):
            validate_usage_fixture(usage, log, token_limit=10_000)

    def test_hook_lifecycle_tampering_fails_closed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        original_messages = [
            json.loads(line) for line in log.read_text().splitlines()
        ]
        for mutation in ("missing_completed", "duplicate_started", "wrong_feedback"):
            with self.subTest(mutation=mutation):
                messages = json.loads(json.dumps(original_messages))
                matching = [
                    (index, message)
                    for index, message in enumerate(messages)
                    if message.get("method")
                    in (
                        codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                        codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                    )
                    and str(message.get("params", {}).get("run", {}).get("id", ""))
                    .endswith(":call_blocked_root")
                ]
                if mutation == "missing_completed":
                    index = next(
                        index
                        for index, message in matching
                        if message["method"]
                        == codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION
                    )
                    messages.pop(index)
                elif mutation == "duplicate_started":
                    index, message = next(
                        pair
                        for pair in matching
                        if pair[1]["method"]
                        == codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION
                    )
                    messages.insert(index + 1, json.loads(json.dumps(message)))
                else:
                    _index, message = next(
                        pair
                        for pair in matching
                        if pair[1]["method"]
                        == codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION
                    )
                    message["params"]["run"]["entries"][0]["text"] = "tampered"
                log.write_text(
                    "".join(
                        json.dumps(message, sort_keys=True) + "\n"
                        for message in messages
                    ),
                    encoding="utf-8",
                )
                with self.assertRaises(BenchmarkToolError):
                    validate_usage_fixture(usage, log, token_limit=10_000)

    def test_policy_blocked_call_cannot_create_a_child(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        messages = [json.loads(line) for line in log.read_text().splitlines()]
        blocked_activity = child_started(
            "root", "root-turn", "forbidden-child", "call_blocked_root"
        )
        insertion = next(
            index
            for index, message in enumerate(messages)
            if message.get("method")
            == codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION
            and str(message.get("params", {}).get("run", {}).get("id", ""))
            .endswith(":call_blocked_root")
        )
        messages.insert(insertion + 1, blocked_activity)
        log.write_text(
            "".join(
                json.dumps(message, sort_keys=True) + "\n" for message in messages
            ),
            encoding="utf-8",
        )
        with self.assertRaises(BenchmarkToolError):
            validate_usage_fixture(usage, log, token_limit=10_000)

    def test_normalized_projection_tampering_fails_closed(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        normalized = runner._read_ultra_token_usage(usage)
        normalized["accounting_complete"] = False
        with self.assertRaisesRegex(BenchmarkToolError, "normalization disagrees"):
            validate_usage_fixture(
                usage,
                log,
                token_limit=10_000,
                normalized_usage=normalized,
            )

    def test_validation_authentication_binding_fails_closed(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        validation_path = self.artifact_root / "validation.json"
        validation = json.loads(validation_path.read_text(encoding="utf-8"))
        validation["authentication"]["candidate_sha256"] = "f" * 64
        unsigned = dict(validation)
        unsigned.pop("record_sha256")
        validation["record_sha256"] = canary._canonical_sha256(unsigned)
        write_json(validation_path, validation)

        runner_path = self.artifact_root / "runner-record.json"
        runner_record = json.loads(runner_path.read_text(encoding="utf-8"))
        runner_record["validation_log_sha256"] = sha256_file(validation_path)
        runner_record["validation_record_sha256"] = validation["record_sha256"]
        write_json(runner_path, runner_record)
        raw_path = self.artifact_root / "runner-record.jsonl"
        raw_path.write_text(
            json.dumps(runner_record, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )
        for label, path in (
            ("validation", validation_path),
            ("runner_record", runner_path),
            ("raw_jsonl", raw_path),
        ):
            evidence["artifacts"][label]["sha256"] = sha256_file(path)
        with self.assertRaisesRegex(
            BenchmarkToolError, "validation authentication bindings disagree"
        ):
            canary.verify_evidence_document(
                evidence,
                project_root=self.project,
                expected_benchmark_id="fixture-benchmark",
                expected_agent=self.expected_agent(),
                expected_token_limit=10_000,
                expected_prompt_protocol=self.expected_prompt_protocol(),
                expected_execution_components=self.expected_execution_components(),
            )

    def test_duplicate_raw_notification_is_counted_but_not_double_charged(self) -> None:
        _evidence, usage, log = self.evidence_fixture()
        lines = log.read_text(encoding="utf-8").splitlines()
        lines.insert(
            -1,
            json.dumps(
                raw_event(
                    "root-submit-response", "root", "root-turn", 60, 4
                ),
                sort_keys=True,
            ),
        )
        log.write_text("\n".join(lines) + "\n", encoding="utf-8")
        outcome = validate_usage_fixture(usage, log, token_limit=10_000)
        self.assertEqual(
            outcome["unique_raw_response_count_in_audit_log"],
            outcome["response_count"],
        )
        self.assertEqual(
            outcome["notification_count_in_audit_log"],
            outcome["response_count"] + 1,
        )

    def test_runner_invocation_parses_as_production_runner_command(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        invocation = json.loads(
            (self.artifact_root / evidence["artifacts"]["invocation"]["path"])
            .read_text(encoding="utf-8")
        )
        parsed = runner.make_parser().parse_args(invocation["argv"][2:])
        self.assertEqual(parsed.task_id, canary.CANARY_ID)
        self.assertTrue(parsed.reject_workspace_local_module_imports)
        self.assertIsNotNone(parsed.audit_command_json)
        agent_command = runner.parse_command_json(
            parsed.agent_command_json, option="--agent-command-json"
        )
        self.assertIsNotNone(agent_command)
        self.assertEqual(
            canary._option_value(agent_command, "--shared-root-relative"),
            "task/shared",
        )
        self.assertEqual(
            Path(parsed.audit_helper).resolve(),
            (self.benchmark_root / "tools" / "dependency_audit.lean").resolve(),
        )

    def test_dependency_audit_tampering_fails_closed(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        validation_path = self.artifact_root / "validation.json"
        validation = json.loads(validation_path.read_text(encoding="utf-8"))
        validation["library_audit_complete"] = False
        unsigned = dict(validation)
        unsigned.pop("record_sha256")
        validation["record_sha256"] = canary._canonical_sha256(unsigned)
        write_json(validation_path, validation)

        runner_path = self.artifact_root / "runner-record.json"
        runner_record = json.loads(runner_path.read_text(encoding="utf-8"))
        runner_record["validation_log_sha256"] = sha256_file(validation_path)
        runner_record["validation_record_sha256"] = validation["record_sha256"]
        write_json(runner_path, runner_record)
        raw_path = self.artifact_root / "runner-record.jsonl"
        raw_path.write_text(
            json.dumps(runner_record, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )
        for label, path in (
            ("validation", validation_path),
            ("runner_record", runner_path),
            ("raw_jsonl", raw_path),
        ):
            evidence["artifacts"][label]["sha256"] = sha256_file(path)
        with self.assertRaisesRegex(
            BenchmarkToolError, "production runner record is invalid"
        ):
            canary.verify_evidence_document(
                evidence,
                project_root=self.project,
                expected_benchmark_id="fixture-benchmark",
                expected_agent=self.expected_agent(),
                expected_token_limit=10_000,
                expected_prompt_protocol=self.expected_prompt_protocol(),
                expected_execution_components=self.expected_execution_components(),
            )

    def test_dependency_audit_system_error_must_be_explicit_null(self) -> None:
        base_evidence, _usage, _log = self.evidence_fixture()
        validation_path = self.artifact_root / "validation.json"
        base_validation = json.loads(validation_path.read_text(encoding="utf-8"))
        runner_path = self.artifact_root / "runner-record.json"
        base_runner_record = json.loads(runner_path.read_text(encoding="utf-8"))
        raw_path = self.artifact_root / "runner-record.jsonl"
        for replacement in (False, "unexpected system error", "missing"):
            with self.subTest(replacement=replacement):
                evidence = json.loads(json.dumps(base_evidence))
                validation = json.loads(json.dumps(base_validation))
                dependency_audit = validation["dependency_audit"]
                if replacement == "missing":
                    dependency_audit.pop("system_error")
                else:
                    dependency_audit["system_error"] = replacement
                unsigned = dict(validation)
                unsigned.pop("record_sha256")
                validation["record_sha256"] = canary._canonical_sha256(unsigned)
                write_json(validation_path, validation)

                runner_record = json.loads(json.dumps(base_runner_record))
                runner_record["validation_log_sha256"] = sha256_file(validation_path)
                runner_record["validation_record_sha256"] = validation["record_sha256"]
                write_json(runner_path, runner_record)
                raw_path.write_text(
                    json.dumps(runner_record, sort_keys=True, separators=(",", ":"))
                    + "\n",
                    encoding="utf-8",
                )
                for label, path in (
                    ("validation", validation_path),
                    ("runner_record", runner_path),
                    ("raw_jsonl", raw_path),
                ):
                    evidence["artifacts"][label]["sha256"] = sha256_file(path)
                with self.assertRaisesRegex(
                    BenchmarkToolError, "production runner record is invalid"
                ):
                    canary.verify_evidence_document(
                        evidence,
                        project_root=self.project,
                        expected_benchmark_id="fixture-benchmark",
                        expected_agent=self.expected_agent(),
                        expected_token_limit=10_000,
                        expected_prompt_protocol=self.expected_prompt_protocol(),
                        expected_execution_components=(
                            self.expected_execution_components()
                        ),
                    )

    def test_ultra_canary_requires_strict_clean_adapter_exit(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        runner_path = self.artifact_root / "runner-record.json"
        raw_path = self.artifact_root / "runner-record.jsonl"
        original_runner_record = json.loads(
            runner_path.read_text(encoding="utf-8")
        )
        for invalid_exit in (2, False, 0.0, None):
            with self.subTest(agent_exit_code=invalid_exit):
                runner_record = json.loads(json.dumps(original_runner_record))
                runner_record["agent_exit_code"] = invalid_exit
                write_json(runner_path, runner_record)
                raw_path.write_text(
                    json.dumps(
                        runner_record,
                        sort_keys=True,
                        separators=(",", ":"),
                    )
                    + "\n",
                    encoding="utf-8",
                )
                evidence["artifacts"]["runner_record"]["sha256"] = sha256_file(
                    runner_path
                )
                evidence["artifacts"]["raw_jsonl"]["sha256"] = sha256_file(
                    raw_path
                )
                with self.assertRaisesRegex(
                    BenchmarkToolError, "production runner record is invalid"
                ):
                    canary.verify_evidence_document(
                        evidence,
                        project_root=self.project,
                        expected_benchmark_id="fixture-benchmark",
                        expected_agent=self.expected_agent(),
                        expected_token_limit=10_000,
                        expected_prompt_protocol=self.expected_prompt_protocol(),
                        expected_execution_components=(
                            self.expected_execution_components()
                        ),
                    )

    def test_log_replay_and_artifact_hashes_fail_closed(self) -> None:
        evidence, _usage, _log = self.evidence_fixture()
        evidence_path = self.project / canary.FROZEN_EVIDENCE_PATH
        evidence_path.parent.mkdir(parents=True)
        write_json(evidence_path, evidence)
        descriptor = {
            "path": canary.FROZEN_EVIDENCE_PATH,
            "sha256": sha256_file(evidence_path),
            "status": "passed",
        }
        summary = canary.verify_frozen_attestation(
            self.project,
            descriptor,
            expected_benchmark_id="fixture-benchmark",
            expected_agent=self.expected_agent(),
            expected_token_limit=10_000,
            expected_prompt_protocol=self.expected_prompt_protocol(),
            expected_execution_components=self.expected_execution_components(),
        )
        self.assertEqual(summary["sha256"], descriptor["sha256"])

        (self.artifact_root / "agent.log").write_text("{}\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "failed authentication"):
            canary.verify_frozen_attestation(
                self.project,
                descriptor,
                expected_benchmark_id="fixture-benchmark",
                expected_agent=self.expected_agent(),
                expected_token_limit=10_000,
                expected_prompt_protocol=self.expected_prompt_protocol(),
                expected_execution_components=self.expected_execution_components(),
            )


if __name__ == "__main__":
    unittest.main()
