from __future__ import annotations

import argparse
import copy
import contextlib
import hashlib
import http.client
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import io
import json
import os
from pathlib import Path
import platform
import queue
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import codex_isolated  # noqa: E402
import provider_token_gate  # noqa: E402
import runner as benchmark_runner  # noqa: E402
from codex_isolated import (  # noqa: E402
    AttemptUsageLedger,
    NETWORK_VIOLATION_MARKER_ENV,
    TOKEN_USAGE_MEASUREMENT_SOURCE,
    bubblewrap_command,
    build_prompt,
    normalized_usage,
    positive_int,
    run as run_codex_isolated,
    validated_condition_prompt,
)
from lean_isolated import namespace_prefix  # noqa: E402


def mounts(command: list[str]) -> list[tuple[str, str, str, int]]:
    result: list[tuple[str, str, str, int]] = []
    for index, item in enumerate(command):
        if item in ("--bind", "--ro-bind"):
            result.append((item, command[index + 1], command[index + 2], index))
    return result


def setenv_value(command: list[str], name: str) -> str:
    for index, item in enumerate(command):
        if item == "--setenv" and command[index + 1] == name:
            return command[index + 2]
    raise AssertionError(f"missing --setenv {name}")


def raw_response_event(
    response_id: str,
    thread_id: str,
    turn_id: str,
    *,
    input_tokens: int,
    cached_input_tokens: int,
    output_tokens: int,
    reasoning_output_tokens: int = 0,
    cache_write_input_tokens: int = 0,
) -> dict[str, object]:
    return {
        "method": "rawResponse/completed",
        "params": {
            "responseId": response_id,
            "threadId": thread_id,
            "turnId": turn_id,
            "usage": {
                "inputTokens": input_tokens,
                "cachedInputTokens": cached_input_tokens,
                "cacheWriteInputTokens": cache_write_input_tokens,
                "outputTokens": output_tokens,
                "reasoningOutputTokens": reasoning_output_tokens,
                "totalTokens": input_tokens + output_tokens,
            },
        },
    }


def cumulative_usage_event(
    thread_id: str,
    turn_id: str,
    *,
    input_tokens: int,
    cached_input_tokens: int,
    output_tokens: int,
    reasoning_output_tokens: int = 0,
    cache_write_input_tokens: int = 0,
) -> dict[str, object]:
    total = {
        "inputTokens": input_tokens,
        "cachedInputTokens": cached_input_tokens,
        "cacheWriteInputTokens": cache_write_input_tokens,
        "outputTokens": output_tokens,
        "reasoningOutputTokens": reasoning_output_tokens,
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


def turn_event(
    method: str,
    thread_id: str,
    turn_id: str,
    status: str,
) -> dict[str, object]:
    return {
        "method": method,
        "params": {
            "threadId": thread_id,
            "turn": {"id": turn_id, "status": status},
        },
    }


def subagent_started_event(
    parent_thread_id: str,
    child_thread_id: str,
    agent_path: str = "root/worker",
    *,
    parent_turn_id: str = "parent-turn",
    activity_id: str | None = None,
) -> dict[str, object]:
    return {
        "method": "item/completed",
        "params": {
            "threadId": parent_thread_id,
            "turnId": parent_turn_id,
            "item": {
                "type": "subAgentActivity",
                "kind": "started",
                "id": activity_id or f"activity-{parent_thread_id}-{child_thread_id}",
                "agentThreadId": child_thread_id,
                "agentPath": agent_path,
            },
        },
    }


def raw_function_call_event(
    parent_thread_id: str,
    parent_turn_id: str,
    call_id: str,
    *,
    fork_turns: str | None = None,
    name: str = "spawn_agent",
    namespace: str | None = "collaboration",
) -> dict[str, object]:
    arguments: dict[str, object] = {
        "task_name": f"task-{call_id}",
        "message": "bounded unit-test task",
    }
    if fork_turns is not None:
        arguments["fork_turns"] = fork_turns
    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": parent_thread_id,
            "turnId": parent_turn_id,
            "item": {
                "type": "function_call",
                "id": f"fc-{call_id}",
                "name": name,
                "namespace": namespace,
                "arguments": json.dumps(arguments),
                "call_id": call_id,
            },
        },
    }


def function_call_output_event(
    parent_thread_id: str,
    parent_turn_id: str,
    call_id: str,
    output: object,
    *,
    item_id: str | None = None,
) -> dict[str, object]:
    return {
        "method": "rawResponseItem/completed",
        "params": {
            "threadId": parent_thread_id,
            "turnId": parent_turn_id,
            "item": {
                "type": "function_call_output",
                "id": item_id or f"fco-{call_id}",
                "call_id": call_id,
                "output": output,
                "internal_chat_message_metadata_passthrough": {
                    "turn_id": parent_turn_id
                },
            },
        },
    }


def collab_spawn_event(
    parent_thread_id: str,
    parent_turn_id: str,
    call_id: str,
    child_thread_id: str | None,
    *,
    method: str = "item/completed",
    status: str = "completed",
) -> dict[str, object]:
    return {
        "method": method,
        "params": {
            "threadId": parent_thread_id,
            "turnId": parent_turn_id,
            "item": {
                "type": "collabAgentToolCall",
                "id": call_id,
                "tool": "spawnAgent",
                "senderThreadId": parent_thread_id,
                "receiverThreadIds": (
                    [] if child_thread_id is None else [child_thread_id]
                ),
                "agentsStates": {},
                "status": status,
            },
        },
    }


def fork_policy_hook_event(
    method: str,
    call_id: str,
    thread_id: str,
    turn_id: str,
    *,
    inside_home: str = "/u501/tester",
    decision: str = "allow",
    source_path: str | None = None,
    run_id: str | None = None,
    status: str | None = None,
    entries: list[dict[str, str]] | None = None,
) -> dict[str, object]:
    policy = codex_isolated.ultra_fork_policy_static_record(inside_home)
    source = source_path or str(policy["source_path"])
    identifier = run_id or f"pre-tool-use:0:{source}:{call_id}"
    started = method == codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION
    if status is None:
        status = (
            "running"
            if started
            else (
                codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
                if decision == codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
                else codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
            )
        )
    if entries is None:
        entries = []
        if not started and decision == codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION:
            entries = [
                {
                    "kind": "feedback",
                    "text": codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                        call_id=call_id
                    ),
                }
            ]
    return {
        "method": method,
        "params": {
            "threadId": thread_id,
            "turnId": turn_id,
            "run": {
                "id": identifier,
                "eventName": codex_isolated.ULTRA_FORK_POLICY_HOOK_EVENT_NAME,
                "executionMode": codex_isolated.ULTRA_FORK_POLICY_EXECUTION_MODE,
                "handlerType": codex_isolated.ULTRA_FORK_POLICY_HANDLER_TYPE,
                "scope": codex_isolated.ULTRA_FORK_POLICY_SCOPE,
                "source": codex_isolated.ULTRA_FORK_POLICY_SOURCE,
                "sourcePath": source,
                "displayOrder": codex_isolated.ULTRA_FORK_POLICY_DISPLAY_ORDER,
                "statusMessage": None,
                "status": status,
                "entries": entries,
                "startedAt": 100,
                "completedAt": None if started else 101,
                "durationMs": None if started else 1,
            },
        },
    }


class AttemptUsageLedgerTests(unittest.TestCase):
    def test_terminal_turn_history_survives_child_reactivation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread"
            )
            ledger._link_child(
                "root-thread", "child-thread", "/root/library_search"
            )

            ledger.observe(
                turn_event(
                    "turn/started",
                    "child-thread",
                    "interrupted-turn",
                    "inProgress",
                )
            )
            interrupted = turn_event(
                "turn/completed",
                "child-thread",
                "interrupted-turn",
                "interrupted",
            )
            interrupted["emittedAtMs"] = int(time.time() * 1_000) - 1
            ledger.observe(interrupted)
            first_lifecycle = copy.deepcopy(
                ledger.terminal_turn_lifecycles[
                    ("child-thread", "interrupted-turn")
                ]
            )

            ledger.observe(
                turn_event(
                    "turn/started",
                    "child-thread",
                    "reactivated-turn",
                    "inProgress",
                )
            )
            self.assertEqual(
                ledger.threads["child-thread"]["active_turn_id"],
                "reactivated-turn",
            )
            self.assertEqual(
                ledger.threads["child-thread"]["turn_status"], "inProgress"
            )
            self.assertEqual(
                ledger.terminal_turn_lifecycles[
                    ("child-thread", "interrupted-turn")
                ],
                first_lifecycle,
            )

            completed = turn_event(
                "turn/completed",
                "child-thread",
                "reactivated-turn",
                "completed",
            )
            completed["emittedAtMs"] = int(time.time() * 1_000) - 1
            ledger.observe(completed)
            self.assertEqual(
                ledger.terminal_turn_lifecycles[
                    ("child-thread", "interrupted-turn")
                ],
                first_lifecycle,
            )
            self.assertEqual(
                ledger.terminal_turn_lifecycles[
                    ("child-thread", "reactivated-turn")
                ]["status"],
                "completed",
            )

    def test_job_1509738_thread_limit_spawn_failure_is_terminal_without_child(
        self,
    ) -> None:
        """Replay the exact failed-spawn lifecycle from P01-T1 rep-02 L."""

        with tempfile.TemporaryDirectory() as directory:
            policy = codex_isolated.ultra_fork_policy_static_record("/u501/tester")
            ledger = AttemptUsageLedger(
                Path(directory) / "usage.json",
                5_000_000,
                "root",
                fork_policy=policy,
            )
            call_id = "call_elPNO7NKs0u2obahg4hTd0jZ"
            ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
            ledger.observe(
                raw_function_call_event(
                    "root", "root-turn", call_id, fork_turns="all"
                )
            )
            ledger.observe(
                raw_response_event(
                    "response-spawn",
                    "root",
                    "root-turn",
                    input_tokens=13_354,
                    cached_input_tokens=12_032,
                    output_tokens=135,
                    reasoning_output_tokens=59,
                )
            )
            ledger.observe(
                fork_policy_hook_event(
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                    call_id,
                    "root",
                    "root-turn",
                )
            )
            ledger.observe(
                fork_policy_hook_event(
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                    call_id,
                    "root",
                    "root-turn",
                )
            )
            ledger.observe(
                function_call_output_event(
                    "root",
                    "root-turn",
                    call_id,
                    codex_isolated.ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_OUTPUT,
                    item_id="fco_019ff940-650f-7342-a2a1-e0a8a91f0c10",
                )
            )
            ledger.observe(
                cumulative_usage_event(
                    "root",
                    "root-turn",
                    input_tokens=13_354,
                    cached_input_tokens=12_032,
                    output_tokens=135,
                    reasoning_output_tokens=59,
                )
            )
            ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))

            snapshot = ledger.snapshot(drain_complete=ledger.quiescent())
            self.assertEqual(snapshot["failed_spawn_call_ids"], [call_id])
            self.assertEqual(snapshot["unresolved_spawn_call_ids"], [])
            self.assertEqual(snapshot["activity_spawn_call_ids"], [])
            self.assertEqual(snapshot["inference_child_thread_ids"], [])
            self.assertTrue(snapshot["fork_policy_complete"], snapshot)
            self.assertTrue(snapshot["spawn_linkage_complete"], snapshot)
            self.assertTrue(snapshot["measurement_exact"], snapshot)
            self.assertEqual(
                ledger.canonical_spawn_failures[call_id]["failure_kind"],
                codex_isolated.ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_KIND,
            )

    def test_thread_limit_spawn_failure_classification_is_fail_closed(self) -> None:
        def staged(name: str) -> tuple[AttemptUsageLedger, str]:
            policy = codex_isolated.ultra_fork_policy_static_record("/u501/tester")
            ledger = AttemptUsageLedger(
                Path(directory) / f"{name}.json",
                5_000_000,
                "root",
                fork_policy=policy,
            )
            call_id = f"call_{name}"
            ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
            ledger.observe(
                raw_function_call_event(
                    "root", "root-turn", call_id, fork_turns="all"
                )
            )
            ledger.observe(
                raw_response_event(
                    f"response-{name}",
                    "root",
                    "root-turn",
                    input_tokens=2,
                    cached_input_tokens=0,
                    output_tokens=1,
                )
            )
            for method in (
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
            ):
                ledger.observe(
                    fork_policy_hook_event(method, call_id, "root", "root-turn")
                )
            return ledger, call_id

        with tempfile.TemporaryDirectory() as directory:
            lookalike, lookalike_call = staged("lookalike")
            lookalike.observe(
                function_call_output_event(
                    "root",
                    "root-turn",
                    lookalike_call,
                    "collab spawn failed: agent thread limit reached.",
                )
            )
            lookalike_snapshot = lookalike.snapshot()
            self.assertEqual(lookalike_snapshot["failed_spawn_call_ids"], [])
            self.assertEqual(
                lookalike_snapshot["unresolved_spawn_call_ids"], [lookalike_call]
            )
            self.assertFalse(lookalike_snapshot["spawn_linkage_complete"])

            contradictory, contradictory_call = staged("contradictory")
            contradictory.observe(
                function_call_output_event(
                    "root",
                    "root-turn",
                    contradictory_call,
                    codex_isolated.ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_OUTPUT,
                )
            )
            contradictory.observe(
                subagent_started_event(
                    "root",
                    "child",
                    parent_turn_id="root-turn",
                    activity_id=contradictory_call,
                )
            )
            contradictory_snapshot = contradictory.snapshot()
            self.assertEqual(contradictory_snapshot["failed_spawn_call_ids"], [])
            self.assertIn(
                contradictory_call,
                contradictory_snapshot["unresolved_spawn_call_ids"],
            )
            self.assertFalse(contradictory_snapshot["spawn_linkage_complete"])
            self.assertTrue(
                any(
                    "contradictory child activity" in reason
                    for reason in contradictory_snapshot["invalid_reasons"]
                )
            )

    @staticmethod
    def _rep03_l_empty_final_answer_ledger(
        directory: str,
    ) -> tuple[AttemptUsageLedger, dict[str, object]]:
        root_thread_id = "019ff85d-5cc9-7f11-aa82-1eb77a320826"
        root_turn_id = "019ff85d-5cf1-7a53-9c0d-ab628b1538ff"
        child_thread_id = "019ff85d-7903-7cd0-9a69-0f3c7246da56"
        ledger = AttemptUsageLedger(
            Path(directory) / "usage.json", 5_000_000, root_thread_id
        )
        ledger.root_turn_id = root_turn_id
        ledger._link_child(
            root_thread_id,
            child_thread_id,
            "/root/library_search",
        )
        ledger.threads[child_thread_id].update(
            {"provisional": False, "spawn_binding_status": "resolved"}
        )
        item: dict[str, object] = {
            "type": "agent_message",
            "id": "amsg_019ff85d-a818-7651-afb6-dc9384881946",
            "author": "/root/library_search",
            "recipient": "/root",
            "content": [
                {
                    "type": "input_text",
                    "text": (
                        "Message Type: FINAL_ANSWER\n"
                        "Task name: /root\n"
                        "Sender: /root/library_search\n"
                        "Payload:\n"
                    ),
                }
            ],
            "internal_chat_message_metadata_passthrough": {
                "turn_id": root_turn_id
            },
        }
        return ledger, item

    def test_job_1509551_rep03_l_empty_final_answer_is_validated_noop(
        self,
    ) -> None:
        """Replay the exact empty child result observed in P01 rep-03 L."""

        with tempfile.TemporaryDirectory() as directory:
            ledger, item = self._rep03_l_empty_final_answer_ledger(directory)
            event = {
                "method": "rawResponseItem/completed",
                "params": {
                    "threadId": ledger.root_thread_id,
                    "turnId": ledger.root_turn_id,
                    "item": item,
                },
                "emittedAtMs": 1_786_578_315_290,
            }
            with mock.patch.object(
                codex_isolated.time,
                "time_ns",
                return_value=1_786_578_315_300_000_000,
            ), mock.patch.object(
                codex_isolated.time,
                "monotonic_ns",
                return_value=2_534_079_584_900_000,
            ):
                self.assertFalse(ledger.observe(event))

            # The item remains in the raw transcript audit trail, but an empty
            # payload cannot explain a suppressed wait or provider response.
            self.assertIn(str(item["id"]), ledger.raw_item_observations)
            self.assertEqual(ledger.final_answer_agent_messages, {})
            self.assertEqual(ledger.collaboration_message_observations, {})

    def test_empty_final_answer_hardening_remains_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            _, exact = self._rep03_l_empty_final_answer_ledger(directory)

        empty_message = copy.deepcopy(exact)
        empty_message["content"][0]["text"] = (  # type: ignore[index]
            "Message Type: MESSAGE\n"
            "Task name: /root\n"
            "Sender: /root/library_search\n"
            "Payload:\n"
        )
        whitespace_payload = copy.deepcopy(exact)
        whitespace_payload["content"][0]["text"] += " "  # type: ignore[index,operator]
        extra_content = copy.deepcopy(exact)
        extra_content["content"].append(  # type: ignore[union-attr]
            {"type": "input_text", "text": "unexpected"}
        )
        wrong_turn = copy.deepcopy(exact)
        wrong_turn["internal_chat_message_metadata_passthrough"][  # type: ignore[index]
            "turn_id"
        ] = "wrong-turn"
        wrong_root_turn = copy.deepcopy(exact)
        wrong_root_turn[
            "internal_chat_message_metadata_passthrough"
        ]["turn_id"] = "wrong-root-turn"  # type: ignore[index]
        wrong_route = copy.deepcopy(exact)
        wrong_route["author"] = "/root/unrelated"

        malformed = {
            "empty MESSAGE": (empty_message, "not canonical"),
            "whitespace payload": (whitespace_payload, "not canonical"),
            "extra content": (extra_content, "not canonical"),
            "wrong turn": (wrong_turn, "mismatched turn metadata"),
            "wrong route": (wrong_route, "not routed within the resolved tree"),
        }
        methods = (
            "_capture_final_answer_agent_message",
            "_capture_collaboration_message",
        )
        for method_name in methods:
            for label, (item, error) in malformed.items():
                with self.subTest(method=method_name, case=label):
                    with tempfile.TemporaryDirectory() as directory:
                        ledger, _ = self._rep03_l_empty_final_answer_ledger(directory)
                        capture = getattr(ledger, method_name)
                        with self.assertRaisesRegex(RuntimeError, error):
                            capture(
                                thread_id=ledger.root_thread_id,
                                turn_id=str(ledger.root_turn_id),
                                item=item,
                                observed_at_unix_ns=1_786_578_315_290_000_000,
                                observed_at_monotonic_ns=2_534_079_584_800_000,
                            )

        for method_name in methods:
            with self.subTest(method=method_name, case="wrong root turn"):
                with tempfile.TemporaryDirectory() as directory:
                    ledger, _ = self._rep03_l_empty_final_answer_ledger(directory)
                    capture = getattr(ledger, method_name)
                    with self.assertRaisesRegex(RuntimeError, "not canonical"):
                        capture(
                            thread_id=ledger.root_thread_id,
                            turn_id="wrong-root-turn",
                            item=wrong_root_turn,
                            observed_at_unix_ns=1_786_578_315_290_000_000,
                            observed_at_monotonic_ns=2_534_079_584_800_000,
                        )

    def test_job_1509446_interacted_subagent_activity_is_validated_and_ignored(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread"
            )
            event = {
                "method": "item/completed",
                "params": {
                    "threadId": "019ff82b-4381-7853-aaff-9d118f013895",
                    "turnId": "019ff82b-439e-7531-aba5-c1b0d3d20f8c",
                    "item": {
                        "type": "subAgentActivity",
                        "id": "call_Zqtz95W2GNhGyUZtP6CUbMxZ",
                        "kind": "interacted",
                        "agentThreadId": "019ff82b-1898-7023-b037-c54db328ab90",
                        "agentPath": "/root",
                    },
                },
                "emittedAtMs": 1_786_575_391_797,
            }

            self.assertFalse(ledger.observe(event))
            self.assertEqual(ledger.subagent_activities, {})
            self.assertEqual(ledger.subagent_interrupt_activities, {})
            self.assertEqual(set(ledger.threads), {"root-thread"})

            malformed = copy.deepcopy(event)
            malformed["params"]["item"]["agentPath"] = ""
            with self.assertRaisesRegex(RuntimeError, "malformed subagent activity"):
                ledger.observe(malformed)

            unknown = copy.deepcopy(event)
            unknown["params"]["item"]["kind"] = "unknown"
            with self.assertRaisesRegex(RuntimeError, "malformed subagent activity"):
                ledger.observe(unknown)

    def test_job_1509405_explicit_child_interrupt_reconciles_discarded_reply(
        self,
    ) -> None:
        arguments = '{"target":"/root/lemma_search"}'
        candidate = {
            "response_id": "resp-discarded",
            "call_id": "provider-call-00000068",
            "thread_id": "child-thread",
            "turn_id": "child-turn",
            "normalized_usage": {
                "input_tokens": 49_980,
                "cached_input_tokens": 48_896,
                "cache_write_input_tokens": 0,
                "output_tokens": 338,
                "reasoning_output_tokens": 69,
                "total_tokens": 50_318,
            },
            # The child request was already in flight when the parent response
            # delivered its interrupt function call.
            "admitted_unix_ns": 1_500_000,
            "admitted_monotonic_ns": 1_500,
            "commit_unix_ns": 12_000_000,
            "commit_monotonic_ns": 12_000,
            "action_capable_item_count": 0,
            "response_output_manifest_sha256": "a" * 64,
            "interrupting_response_id": "resp-interrupt",
            "interrupting_call_id": "provider-call-00000067",
            "interrupt_parent_thread_id": "root-thread",
            "interrupt_parent_turn_id": "root-turn",
            "interrupt_admitted_unix_ns": 1_000_000,
            "interrupt_admitted_monotonic_ns": 1_000,
            "interrupt_commit_unix_ns": 2_000_000,
            "interrupt_commit_monotonic_ns": 2_000,
            "interrupt_bind_unix_ns": 2_500_000,
            "interrupt_bind_monotonic_ns": 2_500,
            "interrupt_function_item_id": "fc-interrupt",
            "interrupt_function_call_id": "call-interrupt",
            "interrupt_function_arguments_sha256": hashlib.sha256(
                arguments.encode("utf-8")
            ).hexdigest(),
            "interrupt_function_arguments_bytes": len(arguments),
            "interrupt_response_output_manifest_sha256": "b" * 64,
        }

        class FakeGate:
            def discarded_after_explicit_child_interrupt_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                return [copy.deepcopy(candidate)]

            def crossbind_discarded_after_explicit_child_interrupt(
                self, response_id: str, thread_id: str, turn_id: str,
                interrupting_response_id: str,
            ) -> None:
                self.binding = (response_id, interrupting_response_id)

            def snapshot(self) -> dict[str, object]:
                return {"state": {}}

            def completed_response_usage_snapshot(self) -> list[dict[str, object]]:
                return []

        with tempfile.TemporaryDirectory() as directory:
            gate = FakeGate()
            ledger = AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread",
                provider_gate=gate,  # type: ignore[arg-type]
                provider_gate_artifact_path=Path(directory) / "gate.json",
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child(
                "root-thread", "child-thread", "/root/lemma_search"
            )
            ledger.threads["child-thread"].update(
                {
                    "provisional": False,
                    "spawn_binding_status": "resolved",
                    "turn_seen": True,
                    "terminal_turn_id": "child-turn",
                    # The historical interrupt has already been followed by a
                    # collaboration-message reactivation on this same thread.
                    "active_turn_id": "child-followup-turn",
                    "turn_status": "inProgress",
                    "turn_completed_event_unix_ns": 5_000_000,
                    "turn_completed_at_monotonic_ns": 50_000,
                }
            )
            ledger.terminal_turn_lifecycles[("child-thread", "child-turn")] = {
                "thread_id": "child-thread",
                "turn_id": "child-turn",
                "status": "interrupted",
                "turn_completed_at_unix_ns": 5_100_000,
                "turn_completed_at_monotonic_ns": 50_000,
                "turn_completed_event_unix_ns": 5_000_000,
            }
            interrupt_item = {
                "type": "function_call",
                "id": "fc-interrupt",
                "call_id": "call-interrupt",
                "name": "interrupt_agent",
                "namespace": "collaboration",
                "arguments": arguments,
            }
            ledger.raw_function_calls["call-interrupt"] = {
                "call_type": "function_call",
                "item_id": "fc-interrupt",
                "call_id": "call-interrupt",
                "name": "interrupt_agent",
                "namespace": "collaboration",
                "arguments": arguments,
                "parent_thread_id": "root-thread",
                "parent_turn_id": "root-turn",
                "parent_response_id": "resp-interrupt",
            }
            ledger.responses["resp-interrupt"] = {
                "thread_id": "root-thread", "turn_id": "root-turn",
                "usage": {field: 0 for field in ledger._SUM_FIELDS},
                "sequence": 1, "raw_items": [interrupt_item],
                "observed_at_unix_ns": 2_100_000,
                "observed_at_monotonic_ns": 21_000,
            }
            ledger.raw_item_observations["fc-interrupt"] = {
                "thread_id": "root-thread", "turn_id": "root-turn",
                "item": interrupt_item,
                "event_observed_at_unix_ns": 2_000_000,
                "observed_at_monotonic_ns": 20_000,
            }
            activity_item = {
                "type": "subAgentActivity", "kind": "interrupted",
                "id": "call-interrupt", "agentThreadId": "child-thread",
                "agentPath": "/root/lemma_search",
            }
            ledger.subagent_interrupt_activities["call-interrupt"] = {
                "activity_id": "call-interrupt", "kind": "interrupted",
                "parent_thread_id": "root-thread",
                "parent_turn_id": "root-turn",
                "child_thread_id": "child-thread",
                "agent_path": "/root/lemma_search",
                "item_sha256": hashlib.sha256(
                    json.dumps(activity_item, sort_keys=True, separators=(",", ":")).encode()
                ).hexdigest(),
                "observed_at_unix_ns": 3_000_000,
                "observed_at_monotonic_ns": 30_000,
            }
            output_item = {
                "type": "function_call_output", "id": "fco-interrupt",
                "call_id": "call-interrupt",
                "output": '{"previous_status":"running"}',
            }
            ledger.delayed_tool_outputs[("function_call_output", "call-interrupt")] = {
                "item_id": "fco-interrupt"
            }
            ledger.raw_item_observations["fco-interrupt"] = {
                "thread_id": "root-thread", "turn_id": "root-turn",
                "item": output_item,
                "event_observed_at_unix_ns": 4_000_000,
                "observed_at_monotonic_ns": 40_000,
            }

            self.assertTrue(
                ledger.has_unreconciled_explicit_child_interrupt_lifecycle()
            )
            self.assertEqual(
                ledger.reconcile_discarded_after_explicit_child_interrupts(), 1
            )
            self.assertFalse(
                ledger.has_unreconciled_explicit_child_interrupt_lifecycle()
            )
            self.assertEqual(gate.binding, ("resp-discarded", "resp-interrupt"))
            evidence = ledger.discarded_after_explicit_child_interrupt_evidence[
                "resp-discarded"
            ]
            self.assertEqual(
                set(evidence),
                set(codex_isolated.DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS),
            )
            self.assertEqual(evidence["interrupted_agent_path"], "/root/lemma_search")

            bad = copy.deepcopy(candidate)
            bad["commit_unix_ns"] = 4_500_000
            gate.discarded_after_explicit_child_interrupt_candidates = (  # type: ignore[method-assign]
                lambda _thread, _turn: [bad]
            )
            ledger.discarded_after_explicit_child_interrupt_evidence.clear()
            with self.assertRaisesRegex(RuntimeError, "conservatively precede"):
                ledger.reconcile_discarded_after_explicit_child_interrupts()

            # A provider request admitted only after the interrupt function was
            # emitted cannot be explained as work discarded by that interrupt.
            admitted_after_interrupt = copy.deepcopy(candidate)
            admitted_after_interrupt["admitted_unix_ns"] = 2_000_000
            gate.discarded_after_explicit_child_interrupt_candidates = (  # type: ignore[method-assign]
                lambda _thread, _turn: [admitted_after_interrupt]
            )
            with self.assertRaisesRegex(RuntimeError, "conservatively precede"):
                ledger.reconcile_discarded_after_explicit_child_interrupts()

    def test_explicit_child_interrupt_cleanup_wait_covers_job_1509703_delay(
        self,
    ) -> None:
        """A 5.568s in-flight completion fits the 45s cleanup envelope."""

        class FakeGate:
            def snapshot(self) -> dict[str, object]:
                return {"state": {"active_handler_count": 1}}

        class FakeLedger:
            def __init__(self) -> None:
                self.resolved = False
                self.reconcile_calls = 0

            def has_unreconciled_explicit_child_interrupt_lifecycle(self) -> bool:
                return not self.resolved

            def reconcile_discarded_after_explicit_child_interrupts(self) -> int:
                self.reconcile_calls += 1
                if clock[0] >= 5.568:
                    self.resolved = True
                    return 1
                return 0

        clock = [0.0]

        def monotonic() -> float:
            return clock[0]

        def sleep(seconds: float) -> None:
            clock[0] += seconds

        ledger = FakeLedger()
        with mock.patch.object(
            codex_isolated.time, "monotonic", side_effect=monotonic
        ), mock.patch.object(codex_isolated.time, "sleep", side_effect=sleep):
            self.assertTrue(
                codex_isolated._wait_for_explicit_child_interrupt_reconciliation(
                    FakeGate(), ledger  # type: ignore[arg-type]
                )
            )
        self.assertGreaterEqual(clock[0], 5.568)
        self.assertLess(clock[0], 45.0)
        self.assertGreater(ledger.reconcile_calls, 1)

    def test_explicit_child_interrupt_cleanup_expiry_remains_unresolved(
        self,
    ) -> None:
        """Cleanup expiry returns unresolved for terminal fail-closed checks."""

        class FakeGate:
            def snapshot(self) -> dict[str, object]:
                return {"state": {"active_handler_count": 1}}

        class FakeLedger:
            def has_unreconciled_explicit_child_interrupt_lifecycle(self) -> bool:
                return True

            def reconcile_discarded_after_explicit_child_interrupts(self) -> int:
                return 0

        clock = [0.0]

        def monotonic() -> float:
            return clock[0]

        def sleep(seconds: float) -> None:
            clock[0] += seconds

        with mock.patch.object(
            codex_isolated.time, "monotonic", side_effect=monotonic
        ), mock.patch.object(codex_isolated.time, "sleep", side_effect=sleep):
            self.assertFalse(
                codex_isolated._wait_for_explicit_child_interrupt_reconciliation(
                    FakeGate(), FakeLedger()  # type: ignore[arg-type]
                )
            )
        self.assertGreaterEqual(clock[0], 45.0)

    def test_new_task_message_is_not_reconciliation_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread"
            )
            ledger._link_child(
                "root-thread", "child-thread", "/root/library_search"
            )
            ledger.threads["child-thread"].update(
                {"provisional": False, "spawn_binding_status": "resolved"}
            )
            ledger._capture_collaboration_message(
                thread_id="child-thread",
                turn_id="child-turn",
                item={
                    "type": "agent_message",
                    "id": "amsg-new-task",
                    "author": "/root",
                    "recipient": "/root/library_search",
                    "content": [
                        {
                            "type": "input_text",
                            "text": (
                                "Message Type: NEW_TASK\n"
                                "Task name: /root/library_search\n"
                                "Sender: /root\n"
                                "Payload:\nperform the bounded search"
                            ),
                        }
                    ],
                    "internal_chat_message_metadata_passthrough": {
                        "turn_id": "child-turn"
                    },
                },
                observed_at_unix_ns=1_500,
                observed_at_monotonic_ns=150,
            )
            self.assertEqual(ledger.collaboration_message_observations, {})

    def test_root_to_child_message_reconciles_child_response_retry(self) -> None:
        candidate = {
            "response_id": "resp-child-interrupted",
            "call_id": "provider-call-00000108",
            "thread_id": "child-thread",
            "turn_id": "child-turn",
            "normalized_usage": {"total_tokens": 29_057},
            "commit_unix_ns": 1_000,
            "commit_monotonic_ns": 100,
            "action_capable_item_count": 1,
            "response_output_manifest_sha256": "a" * 64,
            "successor_response_id": "resp-child-retry",
            "successor_call_id": "provider-call-00000112",
            "successor_admitted_unix_ns": 2_000_000,
            "successor_admitted_monotonic_ns": 200,
        }

        class FakeGate:
            def superseded_by_collaboration_message_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                return [copy.deepcopy(candidate)]

            def crossbind_superseded_by_collaboration_message(
                self, response_id: str, thread_id: str, turn_id: str,
                successor_response_id: str,
            ) -> None:
                self.binding = (response_id, successor_response_id)

        with tempfile.TemporaryDirectory() as directory:
            gate = FakeGate()
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread",
                provider_gate=gate,  # type: ignore[arg-type]
                provider_gate_artifact_path=Path(directory) / "gate.json",
            )
            ledger._link_child("root-thread", "child-thread", "/root/library_search")
            ledger.threads["child-thread"].update(
                {"provisional": False, "spawn_binding_status": "resolved"}
            )
            prefix = (
                "Message Type: MESSAGE\nTask name: /root/library_search\n"
                "Sender: /root\nPayload:\n"
            )
            ledger._capture_collaboration_message(
                thread_id="child-thread", turn_id="child-turn",
                item={
                    "type": "agent_message", "id": "amsg-job-1509232",
                    "author": "/root", "recipient": "/root/library_search",
                    "content": [
                        {"type": "input_text", "text": prefix},
                        {"type": "encrypted_content", "encrypted_content": "ciphertext"},
                    ],
                    "internal_chat_message_metadata_passthrough": {
                        "turn_id": "child-turn"
                    },
                },
                observed_at_unix_ns=500_000,
                observed_at_monotonic_ns=150,
            )
            ledger._reconcile_superseded_responses_for_successor(
                thread_id="child-thread", turn_id="child-turn",
                successor_response_id="resp-child-retry",
            )
            self.assertEqual(
                gate.binding, ("resp-child-interrupted", "resp-child-retry")
            )
            evidence = ledger.superseded_by_collaboration_message_evidence[
                "resp-child-interrupted"
            ]
            self.assertEqual(
                evidence["collaboration_messages"][0]["recipient"],
                "/root/library_search",
            )

    def test_job_1509339_uses_appserver_event_time_across_stdout_backlog(
        self,
    ) -> None:
        commit_unix_ns = 1_786_567_530_186_304_549
        successor_unix_ns = 1_786_567_530_611_518_869
        candidate = {
            "response_id": "resp-job-1509339-missing",
            "call_id": "provider-call-00000161",
            "thread_id": "root-thread",
            "turn_id": "root-turn",
            "normalized_usage": {"total_tokens": 32_512},
            "commit_unix_ns": commit_unix_ns,
            "commit_monotonic_ns": 100,
            "action_capable_item_count": 1,
            "response_output_manifest_sha256": "a" * 64,
            "successor_response_id": "resp-job-1509339-successor",
            "successor_call_id": "provider-call-00000166",
            "successor_admitted_unix_ns": successor_unix_ns,
            "successor_admitted_monotonic_ns": 200,
        }

        class FakeGate:
            def superseded_by_collaboration_message_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                return [copy.deepcopy(candidate)]

            def crossbind_superseded_by_collaboration_message(
                self, response_id: str, thread_id: str, turn_id: str,
                successor_response_id: str,
            ) -> None:
                self.binding = (response_id, successor_response_id)

        def make_ledger(directory: str) -> tuple[AttemptUsageLedger, FakeGate]:
            gate = FakeGate()
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread",
                provider_gate=gate,  # type: ignore[arg-type]
                provider_gate_artifact_path=Path(directory) / "gate.json",
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child("root-thread", "child-thread", "/root/worker")
            ledger.threads["child-thread"].update(
                {"provisional": False, "spawn_binding_status": "resolved"}
            )
            return ledger, gate

        def message(emitted_at_ms: int) -> dict[str, object]:
            return {
                "method": "rawResponseItem/completed",
                "emittedAtMs": emitted_at_ms,
                "params": {
                    "threadId": "root-thread",
                    "turnId": "root-turn",
                    "item": {
                        "type": "agent_message",
                        "id": f"amsg-{emitted_at_ms}",
                        "author": "/root/worker",
                        "recipient": "/root",
                        "content": [{
                            "type": "input_text",
                            "text": (
                                "Message Type: MESSAGE\nTask name: /root\n"
                                "Sender: /root/worker\nPayload:\nreplacement"
                            ),
                        }],
                        "internal_chat_message_metadata_passthrough": {
                            "turn_id": "root-turn"
                        },
                    },
                },
            }

        # The event was emitted inside the provider window, although a stdout
        # backlog made the adapter read it only after successor admission.
        with tempfile.TemporaryDirectory() as directory:
            ledger, gate = make_ledger(directory)
            with mock.patch.object(
                codex_isolated.time, "time_ns",
                return_value=successor_unix_ns + 1_000_000_000,
            ), mock.patch.object(
                codex_isolated.time, "monotonic_ns", return_value=300,
            ):
                ledger.observe(message(1_786_567_530_289))
            ledger._reconcile_superseded_responses_for_successor(
                thread_id="root-thread", turn_id="root-turn",
                successor_response_id="resp-job-1509339-successor",
            )
            self.assertEqual(
                gate.binding,
                ("resp-job-1509339-missing", "resp-job-1509339-successor"),
            )
            evidence = ledger.superseded_by_collaboration_message_evidence[
                "resp-job-1509339-missing"
            ]["collaboration_messages"][0]
            self.assertEqual(
                evidence["observed_at_unix_ns"], 1_786_567_530_289_000_000
            )
            self.assertEqual(evidence["observed_at_monotonic_ns"], 300)

        # The millisecond containing successor admission is not wholly inside
        # the predecessor window, so it is conservatively rejected.
        with tempfile.TemporaryDirectory() as directory:
            ledger, _ = make_ledger(directory)
            with mock.patch.object(
                codex_isolated.time, "time_ns",
                return_value=successor_unix_ns + 1_000_000_000,
            ), mock.patch.object(
                codex_isolated.time, "monotonic_ns", return_value=300,
            ):
                ledger.observe(message(1_786_567_530_611))
            with self.assertRaisesRegex(
                RuntimeError,
                "nonempty collaboration-message batch",
            ):
                ledger._reconcile_superseded_responses_for_successor(
                    thread_id="root-thread", turn_id="root-turn",
                    successor_response_id="resp-job-1509339-successor",
                )

    def test_job_1509369_final_reconciliation_accepts_complete_superseded_shapes(
        self,
    ) -> None:
        usage = {
            "input_tokens": 10,
            "cached_input_tokens": 2,
            "cache_write_input_tokens": 0,
            "output_tokens": 1,
            "reasoning_output_tokens": 1,
            "total_tokens": 11,
        }

        def manifest_item(
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

        shapes = [
            [
                manifest_item(0, "reasoning"),
                manifest_item(1, "custom_tool_call", name="exec"),
            ],
            [manifest_item(0, "reasoning"), manifest_item(1, "message")],
            [
                manifest_item(0, "reasoning"),
                manifest_item(1, "message"),
                manifest_item(
                    2,
                    "function_call",
                    name="send_message",
                    namespace="collaboration",
                ),
            ],
        ]
        metadata = {
            "request_kind": "turn",
            "thread_id": "root-thread",
            "turn_id": "root-turn",
        }
        calls: list[dict[str, object]] = []
        for index, items in enumerate(shapes):
            response_id = f"resp-superseded-{index}"
            successor_id = (
                f"resp-superseded-{index + 1}"
                if index + 1 < len(shapes)
                else "resp-direct"
            )
            calls.append(
                {
                    "sequence": index + 1,
                    "call_id": f"provider-call-{index + 1}",
                    "response_id": response_id,
                    "admitted_monotonic_ns": 10 + index * 20,
                    "admitted_unix_ns": 10_000_000 + index * 20_000_000,
                    "commit_monotonic_ns": 20 + index * 20,
                    "commit_unix_ns": 20_000_000 + index * 20_000_000,
                    "normalized_usage": dict(usage),
                    "error": None,
                    "client_release_complete": True,
                    "crossed_cap": False,
                    "release_kind": "byte_identity",
                    "released_body_sha256": "b" * 64,
                    "upstream_body_sha256": "b" * 64,
                    "released_body_bytes": 100,
                    "upstream_body_bytes": 100,
                    "request_metadata": dict(metadata),
                    "response_output_manifest": {
                        "schema_version": 1,
                        "response_id": response_id,
                        "output_item_count": len(items),
                        "action_capable_item_count": sum(
                            item["type"] == "function_call"
                            or str(item["type"]).endswith("_call")
                            for item in items
                        ),
                        "items": items,
                    },
                    "appserver_crossbind": None,
                    "appserver_delivery": {
                        "kind": "superseded_by_collaboration_message",
                        "successor_call_id": f"provider-call-{index + 2}",
                        "successor_response_id": successor_id,
                        "bind_unix_ns": 25_000_000 + index * 20_000_000,
                        "bind_monotonic_ns": 25 + index * 20,
                    },
                }
            )
        direct = {
            "sequence": 4,
            "call_id": "provider-call-4",
            "response_id": "resp-direct",
            "admitted_monotonic_ns": 70,
            "admitted_unix_ns": 70_000_000,
            "commit_monotonic_ns": 80,
            "commit_unix_ns": 80_000_000,
            "normalized_usage": dict(usage),
            "error": None,
            "client_release_complete": True,
            "request_metadata": dict(metadata),
            "appserver_crossbind": {
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "event_sequence": 1,
                "normalized_usage": dict(usage),
                "bind_unix_ns": 85_000_000,
                "bind_monotonic_ns": 85,
            },
            "appserver_delivery": {
                "kind": "direct_raw_response",
                "successor_call_id": None,
                "successor_response_id": None,
                "bind_unix_ns": 85_000_000,
                "bind_monotonic_ns": 85,
            },
        }
        calls.append(direct)
        state = {
            "phase": "CLOSED",
            "close_reason": "accepted_submission",
            "completed_tokens": 44,
            "crossing": None,
            "crossing_closed": False,
            "open_request_ids": [],
            "all_complete": True,
            "no_post_close_upstream": True,
            "poisoned": False,
            "poison_reasons": [],
        }
        record = {"state": state, "calls": calls, "invariants": {"ok": True}}

        with tempfile.TemporaryDirectory() as directory:
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread"
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child("root-thread", "child-thread", "/root/worker")
            ledger.threads["child-thread"].update(
                {"provisional": False, "spawn_binding_status": "resolved"}
            )
            ledger.responses = {
                "resp-direct": {
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "sequence": 1,
                    "observed_at_unix_ns": 86_000_000,
                    "observed_at_monotonic_ns": 86,
                    "usage": dict(usage),
                }
            }
            ledger.aggregate = dict(usage)
            ledger.superseded_by_collaboration_message_evidence = {
                f"resp-superseded-{index}": {
                    "response_id": f"resp-superseded-{index}",
                    "provider_call_id": f"provider-call-{index + 1}",
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "successor_response_id": (
                        f"resp-superseded-{index + 1}"
                        if index + 1 < len(shapes)
                        else "resp-direct"
                    ),
                    "successor_call_id": f"provider-call-{index + 2}",
                    "collaboration_messages": [
                        {
                            "item_id": f"message-{index}",
                            "item_sha256": "c" * 64,
                            "author": "/root/worker",
                            "recipient": "/root",
                            "observed_at_unix_ns": (
                                25_000_000 + index * 20_000_000
                            ),
                            "observed_at_monotonic_ns": 25 + index * 20,
                        }
                    ],
                }
                for index in range(len(shapes))
            }
            reconciliation = codex_isolated._provider_gate_matches_ledger(
                record,
                state,
                ledger,
                close_reason="accepted_submission",
            )

        self.assertIsNotNone(reconciliation)
        assert reconciliation is not None
        self.assertEqual(reconciliation["provider_response_count"], 4)
        self.assertEqual(reconciliation["appserver_response_count"], 1)
        self.assertEqual(
            reconciliation[
                "superseded_by_collaboration_message_response_count"
            ],
            3,
        )
        self.assertEqual(reconciliation["provider_usage"]["total_tokens"], 44)

    def test_job_1510008_final_reconciliation_accepts_message_superseded_wait(
        self,
    ) -> None:
        """An exact wait may use the generic MESSAGE-supersession delivery."""

        wait_usage = {
            "input_tokens": 52_889,
            "cached_input_tokens": 50_944,
            "cache_write_input_tokens": 0,
            "output_tokens": 63,
            "reasoning_output_tokens": 40,
            "total_tokens": 52_952,
        }
        successor_usage = {
            "input_tokens": 53_107,
            "cached_input_tokens": 51_968,
            "cache_write_input_tokens": 0,
            "output_tokens": 21,
            "reasoning_output_tokens": 0,
            "total_tokens": 53_128,
        }
        wait_response_id = "resp-job-1510008-wait"
        successor_response_id = "resp-job-1510008-successor"
        metadata = {
            "request_kind": "turn",
            "thread_id": "root-thread",
            "turn_id": "root-turn",
        }

        def manifest_item(
            index: int,
            item_type: str,
            *,
            name: str | None = None,
            namespace: str | None = None,
            wait_timeout_ms: int | None = None,
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
                "wait_timeout_ms": wait_timeout_ms,
            }

        wait_items = [
            manifest_item(0, "reasoning"),
            manifest_item(
                1,
                "function_call",
                name="wait_agent",
                namespace="collaboration",
                wait_timeout_ms=30_000,
            ),
        ]
        wait_call = {
            "sequence": 1,
            "call_id": "provider-call-job-1510008-wait",
            "response_id": wait_response_id,
            "admitted_monotonic_ns": 10,
            "admitted_unix_ns": 10_000_000,
            "commit_monotonic_ns": 20,
            "commit_unix_ns": 20_000_000,
            "normalized_usage": dict(wait_usage),
            "error": None,
            "client_release_complete": True,
            "crossed_cap": False,
            "release_kind": "byte_identity",
            "released_body_sha256": "b" * 64,
            "upstream_body_sha256": "b" * 64,
            "released_body_bytes": 100,
            "upstream_body_bytes": 100,
            "request_metadata": dict(metadata),
            "response_output_manifest": {
                "schema_version": 1,
                "response_id": wait_response_id,
                "output_item_count": len(wait_items),
                "action_capable_item_count": 1,
                "items": wait_items,
            },
            "appserver_crossbind": None,
            "appserver_delivery": {
                "kind": "superseded_by_collaboration_message",
                "successor_call_id": "provider-call-job-1510008-successor",
                "successor_response_id": successor_response_id,
                "bind_unix_ns": 35_000_000,
                "bind_monotonic_ns": 35,
            },
        }
        successor_call = {
            "sequence": 2,
            "call_id": "provider-call-job-1510008-successor",
            "response_id": successor_response_id,
            "admitted_monotonic_ns": 30,
            "admitted_unix_ns": 30_000_000,
            "commit_monotonic_ns": 40,
            "commit_unix_ns": 40_000_000,
            "normalized_usage": dict(successor_usage),
            "error": None,
            "client_release_complete": True,
            "request_metadata": dict(metadata),
            "appserver_crossbind": {
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "event_sequence": 1,
                "normalized_usage": dict(successor_usage),
                "bind_unix_ns": 45_000_000,
                "bind_monotonic_ns": 45,
            },
            "appserver_delivery": {
                "kind": "direct_raw_response",
                "successor_call_id": None,
                "successor_response_id": None,
                "bind_unix_ns": 45_000_000,
                "bind_monotonic_ns": 45,
            },
        }
        state = {
            "phase": "CLOSED",
            "close_reason": "accepted_submission",
            "completed_tokens": 106_080,
            "crossing": None,
            "crossing_closed": False,
            "open_request_ids": [],
            "all_complete": True,
            "no_post_close_upstream": True,
            "poisoned": False,
            "poison_reasons": [],
        }
        record = {
            "state": state,
            "calls": [wait_call, successor_call],
            "invariants": {"ok": True},
        }

        with tempfile.TemporaryDirectory() as directory:
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json", 5_000_000, "root-thread"
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child(
                "root-thread", "child-thread", "/root/lemma_search"
            )
            ledger.threads["child-thread"].update(
                {"provisional": False, "spawn_binding_status": "resolved"}
            )
            ledger.responses = {
                successor_response_id: {
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "sequence": 1,
                    "observed_at_unix_ns": 46_000_000,
                    "observed_at_monotonic_ns": 46,
                    "usage": dict(successor_usage),
                }
            }
            ledger.aggregate = dict(successor_usage)
            ledger.superseded_by_collaboration_message_evidence = {
                wait_response_id: {
                    "response_id": wait_response_id,
                    "provider_call_id": "provider-call-job-1510008-wait",
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "successor_response_id": successor_response_id,
                    "successor_call_id": (
                        "provider-call-job-1510008-successor"
                    ),
                    "collaboration_messages": [
                        {
                            "item_id": "amsg-job-1510008",
                            "item_sha256": "c" * 64,
                            "author": "/root/lemma_search",
                            "recipient": "/root",
                            "observed_at_unix_ns": 25_000_000,
                            "observed_at_monotonic_ns": 25,
                        }
                    ],
                }
            }
            reconciliation = codex_isolated._provider_gate_matches_ledger(
                record,
                state,
                ledger,
                close_reason="accepted_submission",
            )

        self.assertIsNotNone(reconciliation)
        assert reconciliation is not None
        self.assertEqual(reconciliation["provider_response_count"], 2)
        self.assertEqual(reconciliation["appserver_response_count"], 1)
        self.assertEqual(
            reconciliation[
                "superseded_by_collaboration_message_response_count"
            ],
            1,
        )
        self.assertEqual(
            reconciliation["provider_usage"]["total_tokens"],
            reconciliation["appserver_usage"]["total_tokens"]
            + reconciliation[
                "superseded_by_collaboration_message_usage"
            ]["total_tokens"],
        )

    def test_job_1509218_six_custom_exec_replacements_bind_message_chain(
        self,
    ) -> None:
        candidates: list[dict[str, object]] = []
        for index in range(6):
            candidates.append(
                {
                    "response_id": f"resp-missing-{index + 1}",
                    "call_id": f"provider-call-{index + 1:08d}",
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "normalized_usage": {
                        "input_tokens": 29_000,
                        "cached_input_tokens": 0,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 250,
                        "reasoning_output_tokens": 0,
                        "total_tokens": 29_250,
                    },
                    "commit_unix_ns": 10_000_000 + index * 2_000_000,
                    "commit_monotonic_ns": 1_000 + index * 100,
                    "action_capable_item_count": 1,
                    "response_output_manifest_sha256": "a" * 64,
                    "successor_response_id": (
                        f"resp-missing-{index + 2}"
                        if index < 5
                        else "resp-direct"
                    ),
                    "successor_call_id": f"provider-call-{index + 2:08d}",
                    "successor_admitted_unix_ns": 11_500_000 + index * 2_000_000,
                    "successor_admitted_monotonic_ns": 1_050 + index * 100,
                }
            )

        class FakeGate:
            def __init__(self) -> None:
                self.bindings: list[tuple[str, str]] = []

            def superseded_by_collaboration_message_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                self.identity = (thread_id, turn_id)
                return copy.deepcopy(candidates)

            def crossbind_superseded_by_collaboration_message(
                self,
                response_id: str,
                thread_id: str,
                turn_id: str,
                successor_response_id: str,
            ) -> None:
                self.bindings.append((response_id, successor_response_id))

        with tempfile.TemporaryDirectory() as directory:
            gate = FakeGate()
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json",
                5_000_000,
                "root-thread",
                provider_gate=gate,  # type: ignore[arg-type]
                provider_gate_artifact_path=Path(directory) / "gate.json",
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child("root-thread", "child-thread", "/root/worker")
            ledger.threads["child-thread"].update(
                {"provisional": False, "spawn_binding_status": "resolved"}
            )
            for index in range(6):
                ledger._capture_collaboration_message(
                    thread_id="root-thread",
                    turn_id="root-turn",
                    item={
                        "type": "agent_message",
                        "id": f"amsg-job-1509218-{index + 1}",
                        "author": "/root/worker",
                        "recipient": "/root",
                        "content": [
                            {
                                "type": "input_text",
                                "text": (
                                    "Message Type: MESSAGE\n"
                                    "Task name: /root\n"
                                    "Sender: /root/worker\n"
                                    "Payload:\nreplacement"
                                ),
                            }
                        ],
                        "internal_chat_message_metadata_passthrough": {
                            "turn_id": "root-turn"
                        },
                    },
                    observed_at_unix_ns=10_500_000 + index * 2_000_000,
                    observed_at_monotonic_ns=1_025 + index * 100,
                )
            ledger._reconcile_superseded_responses_for_successor(
                thread_id="root-thread",
                turn_id="root-turn",
                successor_response_id="resp-direct",
            )
            self.assertEqual(len(gate.bindings), 6)
            self.assertEqual(
                set(ledger.superseded_by_collaboration_message_evidence),
                {f"resp-missing-{index + 1}" for index in range(6)},
            )
            self.assertEqual(
                sum(
                    len(item["collaboration_messages"])
                    for item in ledger.superseded_by_collaboration_message_evidence.values()
                ),
                6,
            )

    def test_suppressed_wait_requires_one_windowed_completed_child_final_answer(
        self,
    ) -> None:
        candidate = {
            "response_id": "resp-wait",
            "call_id": "provider-call-00000007",
            "thread_id": "root-thread",
            "turn_id": "root-turn",
            "normalized_usage": {
                "input_tokens": 11_700,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 135,
                "reasoning_output_tokens": 0,
                "total_tokens": 11_835,
            },
            "commit_unix_ns": 1_000,
            "commit_monotonic_ns": 100,
            "wait_call_id": "call-wait",
            "wait_timeout_ms": 1280,
            "response_output_manifest_sha256": "b" * 64,
            "successor_response_id": "resp-successor",
            "successor_call_id": "provider-call-00000010",
            "successor_admitted_unix_ns": 2_000_000,
            "successor_admitted_monotonic_ns": 200,
        }

        class FakeGate:
            def __init__(self) -> None:
                self.bindings: list[tuple[str, str, str, str]] = []

            def suppressed_collaboration_wait_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                self.assert_identity = (thread_id, turn_id)
                return [copy.deepcopy(candidate)]

            def crossbind_suppressed_collaboration_wait(
                self,
                response_id: str,
                thread_id: str,
                turn_id: str,
                successor_response_id: str,
            ) -> None:
                self.bindings.append(
                    (response_id, thread_id, turn_id, successor_response_id)
                )

        with tempfile.TemporaryDirectory() as directory:
            gate = FakeGate()
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json",
                5_000_000,
                "root-thread",
                provider_gate=gate,  # type: ignore[arg-type]
                provider_gate_artifact_path=Path(directory) / "gate.json",
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child(
                "root-thread", "child-thread", "/root/ultra_child"
            )
            child = ledger.threads["child-thread"]
            child.update(
                {
                    "provisional": False,
                    "spawn_binding_status": "resolved",
                    "turn_status": "completed",
                    "terminal_turn_id": "child-turn",
                    "turn_completed_at_unix_ns": 900,
                    "turn_completed_at_monotonic_ns": 90,
                }
            )
            item = {
                "type": "agent_message",
                "id": "amsg-job-1508245",
                "author": "/root/ultra_child",
                "recipient": "/root",
                "content": [
                    {
                        "type": "input_text",
                        "text": (
                            "Message Type: FINAL_ANSWER\n"
                            "Task name: /root\n"
                            "Sender: /root/ultra_child\n"
                            "Payload:\n"
                            "HIGHAMBENCH_ULTRA_CHILD_OK"
                        ),
                    }
                ],
                "internal_chat_message_metadata_passthrough": {
                    "turn_id": "root-turn"
                },
            }
            ledger._capture_final_answer_agent_message(
                thread_id="root-thread",
                turn_id="root-turn",
                item=item,
                observed_at_unix_ns=500_000,
                observed_at_monotonic_ns=150,
            )
            ledger._reconcile_suppressed_waits_for_successor(
                thread_id="root-thread",
                turn_id="root-turn",
                successor_response_id="resp-successor",
            )
            self.assertEqual(
                gate.bindings,
                [
                    (
                        "resp-wait",
                        "root-thread",
                        "root-turn",
                        "resp-successor",
                    )
                ],
            )
            evidence = ledger.suppressed_collaboration_wait_evidence["resp-wait"]
            self.assertEqual(evidence["agent_message_item_id"], "amsg-job-1508245")
            self.assertEqual(evidence["agent_message_author"], "/root/ultra_child")

            outside = copy.deepcopy(candidate)
            outside["commit_unix_ns"] = 500_000
            with self.assertRaises(RuntimeError):
                ledger._child_result_for_suppressed_wait(outside)

    def test_job_1509972_wait_with_interim_message_uses_general_supersession(
        self,
    ) -> None:
        """A MESSAGE-displaced wait is not forced into FINAL-only evidence."""

        wait_commit_unix_ns = 1_786_614_836_691_613_155
        wait_commit_monotonic_ns = 652_924_558_485_942
        message_unix_ns = 1_786_614_836_860_000_000
        message_monotonic_ns = 652_924_726_872_787
        successor_admitted_unix_ns = 1_786_614_836_953_233_278
        successor_admitted_monotonic_ns = 652_924_820_105_998
        empty_final_unix_ns = 1_786_614_839_933_000_000
        empty_final_monotonic_ns = 652_927_799_872_787
        wait_response_id = "resp_05cb9644c56a82e8016a7d942bfbe881978142d85bfc20090f"
        successor_response_id = (
            "resp_05cb9644c56a82e8016a7d94356cc88197bab7176a02086ca2"
        )
        wait_candidate = {
            "response_id": wait_response_id,
            "call_id": "provider-call-00000238",
            "thread_id": "root-thread",
            "turn_id": "root-turn",
            "normalized_usage": {
                "input_tokens": 35_671,
                "cached_input_tokens": 34_560,
                "cache_write_input_tokens": 0,
                "output_tokens": 234,
                "reasoning_output_tokens": 211,
                "total_tokens": 35_905,
            },
            "commit_unix_ns": wait_commit_unix_ns,
            "commit_monotonic_ns": wait_commit_monotonic_ns,
            "wait_call_id": "call_inZlS92BcA4DsGj3ogBskfwy",
            "wait_timeout_ms": 30_000,
            "response_output_manifest_sha256": "a" * 64,
            "successor_response_id": successor_response_id,
            "successor_call_id": "provider-call-00000243",
            "successor_admitted_unix_ns": successor_admitted_unix_ns,
            "successor_admitted_monotonic_ns": (
                successor_admitted_monotonic_ns
            ),
        }
        general_candidate = {
            key: copy.deepcopy(value)
            for key, value in wait_candidate.items()
            if key not in {"wait_call_id", "wait_timeout_ms"}
        }
        general_candidate["action_capable_item_count"] = 1

        class FakeGate:
            def __init__(self) -> None:
                self.suppressed_bindings: list[tuple[str, str]] = []
                self.superseded_bindings: list[tuple[str, str]] = []

            def suppressed_collaboration_wait_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                return [copy.deepcopy(wait_candidate)]

            def crossbind_suppressed_collaboration_wait(
                self,
                response_id: str,
                thread_id: str,
                turn_id: str,
                successor_response_id: str,
            ) -> None:
                self.suppressed_bindings.append(
                    (response_id, successor_response_id)
                )

            def superseded_by_collaboration_message_candidates(
                self, thread_id: str, turn_id: str
            ) -> list[dict[str, object]]:
                return [copy.deepcopy(general_candidate)]

            def crossbind_superseded_by_collaboration_message(
                self,
                response_id: str,
                thread_id: str,
                turn_id: str,
                successor_response_id: str,
            ) -> None:
                self.superseded_bindings.append(
                    (response_id, successor_response_id)
                )

        def make_ledger(directory: str) -> tuple[AttemptUsageLedger, FakeGate]:
            gate = FakeGate()
            ledger = codex_isolated.AttemptUsageLedger(
                Path(directory) / "usage.json",
                5_000_000,
                "root-thread",
                provider_gate=gate,  # type: ignore[arg-type]
                provider_gate_artifact_path=Path(directory) / "gate.json",
            )
            ledger.root_turn_id = "root-turn"
            ledger._link_child(
                "root-thread", "child-thread", "/root/alternate_proof"
            )
            ledger.threads["child-thread"].update(
                {
                    "provisional": False,
                    "spawn_binding_status": "resolved",
                    "turn_status": "inProgress",
                    "active_turn_id": "child-turn",
                }
            )
            return ledger, gate

        interim_message = {
            "type": "agent_message",
            "id": "amsg_019ffa8a-ee7a-7251-b10a-130edc3327cf",
            "author": "/root/alternate_proof",
            "recipient": "/root",
            "content": [
                {
                    "type": "input_text",
                    "text": (
                        "Message Type: MESSAGE\n"
                        "Task name: /root\n"
                        "Sender: /root/alternate_proof\n"
                        "Payload:\n"
                    ),
                },
                {
                    "type": "encrypted_content",
                    "encrypted_content": "job-1509972-encrypted-payload",
                },
            ],
            "internal_chat_message_metadata_passthrough": {
                "turn_id": "root-turn"
            },
        }
        empty_final = {
            "type": "agent_message",
            "id": "amsg_019ffa8a-fa7c-74c2-9dfc-40251feb4b71",
            "author": "/root/alternate_proof",
            "recipient": "/root",
            "content": [
                {
                    "type": "input_text",
                    "text": (
                        "Message Type: FINAL_ANSWER\n"
                        "Task name: /root\n"
                        "Sender: /root/alternate_proof\n"
                        "Payload:\n"
                    ),
                }
            ],
            "internal_chat_message_metadata_passthrough": {
                "turn_id": "root-turn"
            },
        }

        with tempfile.TemporaryDirectory() as directory:
            ledger, gate = make_ledger(directory)
            ledger._capture_collaboration_message(
                thread_id="root-thread",
                turn_id="root-turn",
                item=interim_message,
                observed_at_unix_ns=message_unix_ns,
                observed_at_monotonic_ns=message_monotonic_ns,
            )
            ledger._capture_final_answer_agent_message(
                thread_id="root-thread",
                turn_id="root-turn",
                item=empty_final,
                observed_at_unix_ns=empty_final_unix_ns,
                observed_at_monotonic_ns=empty_final_monotonic_ns,
            )
            self.assertEqual(ledger.final_answer_agent_messages, {})

            ledger._reconcile_suppressed_waits_for_successor(
                thread_id="root-thread",
                turn_id="root-turn",
                successor_response_id=successor_response_id,
            )
            self.assertEqual(gate.suppressed_bindings, [])
            self.assertEqual(ledger.suppressed_collaboration_wait_evidence, {})

            ledger._reconcile_superseded_responses_for_successor(
                thread_id="root-thread",
                turn_id="root-turn",
                successor_response_id=successor_response_id,
            )
            self.assertEqual(
                gate.superseded_bindings,
                [
                    (
                        wait_response_id,
                        successor_response_id,
                    )
                ],
            )
            evidence = ledger.superseded_by_collaboration_message_evidence[
                wait_response_id
            ]
            self.assertEqual(
                evidence["collaboration_messages"][0]["item_id"],
                "amsg_019ffa8a-ee7a-7251-b10a-130edc3327cf",
            )

        # Zero FINAL results remain fail-closed if there is no exact MESSAGE
        # for the general supersession path to authenticate.
        with tempfile.TemporaryDirectory() as directory:
            ledger, gate = make_ledger(directory)
            ledger._reconcile_suppressed_waits_for_successor(
                thread_id="root-thread",
                turn_id="root-turn",
                successor_response_id=successor_response_id,
            )
            self.assertEqual(gate.suppressed_bindings, [])
            with self.assertRaisesRegex(
                RuntimeError, "nonempty collaboration-message batch"
            ):
                ledger._reconcile_superseded_responses_for_successor(
                    thread_id="root-thread",
                    turn_id="root-turn",
                    successor_response_id=successor_response_id,
                )

        # More than one eligible completed-child FINAL remains ambiguous and
        # must fail before either provider classification can be bound.
        with tempfile.TemporaryDirectory() as directory:
            ledger, gate = make_ledger(directory)
            ledger.threads["child-thread"].update(
                {
                    "turn_status": "completed",
                    "active_turn_id": None,
                    "terminal_turn_id": "child-turn",
                    "turn_completed_at_unix_ns": message_unix_ns - 2_000_000,
                    "turn_completed_at_monotonic_ns": message_monotonic_ns - 2,
                }
            )
            ledger._link_child(
                "root-thread", "second-child", "/root/library_search"
            )
            ledger.threads["second-child"].update(
                {
                    "provisional": False,
                    "spawn_binding_status": "resolved",
                    "turn_status": "completed",
                    "terminal_turn_id": "second-turn",
                    "turn_completed_at_unix_ns": message_unix_ns - 3_000_000,
                    "turn_completed_at_monotonic_ns": message_monotonic_ns - 3,
                }
            )
            for index, author in enumerate(
                ("/root/alternate_proof", "/root/library_search"), start=1
            ):
                ledger._capture_final_answer_agent_message(
                    thread_id="root-thread",
                    turn_id="root-turn",
                    item={
                        "type": "agent_message",
                        "id": f"amsg-job-1509972-final-{index}",
                        "author": author,
                        "recipient": "/root",
                        "content": [
                            {
                                "type": "input_text",
                                "text": (
                                    "Message Type: FINAL_ANSWER\n"
                                    "Task name: /root\n"
                                    f"Sender: {author}\n"
                                    "Payload:\nnonempty result"
                                ),
                            }
                        ],
                        "internal_chat_message_metadata_passthrough": {
                            "turn_id": "root-turn"
                        },
                    },
                    observed_at_unix_ns=message_unix_ns + index,
                    observed_at_monotonic_ns=message_monotonic_ns + index,
                )
            with self.assertRaisesRegex(
                RuntimeError, "one unique completed-child result"
            ):
                ledger._reconcile_suppressed_waits_for_successor(
                    thread_id="root-thread",
                    turn_id="root-turn",
                    successor_response_id=successor_response_id,
                )
            self.assertEqual(gate.suppressed_bindings, [])

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.output = self.root / "trusted" / "usage.json"

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def ledger(self, token_limit: int = 10_000) -> AttemptUsageLedger:
        return AttemptUsageLedger(self.output, token_limit, "root")

    def policy_ledger(self, token_limit: int = 10_000) -> AttemptUsageLedger:
        return AttemptUsageLedger(
            self.output,
            token_limit,
            "root",
            fork_policy=codex_isolated.ultra_fork_policy_static_record(
                "/u501/tester"
            ),
        )

    def runner_policy_ledger(self, token_limit: int = 10_000) -> AttemptUsageLedger:
        """Use the production in-namespace home for runner polling tests."""

        return AttemptUsageLedger(
            self.output,
            token_limit,
            "root",
            fork_policy=codex_isolated.ultra_fork_policy_static_record(
                "/u501/m2fetrat"
            ),
        )

    @staticmethod
    def threads_by_id(snapshot: dict[str, object]) -> dict[str, dict[str, object]]:
        threads = snapshot["threads"]
        assert isinstance(threads, list)
        return {
            str(thread["thread_id"]): thread
            for thread in threads
            if isinstance(thread, dict)
        }

    def test_raw_root_and_child_responses_are_summed_exactly_once(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(
            raw_function_call_event(
                "root", "root-turn", "spawn-child", fork_turns="none"
            )
        )
        ledger.observe(
            collab_spawn_event(
                "root", "root-turn", "spawn-child", "child"
            )
        )
        ledger.observe(
            subagent_started_event(
                "root",
                "child",
                "root/algebra",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        ledger.observe(
            turn_event("turn/started", "child", "child-turn", "inProgress")
        )
        self.assertFalse(
            ledger.observe(
                raw_response_event(
                    "response-root",
                    "root",
                    "root-turn",
                    input_tokens=10,
                    cached_input_tokens=4,
                    cache_write_input_tokens=1,
                    output_tokens=3,
                    reasoning_output_tokens=2,
                )
            )
        )
        self.assertFalse(
            ledger.observe(
                raw_response_event(
                    "response-child",
                    "child",
                    "child-turn",
                    input_tokens=20,
                    cached_input_tokens=7,
                    cache_write_input_tokens=2,
                    output_tokens=5,
                    reasoning_output_tokens=4,
                )
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=10,
                cached_input_tokens=4,
                cache_write_input_tokens=1,
                output_tokens=3,
                reasoning_output_tokens=2,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=20,
                cached_input_tokens=7,
                cache_write_input_tokens=2,
                output_tokens=5,
                reasoning_output_tokens=4,
            )
        )
        ledger.observe(turn_event("turn/completed", "child", "child-turn", "completed"))
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))

        snapshot = ledger.snapshot(drain_complete=ledger.quiescent())
        self.assertEqual(
            {
                field: snapshot[field]
                for field in (
                    "input_tokens",
                    "cached_input_tokens",
                    "cache_write_input_tokens",
                    "output_tokens",
                    "reasoning_output_tokens",
                    "total_tokens",
                )
            },
            {
                "input_tokens": 30,
                "cached_input_tokens": 11,
                "cache_write_input_tokens": 3,
                "output_tokens": 8,
                "reasoning_output_tokens": 6,
                "total_tokens": 38,
            },
        )
        self.assertEqual(snapshot["thread_count"], 2)
        self.assertEqual(snapshot["response_count"], 2)
        self.assertEqual(snapshot["response_ids"], ["response-root", "response-child"])
        self.assertTrue(snapshot["measurement_exact"])
        threads = self.threads_by_id(snapshot)
        self.assertEqual(threads["root"]["total_tokens"], 13)
        self.assertEqual(threads["child"]["total_tokens"], 25)
        self.assertEqual(threads["child"]["parent_thread_id"], "root")
        self.assertEqual(threads["child"]["agent_path"], "root/algebra")
        self.assertEqual(
            threads["child"]["expected_cumulative_baseline"],
            {field: 0 for field in AttemptUsageLedger._SUM_FIELDS},
        )
        self.assertTrue(snapshot["spawn_linkage_complete"])
        self.assertTrue(snapshot["cumulative_projection_complete"])
        self.assertTrue(snapshot["accounting_complete"])

    def test_duplicate_response_id_is_idempotent_but_conflict_is_rejected(self) -> None:
        ledger = self.ledger()
        event = raw_response_event(
            "response-1",
            "root",
            "turn-1",
            input_tokens=9,
            cached_input_tokens=3,
            output_tokens=2,
            reasoning_output_tokens=1,
        )
        self.assertFalse(ledger.observe(event))
        self.assertFalse(ledger.observe(event))
        snapshot = ledger.snapshot()
        self.assertEqual(snapshot["response_count"], 1)
        self.assertEqual(snapshot["notification_sequence"], 1)
        self.assertEqual(snapshot["total_tokens"], 11)

        conflicting = raw_response_event(
            "response-1",
            "root",
            "turn-1",
            input_tokens=9,
            cached_input_tokens=3,
            output_tokens=3,
            reasoning_output_tokens=1,
        )
        with self.assertRaisesRegex(RuntimeError, "reused a response id"):
            ledger.observe(conflicting)
        self.assertEqual(ledger.snapshot()["total_tokens"], 11)

    def test_null_and_malformed_raw_usage_fail_closed(self) -> None:
        invalid_events: list[dict[str, object]] = [
            {
                "method": "rawResponse/completed",
                "params": {
                    "responseId": "null-usage",
                    "threadId": "root",
                    "turnId": "turn",
                    "usage": None,
                },
            },
            {
                "method": "rawResponse/completed",
                "params": {
                    "responseId": "missing-identity",
                    "threadId": "root",
                    "usage": {},
                },
            },
            {
                "method": "rawResponse/completed",
                "params": {
                    "responseId": "boolean-token",
                    "threadId": "root",
                    "turnId": "turn",
                    "usage": {
                        "inputTokens": True,
                        "cachedInputTokens": 0,
                        "cacheWriteInputTokens": 0,
                        "outputTokens": 0,
                        "reasoningOutputTokens": 0,
                        "totalTokens": 1,
                    },
                },
            },
            {
                "method": "rawResponse/completed",
                "params": {
                    "responseId": "bad-total",
                    "threadId": "root",
                    "turnId": "turn",
                    "usage": {
                        "inputTokens": 4,
                        "cachedInputTokens": 1,
                        "cacheWriteInputTokens": 0,
                        "outputTokens": 2,
                        "reasoningOutputTokens": 1,
                        "totalTokens": 7,
                    },
                },
            },
        ]
        for event in invalid_events:
            with self.subTest(response=event.get("params")):
                ledger = self.ledger()
                with self.assertRaisesRegex(RuntimeError, "raw response"):
                    ledger.observe(event)
                self.assertEqual(ledger.snapshot()["response_count"], 0)

    def test_subagent_activity_discovers_recursive_parentage(self) -> None:
        ledger = self.ledger()
        ledger.observe(subagent_started_event("root", "child", "root/analysis"))
        ledger.observe(
            subagent_started_event("child", "grandchild", "root/analysis/check")
        )
        # A repeated delivery of the same activity is harmless.
        ledger.observe(subagent_started_event("root", "child", "root/analysis"))
        snapshot = ledger.snapshot()
        threads = self.threads_by_id(snapshot)
        self.assertEqual(snapshot["thread_count"], 3)
        self.assertEqual(threads["child"]["parent_thread_id"], "root")
        self.assertEqual(threads["grandchild"]["parent_thread_id"], "child")
        self.assertFalse(threads["child"]["provisional"])
        self.assertFalse(threads["grandchild"]["provisional"])
        with self.assertRaisesRegex(RuntimeError, "assigned two parents"):
            ledger.observe(
                subagent_started_event("root", "grandchild", "root/wrong-parent")
            )

    def test_provisional_raw_thread_is_promoted_when_activity_arrives(self) -> None:
        ledger = self.ledger()
        ledger.observe(
            raw_response_event(
                "early-child-response",
                "child",
                "child-turn",
                input_tokens=5,
                cached_input_tokens=1,
                output_tokens=2,
                reasoning_output_tokens=1,
            )
        )
        self.assertEqual(ledger.unresolved_thread_ids(), ["child"])
        self.assertFalse(ledger.snapshot()["measurement_exact"])

        ledger.observe(subagent_started_event("root", "child", "root/early-child"))
        self.assertEqual(ledger.unresolved_thread_ids(), [])
        child = self.threads_by_id(ledger.snapshot())["child"]
        self.assertFalse(child["provisional"])
        self.assertEqual(child["parent_thread_id"], "root")
        self.assertEqual(child["response_count"], 1)

    def test_job_1509399_child_status_before_activity_defers_live_publication(
        self,
    ) -> None:
        ledger = self.runner_policy_ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        baseline = self.output.read_bytes()
        benchmark_runner.read_token_usage(self.output)

        # Job 1509399 emitted this child status one event before the parent's
        # binding subAgentActivity.  Publishing that provisional child exposes
        # a null parent edge to the live runner.
        child_status = {
            "method": "thread/status/changed",
            "params": {
                "threadId": "child",
                "status": {"type": "idle"},
            },
        }
        ledger.observe(child_status)
        self.assertEqual(ledger.unresolved_thread_ids(), ["child"])
        self.assertEqual(self.output.read_bytes(), baseline)
        benchmark_runner.read_token_usage(self.output)

        ledger.observe(
            subagent_started_event(
                "root",
                "child",
                "root/library_search",
                parent_turn_id="root-turn",
                activity_id="call-child",
            )
        )
        published = benchmark_runner.read_token_usage(self.output)
        assert published is not None
        child = self.threads_by_id(
            json.loads(self.output.read_text(encoding="utf-8"))
        )["child"]
        self.assertEqual(child["parent_thread_id"], "root")
        self.assertFalse(child["provisional"])
        self.assertEqual(child["thread_status"], "idle")

        orphan_output = self.root / "trusted" / "orphan-usage.json"
        orphan = AttemptUsageLedger(
            orphan_output,
            10_000,
            "root",
            fork_policy=codex_isolated.ultra_fork_policy_static_record(
                "/u501/m2fetrat"
            ),
        )
        orphan.observe(
            turn_event("turn/started", "root", "root-turn", "inProgress")
        )
        orphan.observe(child_status)
        orphan.publish(drain_complete=True)
        final = json.loads(orphan_output.read_text(encoding="utf-8"))
        self.assertTrue(final["drain_complete"])
        self.assertEqual(final["unresolved_thread_ids"], ["child"])
        with self.assertRaisesRegex(
            benchmark_runner.BenchmarkToolError,
            "invalid parent edge",
        ):
            benchmark_runner.read_token_usage(orphan_output)

    def test_root_completion_is_not_quiescence_while_child_is_active(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(subagent_started_event("root", "child"))
        ledger.observe(
            turn_event("turn/started", "child", "child-turn", "inProgress")
        )
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        self.assertEqual(ledger.root_terminal_status(), "completed")
        self.assertEqual(ledger.active_turns(), {"child": "child-turn"})
        self.assertFalse(ledger.quiescent())

        ledger.observe(turn_event("turn/completed", "child", "child-turn", "completed"))
        self.assertTrue(ledger.quiescent())

    def test_second_root_turn_requires_explicit_provider_compaction_authority(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        with self.assertRaisesRegex(RuntimeError, "out of order"):
            ledger.authorize_provider_gate_compaction_canary()
        with self.assertRaisesRegex(RuntimeError, "inconsistent turn ids"):
            ledger.observe(
                turn_event(
                    "turn/started", "root", "unauthorized-second-turn", "inProgress"
                )
            )
        with self.assertRaisesRegex(RuntimeError, "second root-turn response"):
            ledger.observe(
                raw_response_event(
                    "unauthorized-second-response",
                    "root",
                    "unauthorized-second-turn",
                    input_tokens=5,
                    cached_input_tokens=1,
                    output_tokens=1,
                )
            )

    def test_full_history_child_baseline_is_parent_pre_spawn_response(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(
            raw_response_event(
                "root-prior",
                "root",
                "root-turn",
                input_tokens=40,
                cached_input_tokens=10,
                cache_write_input_tokens=2,
                output_tokens=6,
                reasoning_output_tokens=3,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=40,
                cached_input_tokens=10,
                cache_write_input_tokens=2,
                output_tokens=6,
                reasoning_output_tokens=3,
            )
        )
        ledger.observe(
            raw_function_call_event("root", "root-turn", "spawn-child")
        )
        ledger.observe(
            raw_response_event(
                "root-spawn",
                "root",
                "root-turn",
                input_tokens=7,
                cached_input_tokens=2,
                output_tokens=3,
                reasoning_output_tokens=1,
            )
        )
        # Exercise raw-before-link delivery: the normalized activity arrives
        # only after the exact parent response has closed.
        ledger.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        ledger.observe(turn_event("turn/started", "child", "child-turn", "inProgress"))
        ledger.observe(
            raw_response_event(
                "child-response-1",
                "child",
                "child-turn",
                input_tokens=10,
                cached_input_tokens=4,
                cache_write_input_tokens=1,
                output_tokens=5,
                reasoning_output_tokens=2,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=50,
                cached_input_tokens=14,
                cache_write_input_tokens=3,
                output_tokens=11,
                reasoning_output_tokens=5,
            )
        )
        expected_baseline = {
            "input_tokens": 40,
            "cached_input_tokens": 10,
            "cache_write_input_tokens": 2,
            "output_tokens": 6,
            "reasoning_output_tokens": 3,
            "total_tokens": 46,
        }
        self.assertEqual(
            self.threads_by_id(ledger.snapshot())["child"][
                "expected_cumulative_baseline"
            ],
            expected_baseline,
        )

        ledger.observe(
            raw_response_event(
                "child-response-2",
                "child",
                "child-turn",
                input_tokens=6,
                cached_input_tokens=1,
                output_tokens=4,
                reasoning_output_tokens=1,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=56,
                cached_input_tokens=15,
                cache_write_input_tokens=3,
                output_tokens=15,
                reasoning_output_tokens=6,
            )
        )
        child = self.threads_by_id(ledger.snapshot())["child"]
        self.assertEqual(child["cumulative_baseline"], expected_baseline)
        self.assertEqual(child["observed_cumulative_baseline"], expected_baseline)
        self.assertTrue(child["cumulative_baseline_matches_expected"])
        self.assertTrue(child["cumulative_projection_match"])

    def test_missing_child_raw_response_cannot_be_absorbed_into_baseline(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(
            raw_function_call_event(
                "root", "root-turn", "spawn-child", fork_turns="none"
            )
        )
        ledger.observe(
            raw_response_event(
                "root-spawn",
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=2,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=2,
            )
        )
        ledger.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        ledger.observe(turn_event("turn/started", "child", "child-turn", "inProgress"))
        ledger.observe(
            raw_response_event(
                "observed-child-response",
                "child",
                "child-turn",
                input_tokens=5,
                cached_input_tokens=1,
                output_tokens=2,
            )
        )
        # Seven input and three output tokens belong to an omitted raw response.
        # The former implementation accepted them as an arbitrary child baseline.
        ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=12,
                cached_input_tokens=2,
                output_tokens=5,
            )
        )
        ledger.observe(turn_event("turn/completed", "child", "child-turn", "completed"))
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        snapshot = ledger.snapshot(drain_complete=ledger.quiescent())
        child = self.threads_by_id(snapshot)["child"]
        self.assertEqual(
            child["expected_cumulative_baseline"],
            {field: 0 for field in AttemptUsageLedger._SUM_FIELDS},
        )
        self.assertEqual(child["observed_cumulative_baseline"]["input_tokens"], 7)
        self.assertEqual(child["observed_cumulative_baseline"]["output_tokens"], 3)
        self.assertFalse(child["cumulative_baseline_matches_expected"])
        self.assertFalse(child["cumulative_projection_match"])
        self.assertFalse(snapshot["descendant_accounting_complete"])
        self.assertFalse(snapshot["accounting_complete"])
        self.assertFalse(snapshot["measurement_exact"])

    def test_job_1509324_lagging_child_cumulative_has_no_invalid_baseline(
        self,
    ) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(
            raw_response_event(
                "root-prior",
                "root",
                "root-turn",
                input_tokens=24_819,
                cached_input_tokens=24_064,
                output_tokens=290,
                reasoning_output_tokens=74,
            )
        )
        ledger.observe(
            raw_function_call_event("root", "root-turn", "spawn-child")
        )
        ledger.observe(
            raw_response_event(
                "root-spawn",
                "root",
                "root-turn",
                input_tokens=1,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        ledger.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        ledger.observe(turn_event("turn/started", "child", "child-turn", "inProgress"))
        for index in range(5):
            ledger.observe(
                raw_response_event(
                    f"child-{index + 1}",
                    "child",
                    "child-turn",
                    input_tokens=12_000,
                    cached_input_tokens=11_000,
                    output_tokens=300,
                    reasoning_output_tokens=200,
                )
            )
        ledger.observe(
            raw_response_event(
                "child-6",
                "child",
                "child-turn",
                input_tokens=23_948,
                cached_input_tokens=19_240,
                output_tokens=652,
                reasoning_output_tokens=462,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=108_767,
                cached_input_tokens=98_304,
                output_tokens=2_442,
                reasoning_output_tokens=1_536,
            )
        )
        # The cumulative event is now one response behind.  Subtracting all
        # seven responses would leave input=9,570 and cached=9,984, which is
        # not a valid token breakdown and was the job 1509324 crash shape.
        ledger.observe(
            raw_response_event(
                "child-7",
                "child",
                "child-turn",
                input_tokens=15_249,
                cached_input_tokens=14_080,
                output_tokens=105,
                reasoning_output_tokens=74,
            )
        )

        child = self.threads_by_id(ledger.snapshot())["child"]
        self.assertIsNone(child["observed_cumulative_baseline"])
        self.assertFalse(child["cumulative_baseline_matches_expected"])
        self.assertFalse(child["cumulative_projection_match"])
        self.assertEqual(
            child["cumulative_projection_status"],
            "cumulative_projection_mismatch",
        )
        self.assertFalse(child["accounting_complete"])

    def test_recursive_grandchild_full_history_projection_resolves(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(
            raw_function_call_event(
                "root", "root-turn", "spawn-child", fork_turns="none"
            )
        )
        ledger.observe(
            raw_response_event(
                "root-spawn",
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        ledger.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "root", "root-turn", input_tokens=3, cached_input_tokens=1, output_tokens=1
            )
        )
        ledger.observe(turn_event("turn/started", "child", "child-turn", "inProgress"))
        ledger.observe(
            raw_response_event(
                "child-prior",
                "child",
                "child-turn",
                input_tokens=5,
                cached_input_tokens=2,
                output_tokens=2,
                reasoning_output_tokens=1,
            )
        )
        ledger.observe(
            raw_function_call_event("child", "child-turn", "spawn-grandchild")
        )
        ledger.observe(
            raw_response_event(
                "child-spawn",
                "child",
                "child-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        # Deliver the grandchild's own raw/cumulative stream before the collab
        # edge.  Recursive resolution must repair the ancestry once linked.
        ledger.observe(turn_event("turn/started", "grandchild", "grand-turn", "inProgress"))
        ledger.observe(
            raw_response_event(
                "grand-response",
                "grandchild",
                "grand-turn",
                input_tokens=6,
                cached_input_tokens=2,
                output_tokens=2,
                reasoning_output_tokens=1,
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "grandchild",
                "grand-turn",
                input_tokens=11,
                cached_input_tokens=4,
                output_tokens=4,
                reasoning_output_tokens=2,
            )
        )
        ledger.observe(
            subagent_started_event(
                "child",
                "grandchild",
                "root/child/grandchild",
                parent_turn_id="child-turn",
                activity_id="spawn-grandchild",
            )
        )
        ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=9,
                cached_input_tokens=3,
                output_tokens=3,
                reasoning_output_tokens=1,
            )
        )
        ledger.observe(turn_event("turn/completed", "grandchild", "grand-turn", "completed"))
        ledger.observe(turn_event("turn/completed", "child", "child-turn", "completed"))
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        snapshot = ledger.snapshot(drain_complete=ledger.quiescent())
        threads = self.threads_by_id(snapshot)
        self.assertEqual(
            threads["grandchild"]["expected_cumulative_baseline"],
            {
                "input_tokens": 5,
                "cached_input_tokens": 2,
                "cache_write_input_tokens": 0,
                "output_tokens": 2,
                "reasoning_output_tokens": 1,
                "total_tokens": 7,
            },
        )
        self.assertEqual(
            snapshot["resolved_spawn_call_ids"],
            ["spawn-child", "spawn-grandchild"],
        )
        self.assertTrue(snapshot["accounting_complete"])
        self.assertTrue(snapshot["measurement_exact"])

    def test_wrong_binding_positive_fork_and_unresolved_ancestry_fail_closed(self) -> None:
        wrong = self.ledger()
        wrong.observe(
            raw_function_call_event(
                "root",
                "root-turn",
                "wrong-call",
                name="wait_agent",
                namespace="collaboration",
            )
        )
        wrong.observe(
            raw_response_event(
                "wrong-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        wrong.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="wrong-call",
            )
        )
        wrong_snapshot = wrong.snapshot()
        self.assertIn("wrong-call", wrong_snapshot["unresolved_spawn_call_ids"])
        self.assertFalse(wrong_snapshot["spawn_linkage_complete"])
        self.assertTrue(any("non-spawn" in item for item in wrong_snapshot["invalid_reasons"]))

        mismatched = self.ledger()
        mismatched.observe(
            raw_function_call_event(
                "root", "root-turn", "raw-spawn-call", fork_turns="none"
            )
        )
        mismatched.observe(
            raw_response_event(
                "mismatch-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        mismatched.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="different-activity-id",
            )
        )
        mismatch_snapshot = mismatched.snapshot()
        self.assertEqual(
            mismatch_snapshot["unresolved_spawn_call_ids"],
            ["different-activity-id", "raw-spawn-call"],
        )
        self.assertIsNone(
            self.threads_by_id(mismatch_snapshot)["child"]["spawn_call_id"]
        )
        self.assertFalse(mismatch_snapshot["spawn_linkage_complete"])

        positive = self.ledger()
        positive.observe(
            raw_function_call_event(
                "root", "root-turn", "positive-call", fork_turns="3"
            )
        )
        positive.observe(
            raw_response_event(
                "positive-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        positive.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="positive-call",
            )
        )
        positive_snapshot = positive.snapshot()
        self.assertEqual(positive_snapshot["unsupported_spawn_call_ids"], ["positive-call"])
        self.assertIsNone(
            self.threads_by_id(positive_snapshot)["child"][
                "expected_cumulative_baseline"
            ]
        )
        self.assertFalse(positive_snapshot["accounting_complete"])

        invalid_fork = self.ledger()
        invalid_fork.observe(
            raw_function_call_event(
                "root", "root-turn", "invalid-fork-call", fork_turns="0"
            )
        )
        invalid_fork.observe(
            raw_response_event(
                "invalid-fork-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        invalid_fork.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="invalid-fork-call",
            )
        )
        invalid_fork_snapshot = invalid_fork.snapshot()
        self.assertEqual(
            invalid_fork.raw_spawn_calls["invalid-fork-call"]["resolution_status"],
            "invalid_fork_turns",
        )
        self.assertFalse(invalid_fork_snapshot["measurement_exact"])

        ancestry = self.ledger()
        ancestry.observe(
            subagent_started_event(
                "root", "child", parent_turn_id="root-turn"
            )
        )
        ancestry.observe(
            raw_function_call_event("child", "child-turn", "nested-call")
        )
        ancestry.observe(
            raw_response_event(
                "nested-response",
                "child",
                "child-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        ancestry.observe(
            subagent_started_event(
                "child",
                "grandchild",
                parent_turn_id="child-turn",
                activity_id="nested-call",
            )
        )
        ancestry_snapshot = ancestry.snapshot()
        self.assertEqual(
            ancestry.raw_spawn_calls["nested-call"]["resolution_status"],
            "unresolved_parent_baseline",
        )
        self.assertIsNone(
            self.threads_by_id(ancestry_snapshot)["grandchild"][
                "expected_cumulative_baseline"
            ]
        )
        self.assertFalse(ancestry_snapshot["spawn_linkage_complete"])

    def test_authenticated_positive_block_then_all_child_is_exact_across_event_orders(
        self,
    ) -> None:
        for hook_before_response, completed_before_started in (
            (False, False),
            (True, False),
            (False, True),
            (True, True),
        ):
            with self.subTest(
                hook_before_response=hook_before_response,
                completed_before_started=completed_before_started,
            ):
                ledger = self.policy_ledger()
                ledger.observe(
                    turn_event("turn/started", "root", "root-turn", "inProgress")
                )

                def hook_pair(call_id: str, decision: str) -> list[dict[str, object]]:
                    pair = [
                        fork_policy_hook_event(
                            codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                            call_id,
                            "root",
                            "root-turn",
                            decision=decision,
                        ),
                        fork_policy_hook_event(
                            codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                            call_id,
                            "root",
                            "root-turn",
                            decision=decision,
                        ),
                    ]
                    return list(reversed(pair)) if completed_before_started else pair

                ledger.observe(
                    raw_function_call_event(
                        "root", "root-turn", "call_positive", fork_turns="3"
                    )
                )
                positive_hooks = hook_pair(
                    "call_positive", codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
                )
                if hook_before_response:
                    for event in positive_hooks:
                        ledger.observe(event)
                ledger.observe(
                    raw_response_event(
                        "positive-response",
                        "root",
                        "root-turn",
                        input_tokens=2,
                        cached_input_tokens=1,
                        output_tokens=1,
                    )
                )
                if not hook_before_response:
                    for event in positive_hooks:
                        ledger.observe(event)
                ledger.observe(
                    cumulative_usage_event(
                        "root",
                        "root-turn",
                        input_tokens=2,
                        cached_input_tokens=1,
                        output_tokens=1,
                    )
                )

                ledger.observe(
                    raw_function_call_event(
                        "root", "root-turn", "call_all", fork_turns="all"
                    )
                )
                allow_hooks = hook_pair(
                    "call_all", codex_isolated.ULTRA_FORK_POLICY_ALLOW_DECISION
                )
                if hook_before_response:
                    for event in allow_hooks:
                        ledger.observe(event)
                ledger.observe(
                    raw_response_event(
                        "allow-response",
                        "root",
                        "root-turn",
                        input_tokens=4,
                        cached_input_tokens=1,
                        output_tokens=2,
                    )
                )
                if not hook_before_response:
                    for event in allow_hooks:
                        ledger.observe(event)
                ledger.observe(
                    subagent_started_event(
                        "root",
                        "child",
                        parent_turn_id="root-turn",
                        activity_id="call_all",
                    )
                )
                ledger.observe(
                    cumulative_usage_event(
                        "root",
                        "root-turn",
                        input_tokens=6,
                        cached_input_tokens=2,
                        output_tokens=3,
                    )
                )
                ledger.observe(
                    turn_event("turn/started", "child", "child-turn", "inProgress")
                )
                ledger.observe(
                    raw_response_event(
                        "child-response",
                        "child",
                        "child-turn",
                        input_tokens=3,
                        cached_input_tokens=1,
                        output_tokens=1,
                    )
                )
                ledger.observe(
                    cumulative_usage_event(
                        "child",
                        "child-turn",
                        input_tokens=5,
                        cached_input_tokens=2,
                        output_tokens=2,
                    )
                )
                ledger.observe(
                    turn_event("turn/completed", "child", "child-turn", "completed")
                )
                ledger.observe(
                    turn_event("turn/completed", "root", "root-turn", "completed")
                )
                snapshot = ledger.snapshot(drain_complete=ledger.quiescent())
                self.assertEqual(
                    snapshot["accounting_projection_schema_version"],
                    codex_isolated.ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION,
                )
                self.assertEqual(
                    snapshot["hook_observed_spawn_call_ids"],
                    ["call_all", "call_positive"],
                )
                self.assertEqual(snapshot["hook_allowed_spawn_call_ids"], ["call_all"])
                self.assertEqual(
                    snapshot["hook_blocked_spawn_call_ids"], ["call_positive"]
                )
                self.assertEqual(snapshot["policy_blocked_spawn_call_ids"], ["call_positive"])
                self.assertEqual(snapshot["hook_invalid_spawn_call_ids"], [])
                self.assertEqual(snapshot["unsupported_spawn_call_ids"], [])
                self.assertEqual(snapshot["unresolved_spawn_call_ids"], [])
                self.assertTrue(snapshot["fork_policy_complete"])
                self.assertTrue(snapshot["spawn_linkage_complete"])
                self.assertTrue(snapshot["accounting_complete"])
                self.assertTrue(snapshot["measurement_exact"])
                evidence = {
                    item["call_id"]: item
                    for item in snapshot["fork_policy"]["call_evidence"]
                }
                self.assertEqual(evidence["call_positive"]["decision"], "block")
                self.assertEqual(
                    evidence["call_positive"]["resolution_status"],
                    codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS,
                )
                self.assertEqual(evidence["call_all"]["decision"], "allow")
                self.assertEqual(
                    evidence["call_all"]["resolution_status"], "resolved_child"
                )

    def test_fork_hook_publication_waits_for_actual_job_order_raw_response_index(
        self,
    ) -> None:
        ledger = self.runner_policy_ledger()
        call_id = "call_actual_job_order"
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        baseline = self.output.read_bytes()
        benchmark_runner.read_token_usage(self.output)

        # Job 1508007 emitted the raw spawn item, hook start, enclosing raw
        # response, then hook completion.  The item is retained immediately but
        # cannot be indexed as a spawn until the response supplies its identity
        # and exact usage.
        ledger.observe(
            raw_function_call_event(
                "root", "root-turn", call_id, fork_turns="all"
            )
        )
        self.assertEqual(self.output.read_bytes(), baseline)
        benchmark_runner.read_token_usage(self.output)

        ledger.observe(
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                call_id,
                "root",
                "root-turn",
                inside_home="/u501/m2fetrat",
            )
        )
        self.assertEqual(self.output.read_bytes(), baseline)
        benchmark_runner.read_token_usage(self.output)

        ledger.observe(
            raw_response_event(
                "actual-job-response",
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=2,
            )
        )
        partial = benchmark_runner.read_token_usage(self.output)
        assert partial is not None
        self.assertEqual(partial["raw_spawn_call_ids"], [call_id])
        self.assertEqual(partial["hook_observed_spawn_call_ids"], [call_id])
        self.assertEqual(partial["hook_invalid_spawn_call_ids"], [])
        evidence = partial["fork_policy"]["call_evidence"][0]
        self.assertEqual(evidence["hook_started_count"], 1)
        self.assertEqual(evidence["hook_completed_count"], 0)
        self.assertEqual(
            evidence["resolution_status"],
            codex_isolated.ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS,
        )

        ledger.observe(
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                call_id,
                "root",
                "root-turn",
                inside_home="/u501/m2fetrat",
            )
        )
        terminal = benchmark_runner.read_token_usage(self.output)
        assert terminal is not None
        self.assertEqual(terminal["hook_allowed_spawn_call_ids"], [call_id])
        self.assertEqual(terminal["hook_invalid_spawn_call_ids"], [])
        terminal_evidence = terminal["fork_policy"]["call_evidence"][0]
        self.assertEqual(terminal_evidence["hook_started_count"], 1)
        self.assertEqual(terminal_evidence["hook_completed_count"], 1)
        self.assertEqual(
            terminal_evidence["resolution_status"],
            codex_isolated.ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS,
        )

    def test_fork_hook_pair_before_response_stays_unpublished_in_both_orders(
        self,
    ) -> None:
        for completed_first in (False, True):
            with self.subTest(completed_first=completed_first):
                ledger = self.runner_policy_ledger()
                call_id = "call_pair_before_response"
                ledger.observe(
                    turn_event("turn/started", "root", "root-turn", "inProgress")
                )
                baseline = self.output.read_bytes()
                ledger.observe(
                    raw_function_call_event(
                        "root", "root-turn", call_id, fork_turns="3"
                    )
                )
                self.assertEqual(self.output.read_bytes(), baseline)
                benchmark_runner.read_token_usage(self.output)

                pair = [
                    fork_policy_hook_event(
                        codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                        call_id,
                        "root",
                        "root-turn",
                        inside_home="/u501/m2fetrat",
                        decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
                    ),
                    fork_policy_hook_event(
                        codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                        call_id,
                        "root",
                        "root-turn",
                        inside_home="/u501/m2fetrat",
                        decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
                    ),
                ]
                if completed_first:
                    pair.reverse()
                for event in pair:
                    ledger.observe(event)
                    self.assertEqual(self.output.read_bytes(), baseline)
                    benchmark_runner.read_token_usage(self.output)

                ledger.observe(
                    raw_response_event(
                        "pair-before-response",
                        "root",
                        "root-turn",
                        input_tokens=2,
                        cached_input_tokens=0,
                        output_tokens=1,
                    )
                )
                published = benchmark_runner.read_token_usage(self.output)
                assert published is not None
                self.assertEqual(published["raw_spawn_call_ids"], [call_id])
                self.assertEqual(published["hook_blocked_spawn_call_ids"], [call_id])
                self.assertEqual(published["hook_invalid_spawn_call_ids"], [])
                self.assertTrue(published["fork_policy_complete"])
                self.assertTrue(published["spawn_linkage_complete"])

    def test_truly_orphaned_fork_hook_is_published_fail_closed_at_final_drain(
        self,
    ) -> None:
        ledger = self.runner_policy_ledger()
        call_id = "call_orphaned_at_exit"
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        baseline = self.output.read_bytes()
        for method in (
            codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
            codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
        ):
            ledger.observe(
                fork_policy_hook_event(
                    method,
                    call_id,
                    "root",
                    "root-turn",
                    inside_home="/u501/m2fetrat",
                )
            )
            self.assertEqual(self.output.read_bytes(), baseline)
            benchmark_runner.read_token_usage(self.output)
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        self.assertEqual(self.output.read_bytes(), baseline)

        ledger.publish(drain_complete=True)
        final = json.loads(self.output.read_text(encoding="utf-8"))
        self.assertTrue(final["drain_complete"])
        self.assertFalse(final["measurement_exact"])
        self.assertFalse(final["fork_policy_complete"])
        self.assertFalse(final["accounting_complete"])
        self.assertEqual(final["raw_spawn_call_ids"], [])
        self.assertEqual(final["hook_invalid_spawn_call_ids"], [call_id])
        with self.assertRaises(benchmark_runner.BenchmarkToolError):
            benchmark_runner.read_token_usage(self.output)

    def test_deferred_hook_publication_preserves_other_hook_failures(self) -> None:
        for failure in ("duplicate", "malformed", "cross-thread"):
            with self.subTest(failure=failure):
                ledger = self.runner_policy_ledger()
                call_id = f"call_{failure.replace('-', '_')}"
                ledger.observe(
                    turn_event("turn/started", "root", "root-turn", "inProgress")
                )
                ledger.observe(
                    raw_function_call_event(
                        "root", "root-turn", call_id, fork_turns="3"
                    )
                )
                ledger.observe(
                    raw_response_event(
                        f"response-{failure}",
                        "root",
                        "root-turn",
                        input_tokens=2,
                        cached_input_tokens=0,
                        output_tokens=1,
                    )
                )
                started = fork_policy_hook_event(
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                    call_id,
                    "other-thread" if failure == "cross-thread" else "root",
                    "root-turn",
                    inside_home="/u501/m2fetrat",
                    decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
                    status="completed" if failure == "malformed" else None,
                )
                ledger.observe(started)
                if failure == "duplicate":
                    ledger.observe(started)
                ledger.observe(
                    fork_policy_hook_event(
                        codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                        call_id,
                        "other-thread" if failure == "cross-thread" else "root",
                        "root-turn",
                        inside_home="/u501/m2fetrat",
                        decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
                    )
                )
                ledger.observe(
                    turn_event("turn/completed", "root", "root-turn", "completed")
                )
                ledger.publish(drain_complete=True)
                final = json.loads(self.output.read_text(encoding="utf-8"))
                self.assertFalse(final["measurement_exact"])
                self.assertFalse(final["fork_policy_complete"])
                self.assertFalse(final["accounting_complete"])
                self.assertEqual(final["hook_invalid_spawn_call_ids"], [call_id])
                self.assertTrue(final["invalid_reasons"])

    def test_fork_policy_missing_failed_tampered_and_child_after_block_fail_closed(
        self,
    ) -> None:
        def raw_positive(ledger: AttemptUsageLedger, call_id: str) -> None:
            ledger.observe(
                raw_function_call_event(
                    "root", "root-turn", call_id, fork_turns="3"
                )
            )
            ledger.observe(
                raw_response_event(
                    f"response-{call_id}",
                    "root",
                    "root-turn",
                    input_tokens=2,
                    cached_input_tokens=0,
                    output_tokens=1,
                )
            )

        missing = self.policy_ledger()
        raw_positive(missing, "call_missing")
        missing_snapshot = missing.snapshot()
        self.assertFalse(missing_snapshot["fork_policy_complete"])
        self.assertEqual(missing_snapshot["hook_observed_spawn_call_ids"], [])
        self.assertEqual(missing_snapshot["hook_invalid_spawn_call_ids"], [])
        self.assertEqual(missing_snapshot["unsupported_spawn_call_ids"], ["call_missing"])
        missing_evidence = missing_snapshot["fork_policy"]["call_evidence"][0]
        self.assertEqual(missing_evidence["hook_started_count"], 0)
        self.assertEqual(missing_evidence["hook_completed_count"], 0)
        self.assertIsNone(missing_evidence["hook_status"])
        self.assertIsNone(missing_evidence["decision"])
        self.assertIsNone(missing_evidence["feedback"])
        self.assertEqual(
            missing_evidence["resolution_status"],
            codex_isolated.ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS,
        )

        failed = self.policy_ledger()
        raw_positive(failed, "call_failed")
        failed.observe(
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                "call_failed",
                "root",
                "root-turn",
            )
        )
        failed.observe(
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                "call_failed",
                "root",
                "root-turn",
                status="failed",
                entries=[{"kind": "error", "text": "helper failed"}],
            )
        )
        failed_snapshot = failed.snapshot()
        self.assertEqual(failed_snapshot["hook_invalid_spawn_call_ids"], ["call_failed"])
        self.assertFalse(failed_snapshot["fork_policy_complete"])
        self.assertFalse(failed_snapshot["accounting_complete"])

        tampered = self.policy_ledger()
        raw_positive(tampered, "call_tampered")
        expected_source = tampered.fork_policy_static["source_path"]
        assert isinstance(expected_source, str)
        expected_run_id = f"pre-tool-use:0:{expected_source}:call_tampered"
        tampered.observe(
            fork_policy_hook_event(
                codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                "call_tampered",
                "root",
                "root-turn",
                source_path="/tampered/hooks.json",
                run_id=expected_run_id,
            )
        )
        tampered_snapshot = tampered.snapshot()
        self.assertEqual(
            tampered_snapshot["hook_invalid_spawn_call_ids"], ["call_tampered"]
        )
        self.assertFalse(tampered_snapshot["fork_policy_complete"])

        escaped = self.policy_ledger()
        raw_positive(escaped, "call_escaped")
        for method in (
            codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
            codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
        ):
            escaped.observe(
                fork_policy_hook_event(
                    method,
                    "call_escaped",
                    "root",
                    "root-turn",
                    decision=codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION,
                )
            )
        escaped.observe(
            subagent_started_event(
                "root",
                "child",
                parent_turn_id="root-turn",
                activity_id="call_escaped",
            )
        )
        escaped_snapshot = escaped.snapshot()
        self.assertEqual(escaped_snapshot["hook_blocked_spawn_call_ids"], [])
        self.assertEqual(escaped_snapshot["hook_invalid_spawn_call_ids"], ["call_escaped"])
        self.assertEqual(escaped_snapshot["inference_child_thread_ids"], ["child"])
        self.assertFalse(escaped_snapshot["measurement_exact"])

    def test_natural_exactness_requires_final_cumulative_projection(self) -> None:
        exact = self.ledger()
        exact.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        exact.observe(
            raw_response_event(
                "root-response",
                "root",
                "root-turn",
                input_tokens=8,
                cached_input_tokens=3,
                output_tokens=2,
            )
        )
        exact.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=8,
                cached_input_tokens=3,
                output_tokens=2,
            )
        )
        exact.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        self.assertTrue(exact.snapshot(drain_complete=exact.quiescent())["measurement_exact"])

        missing = self.ledger()
        missing.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        missing.observe(
            raw_response_event(
                "root-response",
                "root",
                "root-turn",
                input_tokens=8,
                cached_input_tokens=3,
                output_tokens=2,
            )
        )
        missing.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        missing_snapshot = missing.snapshot(drain_complete=missing.quiescent())
        self.assertTrue(missing_snapshot["drain_complete"])
        self.assertFalse(missing_snapshot["cumulative_projection_complete"])
        self.assertFalse(missing_snapshot["measurement_exact"])

    def test_aggregate_cap_crosses_once_across_concurrent_threads(self) -> None:
        ledger = self.ledger(token_limit=20)
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(subagent_started_event("root", "child"))
        ledger.observe(
            turn_event("turn/started", "child", "child-turn", "inProgress")
        )
        self.assertFalse(
            ledger.observe(
                raw_response_event(
                    "root-response",
                    "root",
                    "root-turn",
                    input_tokens=8,
                    cached_input_tokens=2,
                    output_tokens=3,
                    reasoning_output_tokens=1,
                )
            )
        )
        self.assertTrue(
            ledger.observe(
                raw_response_event(
                    "child-crossing-response",
                    "child",
                    "child-turn",
                    input_tokens=7,
                    cached_input_tokens=2,
                    output_tokens=2,
                    reasoning_output_tokens=1,
                )
            )
        )
        first_crossing = ledger.snapshot()["first_crossing"]
        self.assertEqual(
            first_crossing,
            {
                "response_id": "child-crossing-response",
                "notification_sequence": 2,
                "observed_at_unix_ns": first_crossing["observed_at_unix_ns"],
                "tokens": 20,
                "active_thread_ids": ["child", "root"],
            },
        )
        self.assertFalse(
            ledger.observe(
                raw_response_event(
                    "post-crossing-response",
                    "child",
                    "child-turn",
                    input_tokens=1,
                    cached_input_tokens=0,
                    output_tokens=1,
                )
            )
        )
        snapshot = ledger.snapshot()
        self.assertEqual(snapshot["total_tokens"], 22)
        self.assertEqual(snapshot["stop_reason"], "token_limit")
        self.assertEqual(snapshot["first_crossing"], first_crossing)

    def test_quiescence_requires_resolved_threads_and_interrupt_acks(self) -> None:
        ledger = self.ledger()
        ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        ledger.observe(turn_event("turn/completed", "root", "root-turn", "completed"))
        self.assertTrue(ledger.quiescent())

        ledger.mark_interrupt_request(1000)
        self.assertFalse(ledger.quiescent())
        self.assertFalse(ledger.observe_interrupt_response({"id": 999, "result": {}}))
        self.assertTrue(ledger.observe_interrupt_response({"id": 1000, "result": {}}))
        self.assertTrue(ledger.quiescent())

        ledger.observe(
            raw_response_event(
                "unlinked-response",
                "late-child",
                "late-turn",
                input_tokens=1,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        self.assertFalse(ledger.quiescent())
        ledger.observe(subagent_started_event("root", "late-child", "root/late"))
        self.assertFalse(ledger.quiescent())
        ledger.observe(
            turn_event("turn/started", "late-child", "late-turn", "inProgress")
        )
        ledger.observe(
            turn_event("turn/completed", "late-child", "late-turn", "completed")
        )
        self.assertTrue(ledger.quiescent())


class SubmissionBarrierTests(unittest.TestCase):
    class Reader:
        def __init__(self) -> None:
            self.messages: queue.Queue[dict[str, object]] = queue.Queue()

        def get(self, timeout: float | None = None) -> dict[str, object]:
            return self.messages.get(timeout=timeout)

        def get_nowait(self) -> dict[str, object]:
            return self.messages.get_nowait()

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.usage = self.root / "trusted" / "usage.json"
        paths = codex_isolated.submission_barrier_paths(self.usage)
        paths["challenge"].parent.mkdir(parents=True)
        paths["challenge"].write_text(
            json.dumps(
                codex_isolated.authenticated_record(
                    {
                        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                        "kind": "highambench_submission_challenge",
                        "run_id": "unit-run",
                        "attempt_nonce": "unit-nonce",
                        "validator_contract_sha256": "b" * 64,
                        **codex_isolated.nested_submission_exec_yield_record(),
                    },
                    "challenge_sha256",
                )
            )
            + "\n",
            encoding="utf-8",
        )
        self.ledger = AttemptUsageLedger(self.usage, 10_000, "root")
        self.ledger.observe(
            turn_event("turn/started", "root", "root-turn", "inProgress")
        )
        self.protocol_input = io.StringIO()
        self.reader = self.Reader()
        self.barrier = codex_isolated.SubmissionBarrier(
            workspace=self.workspace,
            usage_output=self.usage,
            ledger=self.ledger,
            protocol_input=self.protocol_input,
            protocol_reader=self.reader,  # type: ignore[arg-type]
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def request(call_id: str = "call-1", thread_id: str = "root") -> dict[str, object]:
        return {
            "id": 44,
            "method": "item/tool/call",
            "params": {
                "threadId": thread_id,
                "turnId": "root-turn",
                "callId": call_id,
                "namespace": None,
                "tool": "submit_proof",
                "arguments": {"candidate_path": "Candidate.lean"},
            },
        }

    @staticmethod
    def raw_item(call_id: str) -> dict[str, object]:
        return {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": "function_call",
                    "id": "raw-" + call_id,
                    "name": "submit_proof",
                    "arguments": json.dumps({"candidate_path": "Candidate.lean"}),
                    "call_id": call_id,
                },
            },
        }

    @staticmethod
    def nested_raw_item(
        outer_call_id: str = "outer-call-1",
        source: str = codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
    ) -> dict[str, object]:
        return {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": "custom_tool_call",
                    "id": "raw-" + outer_call_id,
                    "name": "exec",
                    "status": "completed",
                    "call_id": outer_call_id,
                    "input": source,
                },
            },
        }

    @staticmethod
    def prior_exec_raw_item(
        call_id: str = "prior-outer-call",
        item_id: str = "prior-outer-item",
    ) -> dict[str, object]:
        return {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": "custom_tool_call",
                    "id": item_id,
                    "status": "completed",
                    "call_id": call_id,
                    "name": "exec",
                    "input": "const r = await tools.exec_command({});\n",
                },
            },
        }

    @staticmethod
    def delayed_exec_output(
        call_id: str = "prior-outer-call",
        item_id: str = "prior-output-item",
        *,
        metadata_turn_id: str = "root-turn",
    ) -> dict[str, object]:
        return {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": "custom_tool_call_output",
                    "id": item_id,
                    "call_id": call_id,
                    "output": "prior trusted output",
                    "internal_chat_message_metadata_passthrough": {
                        "turn_id": metadata_turn_id
                    },
                },
            },
        }

    @staticmethod
    def delayed_function_output(
        call_id: str = "prior-function-call",
        item_id: str = "prior-function-output",
        *,
        metadata_turn_id: str = "root-turn",
        output_type: str = "function_call_output",
    ) -> dict[str, object]:
        return {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": output_type,
                    "id": item_id,
                    "call_id": call_id,
                    "output": "prior collaboration output",
                    "internal_chat_message_metadata_passthrough": {
                        "turn_id": metadata_turn_id
                    },
                },
            },
        }

    @staticmethod
    def reasoning_raw_item(item_id: str = "submit-reasoning") -> dict[str, object]:
        return {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": "reasoning",
                    "id": item_id,
                    "summary": [],
                    "content": None,
                    "encrypted_content": "opaque",
                },
            },
        }

    @staticmethod
    def dynamic_start(call_id: str, thread_id: str = "root") -> dict[str, object]:
        return {
            "method": "item/started",
            "params": {
                "threadId": thread_id,
                "turnId": "root-turn",
                "item": {
                    "type": "dynamicToolCall",
                    "id": call_id,
                    "namespace": None,
                    "tool": "submit_proof",
                    "arguments": {"candidate_path": "Candidate.lean"},
                    "status": "inProgress",
                },
            },
        }

    def stage_nested_call(
        self,
        call_id: str,
        *,
        outer_call_id: str | None = None,
        source: str = codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
    ) -> dict[str, object]:
        self.ledger.observe(
            self.nested_raw_item(outer_call_id or "outer-" + call_id, source)
        )
        self.ledger.observe(self.dynamic_start(call_id))
        request = self.request(call_id)
        self.assertTrue(self.barrier.capture(request))
        return request

    def write_ack_when_requested(self, decision: str) -> threading.Thread:
        def worker() -> None:
            paths = codex_isolated.submission_barrier_paths(self.usage)
            deadline = time.monotonic() + 2
            while not paths["request"].exists():
                if time.monotonic() >= deadline:
                    return
                time.sleep(0.005)
            request = json.loads(paths["request"].read_text(encoding="utf-8"))
            ack = codex_isolated.authenticated_record(
                {
                    "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                    "kind": "highambench_submission_ack",
                    "sequence": request["sequence"],
                    "request_sha256": request["request_sha256"],
                    "candidate_sha256": request["candidate_sha256"],
                    "decision": decision,
                    "note": "accepted" if decision == "accept" else "repair",
                    "validator_accepted_at_unix_ns": time.time_ns(),
                    "validator_accepted_elapsed_seconds": 0.1,
                },
                "ack_sha256",
            )
            temporary = Path(str(paths["ack"]) + ".writer")
            temporary.write_text(json.dumps(ack) + "\n", encoding="utf-8")
            os.replace(temporary, paths["ack"])

        thread = threading.Thread(target=worker)
        thread.start()
        return thread

    def complete_raw(self, response_id: str, call_id: str) -> None:
        self.ledger.observe(
            raw_response_event(
                response_id,
                "root",
                "root-turn",
                input_tokens=10,
                cached_input_tokens=2,
                output_tokens=3,
                reasoning_output_tokens=2,
            )
        )

    def complete_nested_raw(
        self,
        response_id: str = "response-1",
        outer_call_id: str = "outer-call-1",
        source: str = codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
    ) -> None:
        self.ledger.observe(self.nested_raw_item(outer_call_id, source))
        self.ledger.observe(
            raw_response_event(
                response_id,
                "root",
                "root-turn",
                input_tokens=10,
                cached_input_tokens=2,
                output_tokens=3,
                reasoning_output_tokens=2,
            )
        )

    def test_accepts_actual_nested_exec_wire_and_binds_both_call_ids(self) -> None:
        candidate = b"theorem candidate : True := by trivial\n"
        (self.workspace / "Candidate.lean").write_bytes(candidate)
        self.stage_nested_call(
            "inner-dynamic-call", outer_call_id="outer-provider-call"
        )
        source = codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE
        self.complete_raw("nested-response", "inner-dynamic-call")
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaises(codex_isolated._SubmissionAccepted):
            self.barrier.advance()
        ack_thread.join(timeout=2)
        # Acceptance leaves the inner dynamic call unanswered, which also
        # prevents an outer exec output and any later provider response.
        self.assertEqual(self.protocol_input.getvalue(), "")
        paths = codex_isolated.submission_barrier_paths(self.usage, 1)
        request = json.loads(paths["request"].read_text(encoding="utf-8"))
        self.assertEqual(request["call_id"], "inner-dynamic-call")
        self.assertEqual(request["outer_exec_call_id"], "outer-provider-call")
        self.assertEqual(request["response_id"], "nested-response")
        self.assertEqual(
            request["submission_transport"],
            codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
        )
        self.assertEqual(request["outer_exec_program"], source)
        self.assertEqual(len(source.encode("utf-8")), 98)
        self.assertEqual(
            hashlib.sha256(source.encode("utf-8")).hexdigest(),
            "bb4995a4eaad6d9128cb1b0d177f8ba882be176fbd0db589bb861182d3020edd",
        )
        self.assertEqual(
            request["outer_exec_program_sha256"],
            hashlib.sha256(source.encode("utf-8")).hexdigest(),
        )
        boundary = json.loads(self.usage.read_text(encoding="utf-8"))[
            "submission_boundary"
        ]
        for field, expected in (
            codex_isolated.nested_submission_exec_yield_record().items()
        ):
            self.assertEqual(request[field], expected)
            self.assertEqual(boundary[field], expected)
        for field in (
            "call_id",
            "outer_exec_call_id",
            "outer_exec_program",
            "outer_exec_program_sha256",
            "response_id",
            "submission_transport",
        ):
            self.assertEqual(boundary[field], request[field])
        self.assertEqual(
            boundary["submission_event_order"],
            codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
        )
        self.assertTrue(
            boundary["dynamic_call_observed_before_raw_response_completed"]
        )
        self.assertFalse(
            boundary["raw_response_completed_before_dynamic_call_observed"]
        )

    def test_accepts_response_before_inner_call_with_stale_pre_response_cumulative(
        self,
    ) -> None:
        candidate = b"theorem candidate : True := by trivial\n"
        (self.workspace / "Candidate.lean").write_bytes(candidate)
        self.ledger.observe(self.reasoning_raw_item("prior-reasoning"))
        self.ledger.observe(
            raw_response_event(
                "prior-response",
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        self.ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        # Live V4 order from job 1507723: the exact final outer response and
        # raw usage arrive before dynamicToolCall item/started and item/tool/call.
        self.ledger.observe(self.nested_raw_item("response-first-outer"))
        self.ledger.observe(
            raw_response_event(
                "response-first-submit",
                "root",
                "root-turn",
                input_tokens=10,
                cached_input_tokens=2,
                output_tokens=3,
                reasoning_output_tokens=2,
            )
        )
        # The cumulative notification intentionally remains at prior-response:
        # completion of the blocked inner tool is what would normally release it.
        self.ledger.observe(self.dynamic_start("response-first-inner"))
        self.assertTrue(self.barrier.capture(self.request("response-first-inner")))
        self.assertEqual(
            self.barrier.pending["captured_response_id"],  # type: ignore[index]
            "response-first-submit",
        )
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaises(codex_isolated._SubmissionAccepted):
            self.barrier.advance()
        ack_thread.join(timeout=2)
        usage = json.loads(self.usage.read_text(encoding="utf-8"))
        boundary = usage["submission_boundary"]
        self.assertTrue(usage["measurement_exact"])
        self.assertEqual(
            boundary["submission_event_order"],
            codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER,
        )
        self.assertFalse(
            boundary["dynamic_call_observed_before_raw_response_completed"]
        )
        self.assertTrue(
            boundary["raw_response_completed_before_dynamic_call_observed"]
        )
        root_projection = next(
            thread for thread in usage["threads"] if thread["thread_id"] == "root"
        )
        self.assertEqual(
            root_projection["cumulative_projection_exempt_response_id"],
            "response-first-submit",
        )
        self.assertEqual(
            root_projection["cumulative_projection_status"],
            "matched_pre_exempt_response",
        )
        self.assertEqual(self.protocol_input.getvalue(), "")

    def test_accepts_actual_delayed_prior_output_order_before_nested_submit(self) -> None:
        candidate = b"theorem candidate : True := by trivial\n"
        (self.workspace / "Candidate.lean").write_bytes(candidate)
        self.ledger.observe(self.prior_exec_raw_item())
        self.ledger.observe(
            raw_response_event(
                "prior-response",
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        # This is the exact app-server ordering seen in job 1507670: the
        # provider response usage completes before its outer exec output item.
        self.ledger.observe(self.delayed_exec_output())
        self.assertEqual(
            self.ledger.raw_items_pending.get(("root", "root-turn"), []), []
        )
        delayed = self.ledger.delayed_tool_outputs[
            ("custom_tool_call_output", "prior-outer-call")
        ]
        self.assertEqual(delayed["prior_response_id"], "prior-response")
        self.ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        self.ledger.observe(self.reasoning_raw_item())
        self.stage_nested_call("inner-submit", outer_call_id="submit-outer-call")
        self.complete_raw("submit-response", "inner-submit")
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaises(codex_isolated._SubmissionAccepted):
            self.barrier.advance()
        ack_thread.join(timeout=2)
        boundary = json.loads(self.usage.read_text(encoding="utf-8"))[
            "submission_boundary"
        ]
        self.assertEqual(boundary["response_id"], "submit-response")
        self.assertEqual(boundary["outer_exec_call_id"], "submit-outer-call")
        self.assertEqual(self.protocol_input.getvalue(), "")

    def test_accepts_delayed_function_output_bound_to_prior_response(self) -> None:
        self.ledger.observe(
            raw_function_call_event(
                "root",
                "root-turn",
                "prior-function-call",
                name="wait_agent",
                namespace="collaboration",
            )
        )
        self.ledger.observe(
            raw_response_event(
                "prior-function-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        self.ledger.observe(self.delayed_function_output())
        self.assertEqual(
            self.ledger.raw_items_pending.get(("root", "root-turn"), []), []
        )
        delayed = self.ledger.delayed_tool_outputs[
            ("function_call_output", "prior-function-call")
        ]
        self.assertEqual(delayed["prior_response_id"], "prior-function-response")
        self.assertEqual(delayed["prior_call_item_id"], "fc-prior-function-call")

    def test_delayed_tool_output_binding_is_fail_closed(self) -> None:
        def fresh(name: str) -> AttemptUsageLedger:
            ledger = AttemptUsageLedger(self.root / f"{name}.json", 10_000, "root")
            ledger.observe(
                turn_event("turn/started", "root", "root-turn", "inProgress")
            )
            return ledger

        unmatched = fresh("unmatched-output")
        with self.assertRaisesRegex(RuntimeError, "prior completed response"):
            unmatched.observe(self.delayed_exec_output(call_id="unknown-call"))

        tampered = fresh("tampered-output")
        tampered.observe(self.prior_exec_raw_item())
        tampered.observe(
            raw_response_event(
                "prior-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        with self.assertRaisesRegex(RuntimeError, "turn metadata"):
            tampered.observe(
                self.delayed_exec_output(metadata_turn_id="different-turn")
            )

        late = fresh("late-output")
        late.observe(self.prior_exec_raw_item())
        late.observe(
            raw_response_event(
                "prior-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        late.observe(self.nested_raw_item("submit-outer-call"))
        with self.assertRaisesRegex(RuntimeError, "next raw response began"):
            late.observe(self.delayed_exec_output())

        duplicate = fresh("duplicate-function-output")
        duplicate.observe(
            raw_function_call_event(
                "root",
                "root-turn",
                "prior-function-call",
                name="wait_agent",
                namespace="collaboration",
            )
        )
        duplicate.observe(
            raw_response_event(
                "prior-function-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        duplicate.observe(self.delayed_function_output())
        with self.assertRaisesRegex(RuntimeError, "duplicate delayed tool output"):
            duplicate.observe(
                self.delayed_function_output(item_id="duplicate-function-output")
            )

        wrong_type = fresh("wrong-output-type")
        wrong_type.observe(self.prior_exec_raw_item())
        wrong_type.observe(
            raw_response_event(
                "prior-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        with self.assertRaisesRegex(RuntimeError, "prior completed response"):
            wrong_type.observe(
                self.delayed_function_output(call_id="prior-outer-call")
            )

        wrong_thread = fresh("wrong-output-thread")
        wrong_thread.observe(
            raw_function_call_event(
                "root",
                "root-turn",
                "prior-function-call",
                name="wait_agent",
                namespace="collaboration",
            )
        )
        wrong_thread.observe(
            raw_response_event(
                "prior-function-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        wrong_thread_output = self.delayed_function_output()
        wrong_thread_output["params"]["threadId"] = "other-thread"  # type: ignore[index]
        with self.assertRaisesRegex(RuntimeError, "prior completed response"):
            wrong_thread.observe(wrong_thread_output)

        tampered_function = fresh("tampered-function-output")
        tampered_function.observe(
            raw_function_call_event(
                "root",
                "root-turn",
                "prior-function-call",
                name="wait_agent",
                namespace="collaboration",
            )
        )
        tampered_function.observe(
            raw_response_event(
                "prior-function-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        with self.assertRaisesRegex(RuntimeError, "turn metadata"):
            tampered_function.observe(
                self.delayed_function_output(metadata_turn_id="different-turn")
            )

        for bad_item_id in (None, "", "bad-function-call"):
            with self.subTest(bad_function_item_id=bad_item_id):
                malformed_function = fresh(
                    "malformed-function-identity-"
                    + ("none" if bad_item_id is None else str(len(bad_item_id)))
                )
                malformed_call = raw_function_call_event(
                    "root",
                    "root-turn",
                    "bad-function-call",
                    name="wait_agent",
                    namespace="collaboration",
                )
                malformed_call["params"]["item"]["id"] = bad_item_id  # type: ignore[index]
                malformed_function.observe(malformed_call)
                with self.assertRaisesRegex(
                    RuntimeError, "function call lacks an identity"
                ):
                    malformed_function.observe(
                        raw_response_event(
                            "malformed-function-response",
                            "root",
                            "root-turn",
                            input_tokens=2,
                            cached_input_tokens=0,
                            output_tokens=1,
                        )
                    )

        malformed_custom = fresh("malformed-custom-identity")
        malformed_custom.observe(
            self.prior_exec_raw_item(
                call_id="same-custom-identity", item_id="same-custom-identity"
            )
        )
        with self.assertRaisesRegex(RuntimeError, "custom tool call lacks"):
            malformed_custom.observe(
                raw_response_event(
                    "malformed-custom-response",
                    "root",
                    "root-turn",
                    input_tokens=2,
                    cached_input_tokens=0,
                    output_tokens=1,
                )
            )

    def test_nested_exec_rejects_extra_javascript_wrong_path_and_extra_tool(self) -> None:
        bad_sources = (
            'await tools.submit_proof({candidate_path:"Candidate.lean"});',
            'await tools.submit_proof({candidate_path:"Candidate.lean"})\n',
            "await tools.submit_proof({candidate_path:'Candidate.lean'});\n",
            ' await tools.submit_proof({candidate_path:"Candidate.lean"});\n',
            'await tools.submit_proof({candidate_path:"Candidate.lean"});\n\n',
            'await tools.submit_proof({candidate_path:"Candidate.lean"}); text("x");',
            'const x = await tools.submit_proof({candidate_path:"Candidate.lean"});',
            '// prefix\nawait tools.submit_proof({candidate_path:"Candidate.lean"});',
            '// @exec: {"yield_time_ms": 2399999}\nawait tools.submit_proof({candidate_path:"Candidate.lean"});\n',
            '// @exec: {"yield_time_ms": 2400001}\nawait tools.submit_proof({candidate_path:"Candidate.lean"});\n',
            '// @exec:{"yield_time_ms":2400000}\nawait tools.submit_proof({candidate_path:"Candidate.lean"});\n',
            'await tools["submit_proof"]({candidate_path:"Candidate.lean"});',
            'await Promise.all([tools.submit_proof({candidate_path:"Candidate.lean"})]);',
            'await tools.submit_proof({candidate_path:"Other.lean"});',
        )
        for source in bad_sources:
            with self.subTest(source=source):
                self.assertFalse(
                    codex_isolated.is_canonical_nested_submit_exec_input(
                        source, candidate_path="Candidate.lean"
                    )
                )

        self.assertFalse(
            codex_isolated.is_canonical_nested_submit_exec_input(
                " \n await tools.submit_proof( { 'candidate_path' : 'Candidate.lean' } ) \t;\n",
                candidate_path="Candidate.lean",
            )
        )

        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        self.stage_nested_call(
            "inner-extra-tool", outer_call_id="outer-extra-tool"
        )
        self.ledger.observe(self.raw_item("another-model-tool"))
        self.ledger.observe(
            raw_response_event(
                "response-extra-tool",
                "root",
                "root-turn",
                input_tokens=10,
                cached_input_tokens=2,
                output_tokens=3,
            )
        )
        self.assertFalse(self.barrier.advance())
        rejection = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertIn(
            "sole tool call", rejection["result"]["contentItems"][0]["text"]
        )
        self.assertIn(
            repr(codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE),
            rejection["result"]["contentItems"][0]["text"],
        )

    def test_nested_exec_does_not_bind_a_mismatched_response(self) -> None:
        self.ledger.observe(self.nested_raw_item("outer-call"))
        self.ledger.observe(self.dynamic_start("inner-dynamic-call"))
        expected_wire = self.ledger.pending_submission_wire(
            turn_id="root-turn",
            call_id="inner-dynamic-call",
            candidate_path="Candidate.lean",
        )
        self.assertIsNotNone(expected_wire)
        self.ledger.observe(
            raw_response_event(
                "wrong-turn-response",
                "unrelated-child",
                "another-turn",
                input_tokens=10,
                cached_input_tokens=2,
                output_tokens=3,
            )
        )
        self.assertIsNone(
            self.ledger.matching_submit_response(
                turn_id="root-turn",
                call_id="inner-dynamic-call",
                candidate_path="Candidate.lean",
                expected_wire=expected_wire or {},
            )
        )

    def test_response_first_binding_rejects_projection_wrong_response_and_later_raw(
        self,
    ) -> None:
        def fresh_barrier(
            name: str,
        ) -> tuple[AttemptUsageLedger, codex_isolated.SubmissionBarrier, io.StringIO]:
            usage = self.root / name / "usage.json"
            paths = codex_isolated.submission_barrier_paths(usage)
            paths["challenge"].parent.mkdir(parents=True)
            paths["challenge"].write_text(
                json.dumps(
                    codex_isolated.authenticated_record(
                        {
                            "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                            "kind": "highambench_submission_challenge",
                            "run_id": name,
                            "attempt_nonce": name + "-nonce",
                            "validator_contract_sha256": "c" * 64,
                            **codex_isolated.nested_submission_exec_yield_record(),
                        },
                        "challenge_sha256",
                    )
                ),
                encoding="utf-8",
            )
            ledger = AttemptUsageLedger(usage, 10_000, "root")
            ledger.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
            output = io.StringIO()
            barrier = codex_isolated.SubmissionBarrier(
                workspace=self.workspace,
                usage_output=usage,
                ledger=ledger,
                protocol_input=output,
                protocol_reader=self.Reader(),  # type: ignore[arg-type]
            )
            return ledger, barrier, output

        (self.workspace / "Candidate.lean").write_text(
            "theorem candidate : True := by trivial\n", encoding="utf-8"
        )

        gap, gap_barrier, gap_output = fresh_barrier("prior-projection-gap")
        gap.observe(self.reasoning_raw_item("gap-prior-reasoning"))
        gap.observe(
            raw_response_event(
                "gap-prior-response",
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        gap.observe(self.nested_raw_item("gap-submit-outer"))
        gap.observe(
            raw_response_event(
                "gap-submit-response",
                "root",
                "root-turn",
                input_tokens=5,
                cached_input_tokens=1,
                output_tokens=2,
            )
        )
        gap.observe(self.dynamic_start("gap-submit-inner"))
        self.assertTrue(gap_barrier.capture(self.request("gap-submit-inner")))
        self.assertIsNone(gap_barrier.pending)
        self.assertIn("root token projection", gap_output.getvalue())

        wrong, wrong_barrier, wrong_output = fresh_barrier("wrong-latest-response")
        wrong.observe(self.nested_raw_item("old-exact-outer"))
        wrong.observe(
            raw_response_event(
                "old-exact-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        wrong.observe(self.reasoning_raw_item("unrelated-latest-item"))
        wrong.observe(
            raw_response_event(
                "unrelated-latest-response",
                "root",
                "root-turn",
                input_tokens=1,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        wrong.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=0,
                output_tokens=2,
            )
        )
        wrong.observe(self.dynamic_start("wrong-response-inner"))
        self.assertTrue(wrong_barrier.capture(self.request("wrong-response-inner")))
        self.assertIsNone(wrong_barrier.pending)
        self.assertIn("exact preceding outer exec", wrong_output.getvalue())

        later, later_barrier, later_output = fresh_barrier("later-root-response")
        later.observe(self.nested_raw_item("later-submit-outer"))
        later.observe(
            raw_response_event(
                "later-submit-response",
                "root",
                "root-turn",
                input_tokens=2,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        later.observe(self.dynamic_start("later-submit-inner"))
        self.assertTrue(later_barrier.capture(self.request("later-submit-inner")))
        self.assertIsNotNone(later_barrier.pending)
        later.observe(self.reasoning_raw_item("forbidden-later-item"))
        later.observe(
            raw_response_event(
                "forbidden-later-response",
                "root",
                "root-turn",
                input_tokens=0,
                cached_input_tokens=0,
                output_tokens=0,
            )
        )
        self.assertFalse(later_barrier.advance())
        self.assertIsNone(later_barrier.pending)
        self.assertIn("sole tool call", later_output.getvalue())

    def test_nested_exec_requires_preceding_matching_dynamic_start(self) -> None:
        self.ledger.observe(self.nested_raw_item("outer-call"))
        self.assertIsNone(
            self.ledger.pending_submission_wire(
                turn_id="root-turn",
                call_id="inner-call",
                candidate_path="Candidate.lean",
            )
        )
        wrong = self.dynamic_start("different-inner-call")
        self.ledger.observe(wrong)
        self.assertIsNone(
            self.ledger.pending_submission_wire(
                turn_id="root-turn",
                call_id="inner-call",
                candidate_path="Candidate.lean",
            )
        )

        other_usage = self.root / "other-usage.json"
        other = AttemptUsageLedger(other_usage, 10_000, "root")
        other.observe(turn_event("turn/started", "root", "root-turn", "inProgress"))
        other.observe(self.dynamic_start("inner-call"))
        with self.assertRaisesRegex(RuntimeError, "duplicate dynamic tool"):
            other.observe(self.dynamic_start("inner-call"))
        mismatched_duplicate = self.dynamic_start("inner-call")
        mismatched_duplicate["params"]["item"]["arguments"] = {
            "candidate_path": "Other.lean"
        }
        with self.assertRaisesRegex(RuntimeError, "duplicate dynamic tool"):
            other.observe(mismatched_duplicate)
        other.observe(self.nested_raw_item("outer-call"))
        self.assertIsNone(
            other.pending_submission_wire(
                turn_id="root-turn",
                call_id="inner-call",
                candidate_path="Candidate.lean",
            )
        )

    def test_submission_barrier_prior_schema_challenge_is_rejected(self) -> None:
        for prior_version in (1, 2, 3):
            with self.subTest(prior_version=prior_version):
                usage = self.root / f"v{prior_version}" / "usage.json"
                paths = codex_isolated.submission_barrier_paths(usage)
                paths["challenge"].parent.mkdir(parents=True)
                paths["challenge"].write_text(
                    json.dumps(
                        codex_isolated.authenticated_record(
                            {
                                "schema_version": prior_version,
                                "kind": "highambench_submission_challenge",
                                "run_id": "old-run",
                                "attempt_nonce": "old-nonce",
                                "validator_contract_sha256": "c" * 64,
                            },
                            "challenge_sha256",
                        )
                    ),
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(RuntimeError, "malformed"):
                    codex_isolated.SubmissionBarrier(
                        workspace=self.workspace,
                        usage_output=usage,
                        ledger=self.ledger,
                        protocol_input=self.protocol_input,
                        protocol_reader=self.reader,  # type: ignore[arg-type]
                    )

    def test_submission_barrier_requires_full_yield_envelope_challenge(self) -> None:
        for missing in codex_isolated.nested_submission_exec_yield_record():
            with self.subTest(missing=missing):
                usage = self.root / f"missing-{missing}" / "usage.json"
                paths = codex_isolated.submission_barrier_paths(usage)
                paths["challenge"].parent.mkdir(parents=True)
                challenge = {
                    "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                    "kind": "highambench_submission_challenge",
                    "run_id": "missing-yield-field",
                    "attempt_nonce": "missing-yield-nonce",
                    "validator_contract_sha256": "c" * 64,
                    **codex_isolated.nested_submission_exec_yield_record(),
                }
                challenge.pop(missing)
                paths["challenge"].write_text(
                    json.dumps(
                        codex_isolated.authenticated_record(
                            challenge, "challenge_sha256"
                        )
                    ),
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(RuntimeError, "malformed"):
                    codex_isolated.SubmissionBarrier(
                        workspace=self.workspace,
                        usage_output=usage,
                        ledger=self.ledger,
                        protocol_input=self.protocol_input,
                        protocol_reader=self.reader,  # type: ignore[arg-type]
                    )

    def test_accept_uses_raw_then_blocked_call_and_sends_no_tool_response(self) -> None:
        candidate = b"theorem candidate : True := by trivial\n"
        (self.workspace / "Candidate.lean").write_bytes(candidate)
        self.stage_nested_call("call-1")
        self.assertTrue(
            codex_isolated.submission_barrier_paths(self.usage)["call"].is_file()
        )
        self.complete_raw("response-1", "call-1")
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaises(codex_isolated._SubmissionAccepted):
            self.barrier.advance()
        ack_thread.join(timeout=2)
        self.assertEqual(self.protocol_input.getvalue(), "")
        usage = json.loads(self.usage.read_text(encoding="utf-8"))
        self.assertTrue(usage["measurement_exact"])
        self.assertFalse(usage["drain_complete"])
        self.assertEqual(usage["active_thread_ids"], ["root"])
        boundary = usage["submission_boundary"]
        self.assertFalse(boundary["later_model_response_possible"])
        self.assertTrue(boundary["outer_exec_final_raw_item"])
        self.assertTrue(boundary["inner_dynamic_call_left_blocked"])
        self.assertFalse(boundary["inner_dynamic_tool_response_sent"])
        self.assertFalse(boundary["outer_exec_output_emitted"])

    def test_provider_gate_serializes_token_crossing_and_submission_lock_orders(
        self,
    ) -> None:
        class FakeGate:
            def __init__(self, *, token_won: bool) -> None:
                self.state: dict[str, object] = {
                    "phase": "CLOSED" if token_won else "EXCLUSIVE",
                    "close_reason": (
                        codex_isolated.PROVIDER_GATE_CLOSE_TOKEN_LIMIT
                        if token_won
                        else None
                    ),
                    "crossing": {"response_id": "crossing"} if token_won else None,
                    "open_request_ids": [],
                    "all_complete": True,
                    "poisoned": False,
                }

            def snapshot(self) -> dict[str, object]:
                return dict(self.state)

            def close_for_accepted_submission(self) -> dict[str, object]:
                if self.state["close_reason"] is not None:
                    return {
                        "won": False,
                        "effective_reason": self.state["close_reason"],
                        "phase": self.state["phase"],
                        "sequence": 7,
                    }
                self.state.update(
                    {
                        "phase": "CLOSED",
                        "close_reason": codex_isolated.PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION,
                    }
                )
                return {
                    "won": True,
                    "effective_reason": codex_isolated.PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION,
                    "phase": "CLOSED",
                    "sequence": 8,
                }

        (self.workspace / "Candidate.lean").write_text(
            "theorem candidate : True := by trivial\n", encoding="utf-8"
        )
        token_gate = FakeGate(token_won=True)
        self.barrier.provider_gate = token_gate  # type: ignore[assignment]
        self.stage_nested_call("token-won")
        self.assertIsNone(self.barrier.pending)
        self.assertIn("provider-token cap", self.protocol_input.getvalue())
        self.assertFalse(
            codex_isolated.submission_barrier_paths(self.usage, 1)["snapshot"].exists()
        )

        # Recreate a clean barrier: this time the blocked dynamic call prevents
        # any new admission, and accepted_submission wins the gate lock.
        self.tearDown()
        self.setUp()
        (self.workspace / "Candidate.lean").write_text(
            "theorem candidate : True := by trivial\n", encoding="utf-8"
        )
        submit_gate = FakeGate(token_won=False)
        self.barrier.provider_gate = submit_gate  # type: ignore[assignment]
        self.stage_nested_call("submit-won")
        self.complete_raw("submit-response", "submit-won")
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaises(codex_isolated._SubmissionAccepted):
            self.barrier.advance()
        ack_thread.join(timeout=2)
        boundary = json.loads(self.usage.read_text(encoding="utf-8"))[
            "submission_boundary"
        ]
        self.assertTrue(boundary["provider_gate_close"]["won"])
        self.assertEqual(
            boundary["provider_gate_close"]["effective_reason"],
            codex_isolated.PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION,
        )

    def test_reject_cleans_sequence_and_allows_repair(self) -> None:
        (self.workspace / "Candidate.lean").write_text("bad\n", encoding="utf-8")
        self.stage_nested_call("call-1")
        self.complete_raw("response-1", "call-1")
        first_ack = self.write_ack_when_requested("reject")
        self.assertFalse(self.barrier.advance())
        first_ack.join(timeout=2)
        first_response = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertFalse(first_response["result"]["success"])
        self.ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=10,
                cached_input_tokens=2,
                output_tokens=3,
                reasoning_output_tokens=2,
            )
        )
        (self.workspace / "Candidate.lean").write_text("good\n", encoding="utf-8")
        second = self.request("call-2")
        second["id"] = 45
        self.ledger.observe(self.nested_raw_item("outer-call-2"))
        self.ledger.observe(self.dynamic_start("call-2"))
        self.assertTrue(self.barrier.capture(second))
        self.complete_raw("response-2", "call-2")
        second_ack = self.write_ack_when_requested("accept")
        with self.assertRaises(codex_isolated._SubmissionAccepted):
            self.barrier.advance()
        second_ack.join(timeout=2)
        boundary = json.loads(self.usage.read_text(encoding="utf-8"))[
            "submission_boundary"
        ]
        self.assertEqual(boundary["sequence"], 2)

    def test_child_nonquiescent_cap_path_and_symlink_reject_fail_closed(self) -> None:
        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        traversal = self.request("call-traversal")
        traversal["params"]["arguments"]["candidate_path"] = "../Candidate.lean"
        self.barrier.capture(traversal)
        traversal_error = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertIn("exactly Candidate.lean", traversal_error["result"]["contentItems"][0]["text"])

        self.barrier.capture(self.request(thread_id="child"))
        child_error = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertFalse(child_error["result"]["success"])

        self.ledger.observe(
            raw_function_call_event(
                "root", "root-turn", "spawn-child", fork_turns="none"
            )
        )
        self.ledger.observe(
            raw_response_event(
                "spawn-response",
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        self.ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        self.ledger.observe(
            collab_spawn_event(
                "root", "root-turn", "spawn-child", "child"
            )
        )
        self.ledger.observe(
            subagent_started_event(
                "root",
                "child",
                "root/child",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        self.ledger.observe(turn_event("turn/started", "child", "child-turn", "inProgress"))
        self.barrier.capture(self.request("call-active"))
        active_error = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertIn("descendant", active_error["result"]["contentItems"][0]["text"])

        self.ledger.observe(
            cumulative_usage_event(
                "child",
                "child-turn",
                input_tokens=0,
                cached_input_tokens=0,
                output_tokens=0,
            )
        )
        self.ledger.observe(turn_event("turn/completed", "child", "child-turn", "completed"))
        (self.workspace / "Candidate.lean").unlink()
        (self.workspace / "Candidate.lean").symlink_to("missing.lean")
        self.stage_nested_call("call-link")
        link_error = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertIn("symlink", link_error["result"]["contentItems"][0]["text"])

        self.ledger.observe(
            raw_response_event(
                "cap-response",
                "root",
                "root-turn",
                input_tokens=9_999,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        self.barrier.capture(self.request("call-cap"))
        cap_error = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertIn("token cap", cap_error["result"]["contentItems"][0]["text"])

    def test_acceptance_refuses_incomplete_descendant_accounting(self) -> None:
        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        self.ledger.observe(
            raw_function_call_event(
                "root", "root-turn", "spawn-child", fork_turns="none"
            )
        )
        self.ledger.observe(
            raw_response_event(
                "spawn-response",
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        self.ledger.observe(
            cumulative_usage_event(
                "root",
                "root-turn",
                input_tokens=3,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        self.ledger.observe(
            subagent_started_event(
                "root",
                "child",
                "root/child",
                parent_turn_id="root-turn",
                activity_id="spawn-child",
            )
        )
        self.ledger.observe(
            turn_event("turn/started", "child", "child-turn", "inProgress")
        )
        self.ledger.observe(
            raw_response_event(
                "child-observed",
                "child",
                "child-turn",
                input_tokens=4,
                cached_input_tokens=1,
                output_tokens=1,
            )
        )
        # No final child cumulative notification: an omitted raw response could
        # otherwise be invisible, so even a terminal child is not acceptable.
        self.ledger.observe(
            turn_event("turn/completed", "child", "child-turn", "completed")
        )
        self.ledger.observe(self.nested_raw_item("incomplete-descendant-outer"))
        self.ledger.observe(
            raw_response_event(
                "incomplete-descendant-submit-response",
                "root",
                "root-turn",
                input_tokens=5,
                cached_input_tokens=1,
                output_tokens=2,
            )
        )
        self.ledger.observe(self.dynamic_start("submit-incomplete"))
        self.assertTrue(self.barrier.capture(self.request("submit-incomplete")))
        response = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertFalse(response["result"]["success"])
        self.assertIn(
            "descendant token projections",
            response["result"]["contentItems"][0]["text"],
        )
        self.assertFalse(self.ledger.snapshot()["measurement_exact"])

    def test_submit_must_be_final_and_only_tool_item(self) -> None:
        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        self.stage_nested_call("call-1")
        self.ledger.observe(self.raw_item("call-1"))
        self.ledger.observe(
            {
                "method": "rawResponseItem/completed",
                "params": {
                    "threadId": "root",
                    "turnId": "root-turn",
                    "item": {"type": "message", "role": "assistant", "content": []},
                },
            }
        )
        self.ledger.observe(
            raw_response_event(
                "invalid-response",
                "root",
                "root-turn",
                input_tokens=4,
                cached_input_tokens=0,
                output_tokens=2,
            )
        )
        self.assertFalse(self.barrier.advance())
        response = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertIn("sole tool call", response["result"]["contentItems"][0]["text"])

    def test_already_finalized_invalid_raw_response_rejects_immediately(self) -> None:
        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        self.ledger.observe(self.raw_item("call-1"))
        self.ledger.observe(
            {
                "method": "rawResponseItem/completed",
                "params": {
                    "threadId": "root",
                    "turnId": "root-turn",
                    "item": {
                        "type": "local_shell_call",
                        "call_id": "other-call",
                        "status": "completed",
                        "action": {},
                    },
                },
            }
        )
        self.ledger.observe(
            raw_response_event(
                "already-final",
                "root",
                "root-turn",
                input_tokens=5,
                cached_input_tokens=0,
                output_tokens=2,
            )
        )
        self.assertTrue(self.barrier.capture(self.request()))
        self.assertFalse(self.barrier.advance())
        response = json.loads(self.protocol_input.getvalue().splitlines()[-1])
        self.assertFalse(response["result"]["success"])

    def test_post_boundary_raw_activity_taints_while_runner_validates(self) -> None:
        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        self.stage_nested_call("call-1")
        self.complete_raw("response-1", "call-1")
        self.reader.messages.put(
            raw_response_event(
                "forbidden-later-response",
                "root",
                "root-turn",
                input_tokens=1,
                cached_input_tokens=0,
                output_tokens=1,
            )
        )
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaisesRegex(RuntimeError, "post-boundary"):
            self.barrier.advance()
        ack_thread.join(timeout=2)

    def test_job_1507969_outer_exec_progress_yield_is_fatal(self) -> None:
        """Replay the exact causal sequence retained from Slurm job 1507969."""

        (self.workspace / "Candidate.lean").write_text("candidate\n", encoding="utf-8")
        outer_call_id = "call_4l1fCa9c3JFtGZT368hKgO4c"
        self.stage_nested_call(
            "exec-77df-preserved-inner",
            outer_call_id=outer_call_id,
        )
        self.complete_raw("preserved-response", "exec-77df-preserved-inner")
        self.reader.messages.put(
            {
                "method": "rawResponseItem/completed",
                "params": {
                    "threadId": "root",
                    "turnId": "root-turn",
                    "item": {
                        "type": "custom_tool_call_output",
                        "id": "ctco_preserved_job_1507969",
                        "call_id": outer_call_id,
                        "output": (
                            "Script running with cell ID 4\n"
                            "Wall time 11.0 seconds\n"
                            "Output:\n"
                        ),
                    },
                },
            }
        )
        ack_thread = self.write_ack_when_requested("accept")
        with self.assertRaisesRegex(RuntimeError, "post-boundary"):
            self.barrier.advance()
        ack_thread.join(timeout=2)

    def test_hidden_validation_rejects_every_non_bookkeeping_activity_shape(self) -> None:
        progress = {
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": "root",
                "turnId": "root-turn",
                "item": {
                    "type": "custom_tool_call_output",
                    "id": "progress-output",
                    "call_id": "outer-call",
                    "output": "Script running with cell ID 9\nWall time 11.0 seconds\nOutput:\n",
                },
            },
        }
        adversarial = [
            progress,
            {**progress, "params": {**progress["params"], "threadId": "other"}},
            {**progress, "params": {**progress["params"], "item": {**progress["params"]["item"], "output": []}}},
            {"method": "rawResponse/completed", "params": {}},
            self.reasoning_raw_item("late-reasoning"),
            self.dynamic_start("late-inner"),
            {
                "method": "thread/status/changed",
                "params": {"threadId": "child", "status": {"type": "idle"}},
            },
        ]
        for message in adversarial:
            with self.subTest(method=message.get("method"), message=message):
                with self.assertRaisesRegex(RuntimeError, "post-boundary"):
                    self.barrier._observe_during_hidden_validation(message)


class IsolationAdapterTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        (self.workspace / "task" / "shared").mkdir(parents=True)
        self.state_home = self.root / "state-home"
        self.state_home.mkdir()
        self.toolchain = self.root / "toolchain"
        self.toolchain.mkdir()
        self.packages = self.root / "packages"
        (self.packages / "mathlib" / ".lake" / "build" / "lib" / "lean").mkdir(
            parents=True
        )
        (self.packages / "batteries" / ".lake" / "build" / "lib" / "lean").mkdir(
            parents=True
        )
        self.shared_olean = self.root / "shared-olean"
        self.shared_olean.mkdir()
        self.library_source = self.root / "library-source"
        self.library_source.mkdir()
        self.library_olean = self.root / "library-olean"
        self.library_olean.mkdir()
        self.library_root = self.root / "NumStability.lean"
        self.library_root.write_text("import NumStability.Basic\n", encoding="utf-8")
        self.resolver = self.root / "resolver"
        self.resolver.mkdir()
        self.codex = self.root / "codex"
        self.codex.write_text("binary", encoding="utf-8")
        self.offline_shell = self.root / "offline-shell"
        self.offline_shell.write_text("binary", encoding="utf-8")
        self.network_marker = self.workspace / ".network-marker"
        self.network_marker.write_bytes(b"")
        self.bwrap = self.root / "bwrap"
        self.bwrap.write_text("binary", encoding="utf-8")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def codex_args(self, condition: str) -> argparse.Namespace:
        return argparse.Namespace(
            bwrap=self.bwrap,
            resolver_root=self.resolver,
            inside_home="/u501/tester",
            workspace=self.workspace,
            controlled_relative="task",
            codex=self.codex,
            offline_shell=self.offline_shell,
            toolchain_root=self.toolchain,
            packages_root=self.packages,
            shared_olean_root=self.shared_olean,
            shared_root_relative="task/shared",
            condition=condition,
            library_source=self.library_source if condition == "L" else None,
            library_root_file=self.library_root if condition == "L" else None,
            library_olean=self.library_olean if condition == "L" else None,
            model="test-model",
            reasoning_effort="medium",
            token_limit=1234,
            advisory_rollout_budget_limit=4321,
            network_violation_marker=self.network_marker,
            provider_gate_base_url=(
                "http://127.0.0.1:23456/"
                + "a" * 32
                + "/backend-api/codex"
            ),
            model_catalog_sha256="c" * 64,
            model_entry_sha256="d" * 64,
            provider_response_bound=codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND,
        )

    def enable_prompt_handshake(
        self, args: argparse.Namespace, usage_output: Path
    ) -> threading.Thread:
        """Act as the trusted runner for a direct adapter protocol test."""

        usage_output.parent.mkdir(parents=True, exist_ok=True)
        paths = codex_isolated.prompt_handshake_paths(usage_output)
        args.prompt_ready_output = paths["ready"]
        args.prompt_go_input = paths["go"]
        args.prompt_release_output = paths["release"]
        args.prompt_handshake_nonce = "b" * 64
        args.prompt_run_id = "direct-adapter-test"
        gate_paths = codex_isolated.provider_gate_paths(usage_output)
        args.provider_gate_live_output = gate_paths["live"]
        args.provider_gate_output = gate_paths["final"]

        def authorize() -> None:
            deadline = time.monotonic() + 2.0
            while not paths["ready"].exists():
                if time.monotonic() >= deadline:
                    return
                time.sleep(0.002)
            ready = codex_isolated.read_authenticated_record_file(
                paths["ready"], "ready_sha256"
            )
            common = {
                field: ready[field]
                for field in codex_isolated.PromptReleaseHandshake._COMMON_FIELDS
            }
            codex_isolated.write_authenticated_record_atomic(
                paths["go"],
                {
                    **common,
                    "kind": codex_isolated.PROMPT_GO_KIND,
                    "ready_sha256": ready["ready_sha256"],
                    "turn_start_write_authorized": True,
                    "authorized_at_monotonic_ns": max(
                        time.monotonic_ns(), ready["ready_at_monotonic_ns"]
                    ),
                    "authorized_at_unix_ns": time.time_ns(),
                },
                "go_sha256",
            )

        thread = threading.Thread(target=authorize, daemon=True)
        thread.start()
        return thread

    def lean_args(self, condition: str) -> argparse.Namespace:
        return argparse.Namespace(
            bwrap=self.bwrap,
            workspace=self.workspace,
            toolchain_root=self.toolchain,
            packages_root=self.packages,
            shared_olean_root=self.shared_olean,
            shared_root_relative="task/shared",
            condition=condition,
            library_source=self.library_source if condition == "L" else None,
            library_root_file=self.library_root if condition == "L" else None,
            library_olean=self.library_olean if condition == "L" else None,
        )

    def test_prompt_construction_has_fixed_sections_and_one_final_newline(self) -> None:
        prompt_file = self.root / "prompt.md"
        context_file = self.root / "context.md"
        target_file = self.root / "Target.lean"
        prompt_file.write_text("Instructions.\n\n", encoding="utf-8")
        context_file.write_text("Paper context.   \n", encoding="utf-8")
        target_file.write_text("theorem fixed : True := by\n  sorry\n\n", encoding="utf-8")
        self.assertEqual(
            build_prompt(prompt_file, context_file, target_file),
            "Instructions.\n\n"
            "## Task context\n\nPaper context.\n\n"
            "## Fixed Lean target\n\n```lean\n"
            "theorem fixed : True := by\n  sorry\n```\n",
        )

        condition_prompt = self.root / "condition-L.md"
        condition_prompt.write_text("L can search the frozen library.\n\n", encoding="utf-8")
        self.assertEqual(
            build_prompt(prompt_file, context_file, target_file, condition_prompt),
            "Instructions.\n\n"
            "L can search the frozen library.\n\n"
            "## Task context\n\nPaper context.\n\n"
            "## Fixed Lean target\n\n```lean\n"
            "theorem fixed : True := by\n  sorry\n```\n",
        )

    def test_prompt_handshake_paths_fail_closed_on_unsafe_or_stale_artifacts(self) -> None:
        logs = self.root / "trusted-logs"
        logs.mkdir()
        usage = logs / "attempt.usage.json"
        paths = codex_isolated.prompt_handshake_paths(usage)
        args = self.codex_args("N")
        args.prompt_ready_output = paths["ready"]
        args.prompt_go_input = paths["go"]
        args.prompt_release_output = paths["release"]
        args.prompt_handshake_nonce = "c" * 64
        args.prompt_run_id = "path-test"

        paths["ready"].symlink_to(self.root / "attacker-record")
        with self.assertRaisesRegex(RuntimeError, "already exists"):
            codex_isolated.PromptReleaseHandshake(
                args=args,
                workspace=self.workspace,
                usage_output=usage,
                prompt="fixed prompt\n",
            )
        paths["ready"].unlink()

        args.prompt_release_output = self.root / "outside-release.json"
        with self.assertRaisesRegex(RuntimeError, "direct child of trusted logs"):
            codex_isolated.PromptReleaseHandshake(
                args=args,
                workspace=self.workspace,
                usage_output=usage,
                prompt="fixed prompt\n",
            )
        args.prompt_release_output = paths["release"]
        paths["go"].write_text("stale", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "already exists"):
            codex_isolated.PromptReleaseHandshake(
                args=args,
                workspace=self.workspace,
                usage_output=usage,
                prompt="fixed prompt\n",
            )

    def test_provider_gate_paths_are_usage_bound_and_fail_closed_if_stale(self) -> None:
        logs = self.root / "gate-logs"
        logs.mkdir()
        usage = logs / "attempt.usage.json"
        paths = codex_isolated.provider_gate_paths(usage)
        self.assertEqual(paths["live"], logs / "attempt.provider-token-gate.live.json")
        self.assertEqual(paths["final"], logs / "attempt.provider-token-gate.json")
        args = self.codex_args("N")
        args.provider_gate_live_output = paths["live"]
        args.provider_gate_output = paths["final"]
        self.assertEqual(
            codex_isolated._validated_provider_gate_paths(
                args, self.workspace, usage
            ),
            paths,
        )
        paths["live"].write_text("stale\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "already exists"):
            codex_isolated._validated_provider_gate_paths(
                args, self.workspace, usage
            )

    def test_preserved_1508037_interrupt_record_remains_unscored(self) -> None:
        archive = (
            TOOLS.parent.parent
            / "scratch_pad"
            / "highambench_p01_actual_ultra_failed_token_interrupt_slurm-1508037"
        )
        usage_path = (
            archive / "logs" / "P01-T1-rep-01-N.attempt-1.usage.json"
        )
        attempt_path = (
            archive / "attempts" / "P01-T1-rep-01-N.attempt-1.json"
        )
        if not usage_path.is_file() or not attempt_path.is_file():
            self.skipTest("preserved Slurm 1508037 evidence is not installed")
        usage = json.loads(usage_path.read_text(encoding="utf-8"))
        attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
        self.assertTrue(usage["interrupt_requested"])
        self.assertFalse(usage["measurement_exact"])
        self.assertEqual(usage["total_tokens"], 2_007_939)
        self.assertEqual(len(usage["first_crossing"]["active_thread_ids"]), 4)
        self.assertNotIn("provider_token_gate", usage)
        self.assertFalse(attempt["scored"])
        self.assertFalse(attempt["pass"])
        self.assertEqual(attempt["failure_code"], "TOKEN_LIMIT")

    def test_prompt_handshake_publication_is_exclusive_and_tamper_evident(self) -> None:
        path = self.root / "record.json"
        record = codex_isolated.write_authenticated_record_atomic(
            path,
            {"schema_version": 1, "kind": "test", "value": 7},
            "record_sha256",
        )
        self.assertEqual(
            codex_isolated.read_authenticated_record_file(path, "record_sha256"),
            record,
        )
        self.assertEqual(stat.S_IMODE(path.lstat().st_mode), 0o444)
        with self.assertRaises(FileExistsError):
            codex_isolated.write_authenticated_record_atomic(
                path,
                {"schema_version": 1, "kind": "replacement", "value": 8},
                "record_sha256",
            )
        path.chmod(0o600)
        tampered = dict(record)
        tampered["value"] = 8
        path.write_text(
            json.dumps(tampered, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(RuntimeError, "self-hash mismatch"):
            codex_isolated.read_authenticated_record_file(path, "record_sha256")

    def test_condition_prompt_is_required_only_for_l_and_hash_checked(self) -> None:
        condition_prompt = self.root / "condition-L.md"
        condition_prompt.write_text("signposted library\n", encoding="utf-8")
        digest = hashlib.sha256(condition_prompt.read_bytes()).hexdigest()
        self.assertIsNone(validated_condition_prompt("N", None, None))
        self.assertEqual(
            validated_condition_prompt("L", condition_prompt, digest),
            condition_prompt,
        )
        with self.assertRaisesRegex(RuntimeError, "condition L requires"):
            validated_condition_prompt("L", None, None)
        with self.assertRaisesRegex(RuntimeError, "condition N must not receive"):
            validated_condition_prompt("N", condition_prompt, digest)
        with self.assertRaisesRegex(RuntimeError, "does not match"):
            validated_condition_prompt("L", condition_prompt, "0" * 64)
        symlink = self.root / "condition-link.md"
        symlink.symlink_to(condition_prompt)
        with self.assertRaisesRegex(RuntimeError, "non-symlink"):
            validated_condition_prompt("L", symlink, digest)

    def test_frozen_l_notice_names_access_paths_but_no_task_theorem_hint(self) -> None:
        text = (TOOLS.parent / "condition_prompts" / "L.md").read_text(
            encoding="utf-8"
        )
        for required in (
            "45813a95dacf577461bae13f033af0dbc985a225",
            "/library/NumStability",
            "/library/NumStability.lean",
            "/library-olean",
            "LEAN_PATH",
            "find ",
            "rg -n",
            "import NumStability",
        ):
            self.assertIn(required, text)
        for forbidden in (
            "pairwiseSum_forward_error_bound",
            "recursiveSum_forward_error_bound",
            "noGuardAddWitness_error_eq",
            "gamma_mono",
        ):
            self.assertNotIn(forbidden, text)

    def test_usage_parser_accepts_only_exact_nonnegative_integer_fields(self) -> None:
        self.assertEqual(
            normalized_usage(
                {
                    "method": "thread/tokenUsage/updated",
                    "params": {
                        "threadId": "thread-1",
                        "turnId": "turn-1",
                        "tokenUsage": {
                            "last": {},
                            "total": {
                                "inputTokens": 10,
                                "cachedInputTokens": 4,
                                "outputTokens": 3,
                                "reasoningOutputTokens": 2,
                                "totalTokens": 13,
                                "ignored": 99,
                            },
                        },
                    },
                }
            ),
            {
                "input_tokens": 10,
                "cached_input_tokens": 4,
                "output_tokens": 3,
                "measurement_source": TOKEN_USAGE_MEASUREMENT_SOURCE,
                "live_cumulative": True,
                "input_includes_cached": True,
            },
        )
        self.assertIsNone(normalized_usage({"method": "item/completed", "params": {}}))
        self.assertIsNone(
            normalized_usage(
                {
                    "method": "thread/tokenUsage/updated",
                    "params": {
                        "tokenUsage": {
                            "total": {
                                "inputTokens": True,
                                "cachedInputTokens": 0,
                                "outputTokens": 1,
                                "totalTokens": 1,
                            }
                        }
                    },
                }
            )
        )
        self.assertIsNone(
            normalized_usage(
                {
                    "method": "thread/tokenUsage/updated",
                    "params": {
                        "tokenUsage": {
                            "total": {
                                "inputTokens": 1,
                                "cachedInputTokens": -1,
                                "outputTokens": 1,
                                "totalTokens": 2,
                            }
                        }
                    },
                }
            )
        )
        self.assertIsNone(
            normalized_usage(
                {
                    "method": "thread/tokenUsage/updated",
                    "params": {
                        "tokenUsage": {
                            "total": {
                                "inputTokens": 4,
                                "cachedInputTokens": 1,
                                "outputTokens": 2,
                                "totalTokens": 7,
                            }
                        }
                    },
                }
            )
        )

    def test_codex_n_and_l_mounts_are_separate_and_controlled_tree_is_read_only(self) -> None:
        n_args = self.codex_args("N")
        # Even accidental L-only arguments must not leak into condition N.
        n_args.library_source = self.library_source
        n_args.library_root_file = self.library_root
        n_args.library_olean = self.library_olean
        n_command = bubblewrap_command(n_args, self.state_home)
        l_command = bubblewrap_command(self.codex_args("L"), self.state_home)
        n_mounts = mounts(n_command)
        l_mounts = mounts(l_command)

        workspace_bind = next(
            mount for mount in n_mounts if mount[2] == "/workspace"
        )
        controlled_bind = next(
            mount for mount in n_mounts if mount[2] == "/workspace/task"
        )
        self.assertEqual(workspace_bind[0], "--bind")
        self.assertEqual(controlled_bind[0], "--ro-bind")
        self.assertLess(workspace_bind[3], controlled_bind[3])

        n_destinations = {mount[2] for mount in n_mounts}
        l_destinations = {mount[2] for mount in l_mounts}
        self.assertNotIn("/library/NumStability", n_destinations)
        self.assertNotIn("/library/NumStability.lean", n_destinations)
        self.assertNotIn("/library-olean", n_destinations)
        self.assertIn("/library/NumStability", l_destinations)
        self.assertIn("/library/NumStability.lean", l_destinations)
        self.assertIn("/library-olean", l_destinations)
        for destination in (
            "/library/NumStability",
            "/library/NumStability.lean",
            "/library-olean",
        ):
            self.assertEqual(
                next(mount[0] for mount in l_mounts if mount[2] == destination),
                "--ro-bind",
            )

        self.assertIn(("--ro-bind", str(self.shared_olean), "/shared-olean"), {
            mount[:3] for mount in n_mounts
        })
        self.assertIn("/shared-olean", setenv_value(n_command, "LEAN_PATH").split(":"))
        self.assertIn("/shared-olean", setenv_value(l_command, "LEAN_PATH").split(":"))
        self.assertEqual(setenv_value(n_command, "SHELL"), "/offline-bash")
        self.assertEqual(
            setenv_value(n_command, NETWORK_VIOLATION_MARKER_ENV),
            "/workspace/.network-marker",
        )
        self.assertIn(
            ("--ro-bind", str(self.offline_shell), "/offline-bash"),
            {mount[:3] for mount in n_mounts},
        )
        self.assertIn("--share-net", n_command)
        self.assertIn("--share-net", l_command)
        self.assertIn("app-server", n_command)
        self.assertIn("--stdio", n_command)
        self.assertNotIn("exec", n_command)
        self.assertNotIn("--json", n_command)
        self.assertEqual(setenv_value(n_command, "HOME"), "/u501/tester")
        self.assertIn('history.persistence="none"', n_command)
        self.assertIn("memories.use_memories=false", n_command)
        self.assertIn("memories.generate_memories=false", n_command)
        self.assertIn("external_agent_memory_import", n_command)

        n_lean_path = setenv_value(n_command, "LEAN_PATH").split(":")
        l_lean_path = setenv_value(l_command, "LEAN_PATH").split(":")
        self.assertEqual(
            n_lean_path,
            [
                "/shared-olean",
                "/workspace/task/shared",
                "/packages/mathlib/.lake/build/lib/lean",
                "/packages/batteries/.lake/build/lib/lean",
                "/lean/lib/lean",
                "/workspace",
            ],
        )
        self.assertEqual(
            l_lean_path,
            [
                "/shared-olean",
                "/workspace/task/shared",
                "/library-olean",
                "/packages/mathlib/.lake/build/lib/lean",
                "/packages/batteries/.lake/build/lib/lean",
                "/lean/lib/lean",
                "/workspace",
            ],
        )

    def test_lean_validator_namespace_has_shared_olean_but_only_l_has_library(self) -> None:
        n_args = self.lean_args("N")
        n_args.library_source = self.library_source
        n_args.library_root_file = self.library_root
        n_args.library_olean = self.library_olean
        n_command = namespace_prefix(n_args)
        l_command = namespace_prefix(self.lean_args("L"))
        n_destinations = {mount[2] for mount in mounts(n_command)}
        l_destinations = {mount[2] for mount in mounts(l_command)}
        self.assertIn("/shared-olean", n_destinations)
        self.assertIn("/shared-olean", l_destinations)
        self.assertNotIn("/library-olean", n_destinations)
        self.assertNotIn("/library/NumStability", n_destinations)
        self.assertIn("/library-olean", l_destinations)
        self.assertIn("/library/NumStability", l_destinations)
        self.assertNotIn("--share-net", n_command)
        self.assertNotIn("--share-net", l_command)

    def test_live_cap_and_advisory_rollout_budget_are_separate_options(self) -> None:
        self.assertEqual(positive_int("7"), 7)
        for raw in ("0", "-1", "not-an-int"):
            with self.assertRaises(argparse.ArgumentTypeError):
                positive_int(raw)
        args = self.codex_args("N")
        command = bubblewrap_command(args, self.state_home)
        self.assertEqual(
            command.count("features.rollout_budget.limit_tokens=4321"), 1
        )
        self.assertNotIn("features.rollout_budget.limit_tokens=1234", command)

        args.advisory_rollout_budget_limit = None
        fallback_command = bubblewrap_command(args, self.state_home)
        self.assertEqual(
            fallback_command.count("features.rollout_budget.limit_tokens=1234"), 1
        )

        advisory_action = next(
            action
            for action in codex_isolated.make_parser()._actions
            if action.dest == "advisory_rollout_budget_limit"
        )
        self.assertIsNone(advisory_action.default)
        self.assertEqual(advisory_action.type("99"), 99)
        with self.assertRaises(argparse.ArgumentTypeError):
            advisory_action.type("0")
        response_bound_action = next(
            action
            for action in codex_isolated.make_parser()._actions
            if action.dest == "provider_response_bound"
        )
        self.assertEqual(
            response_bound_action.type(str(codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND)),
            codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND,
        )
        compaction_canary_action = next(
            action
            for action in codex_isolated.make_parser()._actions
            if action.dest == "provider_token_gate_compaction_canary"
        )
        self.assertIs(compaction_canary_action.default, False)
        self.assertIs(compaction_canary_action.const, True)

        args.token_limit = 0
        with self.assertRaisesRegex(RuntimeError, "token limit must be positive"):
            bubblewrap_command(args, self.state_home)
        args.token_limit = 1234
        args.advisory_rollout_budget_limit = 0
        with self.assertRaisesRegex(RuntimeError, "advisory rollout-budget"):
            bubblewrap_command(args, self.state_home)

    def test_ultra_bubblewrap_enables_frozen_subagent_configuration(self) -> None:
        args = self.codex_args("N")
        args.reasoning_effort = "ultra"
        command = bubblewrap_command(args, self.state_home)
        adjacent = set(zip(command, command[1:]))
        self.assertIn(("--enable", "multi_agent"), adjacent)
        self.assertNotIn(("--disable", "multi_agent"), adjacent)
        for expected in (
            'model_reasoning_effort="ultra"',
            'agents.default_subagent_model="test-model"',
            'agents.default_subagent_reasoning_effort="ultra"',
            "features.multi_agent_v2.expose_spawn_agent_model_overrides=false",
            "features.multi_agent_v2.hide_spawn_agent_metadata=true",
            "features.multi_agent_v2.max_concurrent_threads_per_session=4",
            "features.multi_agent_v2.usage_hint_enabled=true",
            "features.multi_agent_v2.usage_hint_text="
            + json.dumps(codex_isolated.ULTRA_FORK_USAGE_HINT),
            'history.persistence="none"',
        ):
            self.assertEqual(command.count(expected), 1)
        self.assertIn(("--enable", "hooks"), adjacent)
        self.assertIn(("--enable", "remote_compaction_v2"), adjacent)
        self.assertIn(("--disable", "enable_request_compression"), adjacent)
        self.assertEqual(
            command.count(
                f'model_provider="{codex_isolated.PROVIDER_GATE_PROVIDER_ID}"'
            ),
            1,
        )
        provider_config = next(
            value
            for value in command
            if value.startswith(
                f"model_providers.{codex_isolated.PROVIDER_GATE_PROVIDER_ID}="
            )
        )
        for fragment in (
            'name="OpenAI"',
            'wire_api="responses"',
            "requires_openai_auth=true",
            "supports_websockets=false",
            "request_max_retries=0",
            "stream_max_retries=0",
        ):
            self.assertIn(fragment, provider_config)
        self.assertIn(args.provider_gate_base_url, provider_config)
        self.assertEqual(
            command.count(
                f"model_context_window={codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND}"
            ),
            1,
        )
        codex_index = max(
            index for index, value in enumerate(command) if value == "/codex"
        )
        bypass_index = command.index("--dangerously-bypass-hook-trust")
        app_server_index = command.index("app-server")
        self.assertEqual(bypass_index, codex_index + 1)
        self.assertEqual(app_server_index, bypass_index + 1)
        policy = codex_isolated.ultra_fork_policy_static_record("/u501/tester")
        self.assertIs(policy["hook_trust_bypass_cli_flag_present"], True)
        self.assertEqual(
            policy["hook_trust_bypass_thread_config"],
            {codex_isolated.ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True},
        )
        self.assertEqual(
            policy["hook_trust_bypass_effective_source"],
            codex_isolated.ULTRA_FORK_POLICY_TRUST_BYPASS_EFFECTIVE_SOURCE,
        )
        policy_mounts = {
            destination: (kind, Path(source), index)
            for kind, source, destination, index in mounts(command)
            if destination
            in {
                policy["source_path"],
                "/u501/tester/.codex/"
                + codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME,
            }
        }
        self.assertEqual(set(policy_mounts), {
            policy["source_path"],
            "/u501/tester/.codex/"
            + codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME,
        })
        home_mount_index = next(
            index for _kind, _source, destination, index in mounts(command)
            if destination == "/u501/tester"
        )
        for kind, source, index in policy_mounts.values():
            self.assertEqual(kind, "--ro-bind")
            self.assertGreater(index, home_mount_index)
            self.assertEqual(source.parent, self.root / "policy")
            self.assertFalse(str(source).startswith(str(self.state_home) + os.sep))
        hooks_source = policy_mounts[str(policy["source_path"])][1]
        helper_source = policy_mounts[
            "/u501/tester/.codex/"
            + codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME
        ][1]
        self.assertEqual(
            hashlib.sha256(hooks_source.read_bytes()).hexdigest(),
            policy["hooks_json_sha256"],
        )
        self.assertEqual(
            hashlib.sha256(helper_source.read_bytes()).hexdigest(),
            policy["helper_sha256"],
        )
        self.assertEqual(stat.S_IMODE(hooks_source.stat().st_mode), 0o444)
        self.assertEqual(stat.S_IMODE(helper_source.stat().st_mode), 0o555)
        self.assertEqual(
            json.loads(hooks_source.read_text(encoding="utf-8")),
            {
                "hooks": {
                    "PreToolUse": [
                        {
                            "hooks": [
                                {
                                    "command": policy["command"],
                                    "timeout": 5,
                                    "type": "command",
                                }
                            ],
                            "matcher": codex_isolated.ULTRA_FORK_POLICY_MATCHER,
                        }
                    ]
                }
            },
        )
        for feature in codex_isolated.DISABLED_FEATURES:
            self.assertIn(("--disable", feature), adjacent)

    def test_ultra_fork_policy_helper_allows_only_omitted_all_and_none(self) -> None:
        args = self.codex_args("N")
        args.reasoning_effort = "ultra"
        command = bubblewrap_command(args, self.state_home)
        helper_source = next(
            Path(source)
            for kind, source, destination, _index in mounts(command)
            if kind == "--ro-bind"
            and destination.endswith(
                "/.codex/" + codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME
            )
        )

        def invoke(
            tool_input: object,
            *,
            call_id: str = "call_policy",
            tool_name: str = "spawn_agent",
        ) -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                ["/usr/bin/python3.10", str(helper_source)],
                input=json.dumps(
                    {
                        "hook_event_name": "PreToolUse",
                        "tool_name": tool_name,
                        "tool_use_id": call_id,
                        "tool_input": tool_input,
                    }
                ),
                text=True,
                capture_output=True,
                check=False,
            )

        for allowed in (
            {"message": "task", "task_name": "worker"},
            {"message": "task", "task_name": "worker", "fork_turns": "all"},
            {"message": "task", "task_name": "worker", "fork_turns": "none"},
        ):
            with self.subTest(allowed=allowed):
                result = invoke(allowed)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr, "")

        for tool_name in ("Agent", "spawn_agent", "collaborationspawn_agent"):
            with self.subTest(tool_name=tool_name):
                result = invoke({"fork_turns": "all"}, tool_name=tool_name)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr, "")

        for denied in (
            {"fork_turns": "1"},
            {"fork_turns": "999"},
            {"fork_turns": "0"},
            {"fork_turns": "ALL"},
            {"fork_turns": 1},
            {"fork_turns": None},
            {"fork_turns": ["all"]},
        ):
            with self.subTest(denied=denied):
                result = invoke(denied)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(result.stderr, "")
                payload = json.loads(result.stdout)
                reason = codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id="call_policy"
                )
                self.assertEqual(
                    payload,
                    {
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": reason,
                        }
                    },
                )

        non_object = invoke([])
        self.assertEqual(
            json.loads(non_object.stdout)["hookSpecificOutput"][
                "permissionDecisionReason"
            ],
            codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                call_id="unknown"
            ),
        )
        malformed = invoke(
            {"fork_turns": "3"}, call_id="not-a-runtime-call-id"
        )
        self.assertEqual(
            json.loads(malformed.stdout)["hookSpecificOutput"][
                "permissionDecisionReason"
            ],
            codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                call_id="unknown"
            ),
        )
        wrong_tool = invoke({"fork_turns": "all"}, tool_name="collaboration.spawn_agent")
        self.assertEqual(
            json.loads(wrong_tool.stdout)["hookSpecificOutput"][
                "permissionDecisionReason"
            ],
            codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                call_id="unknown"
            ),
        )

    def test_ultra_fork_policy_artifact_tamper_fails_closed(self) -> None:
        args = self.codex_args("N")
        args.reasoning_effort = "ultra"
        bubblewrap_command(args, self.state_home)
        helper = self.root / "policy" / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME
        helper.chmod(0o644)
        with self.assertRaisesRegex(RuntimeError, "wrong mode"):
            bubblewrap_command(args, self.state_home)

    def test_pinned_app_server_dispatches_real_fork_policy_hook_offline(self) -> None:
        frozen_codex = (
            TOOLS.parent.parent
            / "scratch_pad"
            / "highambench_environment"
            / "codex-0.146.0-alpha.9.2"
        )
        if not frozen_codex.is_file():
            self.skipTest("pinned Codex binary is unavailable")
        call_id = "call_positivehook"
        requests: list[dict[str, object]] = []

        def usage(input_tokens: int, output_tokens: int) -> dict[str, object]:
            return {
                "input_tokens": input_tokens,
                "input_tokens_details": {"cached_tokens": 0},
                "output_tokens": output_tokens,
                "output_tokens_details": {"reasoning_tokens": 0},
                "total_tokens": input_tokens + output_tokens,
            }

        def sse(events: list[dict[str, object]]) -> bytes:
            return "".join(
                f"event: {event['type']}\ndata: "
                + json.dumps(event, separators=(",", ":"))
                + "\n\n"
                for event in events
            ).encode("utf-8")

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def do_POST(self) -> None:  # noqa: N802
                length = int(self.headers.get("Content-Length", "0"))
                request = json.loads(self.rfile.read(length))
                requests.append(request)
                if len(requests) == 1:
                    response_id = "resp_positive"
                    events = [
                        {
                            "type": "response.created",
                            "response": {"id": response_id},
                        },
                        {
                            "type": "response.output_item.done",
                            "output_index": 0,
                            "item": {
                                "type": "function_call",
                                "id": "fc_positivehook",
                                "status": "completed",
                                "call_id": call_id,
                                "name": "spawn_agent",
                                "namespace": "collaboration",
                                "arguments": json.dumps(
                                    {
                                        "task_name": "blocked_positive",
                                        "message": "bounded offline test",
                                        "fork_turns": "3",
                                    },
                                    separators=(",", ":"),
                                ),
                            },
                        },
                        {
                            "type": "response.completed",
                            "response": {
                                "id": response_id,
                                "usage": usage(10, 2),
                            },
                        },
                    ]
                else:
                    response_id = "resp_final"
                    events = [
                        {
                            "type": "response.created",
                            "response": {"id": response_id},
                        },
                        {
                            "type": "response.output_item.done",
                            "output_index": 0,
                            "item": {
                                "type": "message",
                                "id": "msg_final",
                                "status": "completed",
                                "role": "assistant",
                                "content": [
                                    {
                                        "type": "output_text",
                                        "text": "done",
                                        "annotations": [],
                                    }
                                ],
                            },
                        },
                        {
                            "type": "response.completed",
                            "response": {
                                "id": response_id,
                                "usage": usage(14, 1),
                            },
                        },
                    ]
                body = sse(events)
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, _format: str, *_args: object) -> None:
                return

        try:
            server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        except PermissionError:
            self.skipTest("loopback sockets are unavailable in this sandbox")
        server_thread = threading.Thread(target=server.serve_forever, daemon=True)
        server_thread.start()
        process: subprocess.Popen[str] | None = None
        try:
            home = self.root / "pinned-home"
            codex_home = home / ".codex"
            codex_home.mkdir(parents=True)
            policy_root = self.root / "pinned-policy-root"
            policy_root.mkdir()
            hooks_source, helper_source, policy = (
                codex_isolated._prepare_ultra_fork_policy(
                    policy_root, str(home)
                )
            )
            shutil.copyfile(hooks_source, codex_home / "hooks.json")
            shutil.copyfile(
                helper_source,
                codex_home / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME,
            )
            (codex_home / "hooks.json").chmod(0o444)
            (
                codex_home / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME
            ).chmod(0o555)
            workspace = self.root / "pinned-workspace"
            workspace.mkdir()
            model_catalog = policy_root / "offline-model-catalog.json"
            model_catalog.write_text(
                json.dumps(
                    {
                        "models": [
                            {
                                "slug": "gpt-5.6-sol",
                                "display_name": "GPT-5.6-Sol (offline fixture)",
                                "description": "Pinned offline V2 dispatch fixture.",
                                "default_reasoning_level": "ultra",
                                "supported_reasoning_levels": [
                                    {
                                        "effort": "ultra",
                                        "description": "Offline hook dispatch",
                                    }
                                ],
                                "shell_type": "shell_command",
                                "visibility": "list",
                                "supported_in_api": True,
                                "priority": 1,
                                "additional_speed_tiers": [],
                                "service_tiers": [],
                                "availability_nux": None,
                                "upgrade": None,
                                "base_instructions": "Offline hook dispatch test.",
                                "include_skills_usage_instructions": False,
                                "include_plugin_usage_instructions": False,
                                "default_reasoning_summary": "none",
                                "support_verbosity": False,
                                "default_verbosity": None,
                                "apply_patch_tool_type": None,
                                "web_search_tool_type": "text",
                                "truncation_policy": {
                                    "mode": "tokens",
                                    "limit": 10_000,
                                },
                                "supports_parallel_tool_calls": True,
                                "supports_image_detail_original": False,
                                "context_window": 272_000,
                                "max_context_window": 272_000,
                                "comp_hash": "offline-v2-hook-dispatch",
                                "effective_context_window_percent": 95,
                                "experimental_supported_tools": [],
                                "input_modalities": ["text"],
                                "supports_search_tool": False,
                                "use_responses_lite": False,
                                "tool_mode": "code_mode_only",
                                "multi_agent_version": "v2",
                            }
                        ]
                    },
                    separators=(",", ":"),
                )
                + "\n",
                encoding="utf-8",
            )
            port = server.server_address[1]
            provider = (
                '{name="offline_mock",base_url="http://127.0.0.1:'
                f'{port}/v1",env_key="HIGHAMBENCH_MOCK_API_KEY",'
                'wire_api="responses"}'
            )
            command = [
                str(frozen_codex),
                "app-server",
                "--stdio",
                "--strict-config",
                "--config",
                'model_provider="offline_mock"',
                "--config",
                "model_catalog_json=" + json.dumps(str(model_catalog)),
                "--config",
                f"model_providers.offline_mock={provider}",
                "--config",
                'model="gpt-5.6-sol"',
                "--config",
                'model_reasoning_effort="ultra"',
                "--config",
                'approval_policy="never"',
                "--config",
                'sandbox_mode="danger-full-access"',
                "--config",
                'history.persistence="none"',
                "--config",
                'agents.default_subagent_model="gpt-5.6-sol"',
                "--config",
                'agents.default_subagent_reasoning_effort="ultra"',
                "--config",
                "features.multi_agent_v2.expose_spawn_agent_model_overrides=false",
                "--config",
                "features.multi_agent_v2.hide_spawn_agent_metadata=true",
                "--config",
                "features.multi_agent_v2.max_concurrent_threads_per_session=4",
                "--config",
                "features.multi_agent_v2.usage_hint_enabled=true",
                "--config",
                "features.multi_agent_v2.usage_hint_text="
                + json.dumps(codex_isolated.ULTRA_FORK_USAGE_HINT),
                "--enable",
                "hooks",
                "--enable",
                "multi_agent",
            ]
            environment = {
                "CODEX_HOME": str(codex_home),
                "HOME": str(home),
                "HIGHAMBENCH_MOCK_API_KEY": "offline-test-key",
                "PATH": "/usr/bin:/bin",
            }
            process = subprocess.Popen(
                command,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
                cwd=workspace,
                env=environment,
            )
            assert process.stdin is not None and process.stdout is not None
            messages: queue.Queue[dict[str, object] | BaseException] = queue.Queue()

            def read_protocol() -> None:
                try:
                    for line in process.stdout:
                        parsed = json.loads(line)
                        if isinstance(parsed, dict):
                            messages.put(parsed)
                except BaseException as error:
                    messages.put(error)

            reader = threading.Thread(target=read_protocol, daemon=True)
            reader.start()
            notifications: list[dict[str, object]] = []

            def send(message: dict[str, object]) -> None:
                process.stdin.write(json.dumps(message, separators=(",", ":")) + "\n")
                process.stdin.flush()

            def await_response(request_id: int) -> dict[str, object]:
                deadline = time.monotonic() + 20.0
                while True:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise AssertionError(f"timed out waiting for response {request_id}")
                    item = messages.get(timeout=remaining)
                    if isinstance(item, BaseException):
                        raise item
                    if item.get("id") == request_id and "method" not in item:
                        if "error" in item:
                            raise AssertionError(item["error"])
                        return item
                    notifications.append(item)

            send(
                {
                    "id": 1,
                    "method": "initialize",
                    "params": {
                        "clientInfo": {"name": "offline-hook-test", "version": "1"},
                        "capabilities": {"experimentalApi": True},
                    },
                }
            )
            await_response(1)
            send({"method": "initialized"})
            send(
                {
                    "id": 10,
                    "method": "hooks/list",
                    "params": {"cwds": [str(workspace)]},
                }
            )
            hooks_response = await_response(10)
            self.assertEqual(
                len(hooks_response["result"]["data"][0]["hooks"]),
                1,
                hooks_response,
            )
            self.assertEqual(
                hooks_response["result"]["data"][0]["hooks"][0]["trustStatus"],
                "untrusted",
                hooks_response,
            )
            send(
                {
                    "id": 2,
                    "method": "thread/start",
                    "params": {
                        "approvalPolicy": "never",
                        "config": {
                            codex_isolated.ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True
                        },
                        "cwd": str(workspace),
                        "ephemeral": False,
                        "experimentalRawEvents": True,
                        "historyMode": "legacy",
                        "model": "gpt-5.6-sol",
                        "sandbox": "danger-full-access",
                    },
                }
            )
            thread_response = await_response(2)
            thread_id = thread_response["result"]["thread"]["id"]
            send(
                {
                    "id": 3,
                    "method": "turn/start",
                    "params": {
                        "approvalPolicy": "never",
                        "cwd": str(workspace),
                        "effort": "ultra",
                        "input": [{"type": "text", "text": "offline hook test"}],
                        "model": "gpt-5.6-sol",
                        "sandboxPolicy": {"type": "dangerFullAccess"},
                        "threadId": thread_id,
                    },
                }
            )
            await_response(3)
            deadline = time.monotonic() + 20.0
            while not any(
                item.get("method") == "turn/completed"
                and item.get("params", {}).get("threadId") == thread_id
                for item in notifications
            ):
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    stderr = process.stderr.read() if process.stderr is not None else ""
                    raise AssertionError(f"timed out waiting for turn completion: {stderr}")
                item = messages.get(timeout=remaining)
                if isinstance(item, BaseException):
                    raise item
                notifications.append(item)

            hook_events = [
                item
                for item in notifications
                if item.get("method")
                in {
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                }
            ]
            self.assertEqual(
                [item["method"] for item in hook_events],
                [
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
                    codex_isolated.ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
                ],
                {
                    "hooks": hook_events,
                    "loaded_hooks": hooks_response["result"]["data"][0]["hooks"],
                    "notification_methods": [
                        item.get("method") for item in notifications
                    ],
                    "request_tool_names": [
                        tool.get("name")
                        for request in requests
                        for tool in request.get("tools", [])
                        if isinstance(tool, dict)
                    ],
                    "raw_tool_items": [
                        {
                            key: raw_item.get(key)
                            for key in (
                                "type",
                                "name",
                                "namespace",
                                "call_id",
                                "output",
                            )
                            if key in raw_item
                        }
                        for notification in notifications
                        if notification.get("method") == "rawResponseItem/completed"
                        and isinstance(
                            raw_item := notification.get("params", {}).get("item"),
                            dict,
                        )
                        and raw_item.get("type")
                        in {"function_call", "function_call_output"}
                    ],
                },
            )
            completed_run = hook_events[1]["params"]["run"]
            self.assertEqual(completed_run["status"], "blocked")
            self.assertEqual(
                completed_run["entries"],
                [
                    {
                        "kind": "feedback",
                        "text": codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                            call_id=call_id
                        ),
                    }
                ],
            )
            ledger = AttemptUsageLedger(
                self.root / "pinned-hook-usage.json",
                10_000,
                str(thread_id),
                fork_policy=policy,
            )
            for item in notifications:
                ledger.observe(item)
            snapshot = ledger.snapshot(drain_complete=ledger.quiescent())
            self.assertEqual(snapshot["hook_blocked_spawn_call_ids"], [call_id])
            self.assertEqual(snapshot["policy_blocked_spawn_call_ids"], [call_id])
            self.assertEqual(snapshot["failed_spawn_call_ids"], [call_id])
            self.assertEqual(snapshot["inference_child_thread_ids"], [])
            self.assertTrue(snapshot["fork_policy_complete"], snapshot)
            self.assertTrue(snapshot["measurement_exact"], snapshot)
            self.assertEqual(len(requests), 2)
            blocked_outputs = [
                item
                for item in requests[1]["input"]
                if item.get("type") == "function_call_output"
                and item.get("call_id") == call_id
            ]
            self.assertEqual(len(blocked_outputs), 1)
            reason = codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                call_id=call_id
            )
            self.assertEqual(
                blocked_outputs,
                [
                    {
                        "type": "function_call_output",
                        "call_id": call_id,
                        "id": blocked_outputs[0]["id"],
                        "output": (
                            f"Tool call blocked by PreToolUse hook: {reason}. "
                            "Tool: collaborationspawn_agent"
                        ),
                    }
                ],
            )
        finally:
            if process is not None:
                codex_isolated._stop_child(process)
                if process.stdout is not None:
                    process.stdout.close()
                if process.stderr is not None:
                    process.stderr.close()
            server.shutdown()
            server.server_close()
            server_thread.join(timeout=2)

    def test_pinned_app_server_gate_buffers_crossing_and_releases_below_cap(self) -> None:
        """Exercise the real app-server through the trusted buffering proxy.

        The first response is released byte-for-byte and starts a subagent.  Its
        follow-up is the sole exclusive request and crosses the cap.  That
        upstream body deliberately contains every action-shaped output we need
        to quarantine; Codex may observe only the minimal completed response.
        """

        frozen_codex = (
            TOOLS.parent.parent
            / "scratch_pad"
            / "highambench_environment"
            / "codex-0.146.0-alpha.9.2"
        )
        if not frozen_codex.is_file():
            self.skipTest("pinned Codex binary is unavailable")

        upstream_requests: list[dict[str, object]] = []
        upstream_paths: list[str] = []

        def provider_usage(
            input_tokens: int,
            output_tokens: int,
            *,
            cached_tokens: int,
            cache_write_tokens: int,
            reasoning_tokens: int,
        ) -> dict[str, object]:
            return {
                "input_tokens": input_tokens,
                "input_tokens_details": {
                    "cached_tokens": cached_tokens,
                    "cache_write_tokens": cache_write_tokens,
                },
                "output_tokens": output_tokens,
                "output_tokens_details": {
                    "reasoning_tokens": reasoning_tokens,
                },
                "total_tokens": input_tokens + output_tokens,
            }

        def sse(events: list[dict[str, object]]) -> bytes:
            return "".join(
                f"event: {event['type']}\ndata: "
                + json.dumps(event, separators=(",", ":"))
                + "\n\n"
                for event in events
            ).encode("utf-8")

        first_response_id = "resp_gate_below"
        spawn_call_id = "call_gate_spawn"
        first_usage = provider_usage(
            10,
            2,
            cached_tokens=2,
            cache_write_tokens=1,
            reasoning_tokens=1,
        )
        first_body = sse(
            [
                {
                    "type": "response.created",
                    "response": {"id": first_response_id},
                },
                {
                    "type": "response.output_item.done",
                    "output_index": 0,
                    "item": {
                        "type": "function_call",
                        "id": "fc_gate_spawn",
                        "status": "completed",
                        "call_id": spawn_call_id,
                        "name": "spawn_agent",
                        "namespace": "collaboration",
                        "arguments": json.dumps(
                            {
                                "task_name": "gate_child",
                                "message": "Finish the bounded offline task.",
                                "fork_turns": "none",
                            },
                            separators=(",", ":"),
                        ),
                    },
                },
                {
                    "type": "response.completed",
                    "response": {
                        "id": first_response_id,
                        "usage": first_usage,
                    },
                },
            ]
        )

        crossing_response_id = "resp_gate_crossing"
        crossing_usage = provider_usage(
            9_000,
            1_000,
            cached_tokens=100,
            cache_write_tokens=50,
            reasoning_tokens=500,
        )
        crossing_action_ids = {
            "msg_gate_crossing",
            "fc_gate_cross_exec",
            "fc_gate_cross_spawn",
            "ct_gate_cross_submit",
            "call_gate_cross_exec",
            "call_gate_cross_spawn",
            "call_gate_cross_submit",
        }
        crossing_body = sse(
            [
                {
                    "type": "response.created",
                    "response": {"id": crossing_response_id},
                },
                {
                    "type": "response.output_item.done",
                    "output_index": 0,
                    "item": {
                        "type": "message",
                        "id": "msg_gate_crossing",
                        "status": "completed",
                        "role": "assistant",
                        "content": [
                            {
                                "type": "output_text",
                                "text": "this crossing message must remain quarantined",
                                "annotations": [],
                            }
                        ],
                    },
                },
                {
                    "type": "response.output_item.done",
                    "output_index": 1,
                    "item": {
                        "type": "function_call",
                        "id": "fc_gate_cross_exec",
                        "status": "completed",
                        "call_id": "call_gate_cross_exec",
                        "name": "exec",
                        "arguments": '{"cmd":"touch crossing-exec-ran"}',
                    },
                },
                {
                    "type": "response.output_item.done",
                    "output_index": 2,
                    "item": {
                        "type": "function_call",
                        "id": "fc_gate_cross_spawn",
                        "status": "completed",
                        "call_id": "call_gate_cross_spawn",
                        "name": "spawn_agent",
                        "namespace": "collaboration",
                        "arguments": (
                            '{"task_name":"must_not_spawn","message":"quarantined",'
                            '"fork_turns":"none"}'
                        ),
                    },
                },
                {
                    "type": "response.output_item.done",
                    "output_index": 3,
                    "item": {
                        "type": "custom_tool_call",
                        "id": "ct_gate_cross_submit",
                        "status": "completed",
                        "call_id": "call_gate_cross_submit",
                        "name": "submit_proof",
                        "input": '{"candidate_path":"crossing-candidate.lean"}',
                    },
                },
                {
                    "type": "response.completed",
                    "response": {
                        "id": crossing_response_id,
                        "usage": crossing_usage,
                    },
                },
            ]
        )
        served_bodies = [first_body, crossing_body]

        class UpstreamHandler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def do_POST(self) -> None:  # noqa: N802
                length = int(self.headers.get("Content-Length", "0"))
                request_body = self.rfile.read(length)
                parsed = json.loads(request_body)
                if not isinstance(parsed, dict):
                    raise AssertionError("mock upstream request is not an object")
                upstream_requests.append(parsed)
                upstream_paths.append(self.path)
                index = len(upstream_requests) - 1
                if index >= len(served_bodies):
                    raise AssertionError("provider gate made a post-crossing upstream call")
                body = served_bodies[index]
                self.send_response(200)
                self.send_header("Content-Encoding", "identity")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, _format: str, *_args: object) -> None:
                return

        try:
            upstream = ThreadingHTTPServer(("127.0.0.1", 0), UpstreamHandler)
        except PermissionError:
            self.skipTest("loopback sockets are unavailable in this sandbox")
        upstream_thread = threading.Thread(target=upstream.serve_forever, daemon=True)
        upstream_thread.start()

        gate: codex_isolated.ProviderTokenGate | None = None
        process: subprocess.Popen[str] | None = None
        gate_finalized = False
        teardown: dict[str, object] | None = None
        try:
            upstream_port = int(upstream.server_address[1])
            gate_live = self.root / "pinned-gate.live.json"
            gate_final = self.root / "pinned-gate.json"
            gate = codex_isolated.ProviderTokenGate(
                gate_live,
                gate_final,
                token_limit=10_000,
                response_bound=codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND,
                model_catalog_sha256="a" * 64,
                model_entry_sha256="b" * 64,
                capability_nonce="c" * 32,
                _connection_factory=lambda: http.client.HTTPConnection(
                    "127.0.0.1", upstream_port, timeout=10
                ),
            )
            try:
                gate_base_url = gate.start()
            except PermissionError:
                self.skipTest("provider-gate loopback socket is unavailable")

            home = self.root / "pinned-gate-home"
            codex_home = home / ".codex"
            codex_home.mkdir(parents=True)
            (codex_home / "auth.json").write_text(
                '{"OPENAI_API_KEY":"offline-test-key"}\n', encoding="utf-8"
            )
            (codex_home / "auth.json").chmod(0o600)
            policy_root = self.root / "pinned-gate-policy"
            policy_root.mkdir()
            hooks_source, helper_source, policy = (
                codex_isolated._prepare_ultra_fork_policy(policy_root, str(home))
            )
            shutil.copyfile(hooks_source, codex_home / "hooks.json")
            shutil.copyfile(
                helper_source,
                codex_home / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME,
            )
            (codex_home / "hooks.json").chmod(0o444)
            (
                codex_home / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME
            ).chmod(0o555)

            workspace = self.root / "pinned-gate-workspace"
            workspace.mkdir()
            model_catalog = policy_root / "offline-model-catalog.json"
            model_catalog.write_text(
                json.dumps(
                    {
                        "models": [
                            {
                                "slug": "gpt-5.6-sol",
                                "display_name": "GPT-5.6-Sol (gate fixture)",
                                "description": "Pinned provider-gate buffering fixture.",
                                "default_reasoning_level": "ultra",
                                "supported_reasoning_levels": [
                                    {
                                        "effort": "ultra",
                                        "description": "Offline gate buffering",
                                    }
                                ],
                                "shell_type": "shell_command",
                                "visibility": "list",
                                "supported_in_api": True,
                                "priority": 1,
                                "additional_speed_tiers": [],
                                "service_tiers": [],
                                "availability_nux": None,
                                "upgrade": None,
                                "base_instructions": "Offline gate test.",
                                "include_skills_usage_instructions": False,
                                "include_plugin_usage_instructions": False,
                                "default_reasoning_summary": "none",
                                "support_verbosity": False,
                                "default_verbosity": None,
                                "apply_patch_tool_type": None,
                                "web_search_tool_type": "text",
                                "truncation_policy": {"mode": "tokens", "limit": 10_000},
                                "supports_parallel_tool_calls": True,
                                "supports_image_detail_original": False,
                                "context_window": 272_000,
                                "max_context_window": 272_000,
                                "comp_hash": "offline-provider-gate-buffering",
                                "effective_context_window_percent": 95,
                                "experimental_supported_tools": [],
                                "input_modalities": ["text"],
                                "supports_search_tool": False,
                                "use_responses_lite": False,
                                "tool_mode": "code_mode_only",
                                "multi_agent_version": "v2",
                            }
                        ]
                    },
                    separators=(",", ":"),
                )
                + "\n",
                encoding="utf-8",
            )
            provider = codex_isolated._provider_gate_config(gate_base_url)
            command = [
                str(frozen_codex),
                "app-server",
                "--stdio",
                "--strict-config",
                "--config",
                f'model_provider="{codex_isolated.PROVIDER_GATE_PROVIDER_ID}"',
                "--config",
                "model_catalog_json=" + json.dumps(str(model_catalog)),
                "--config",
                f"model_providers.{codex_isolated.PROVIDER_GATE_PROVIDER_ID}={provider}",
                "--config",
                'model="gpt-5.6-sol"',
                "--config",
                'model_reasoning_effort="ultra"',
                "--config",
                f"model_context_window={codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND}",
                "--config",
                'approval_policy="never"',
                "--config",
                'sandbox_mode="danger-full-access"',
                "--config",
                'history.persistence="none"',
                "--config",
                'agents.default_subagent_model="gpt-5.6-sol"',
                "--config",
                'agents.default_subagent_reasoning_effort="ultra"',
                "--config",
                "features.multi_agent_v2.expose_spawn_agent_model_overrides=false",
                "--config",
                "features.multi_agent_v2.hide_spawn_agent_metadata=true",
                "--config",
                "features.multi_agent_v2.max_concurrent_threads_per_session=4",
                "--disable",
                "enable_request_compression",
                "--enable",
                "remote_compaction_v2",
                "--enable",
                "hooks",
                "--enable",
                "multi_agent",
            ]
            environment = {
                "CODEX_HOME": str(codex_home),
                "HOME": str(home),
                "OPENAI_API_KEY": "offline-test-key",
                "PATH": "/usr/bin:/bin",
            }
            process = subprocess.Popen(
                command,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
                cwd=workspace,
                env=environment,
                start_new_session=True,
            )
            assert process.stdin is not None and process.stdout is not None
            messages: queue.Queue[dict[str, object] | BaseException] = queue.Queue()

            def read_protocol() -> None:
                try:
                    for line in process.stdout:
                        parsed = json.loads(line)
                        if isinstance(parsed, dict):
                            messages.put(parsed)
                except BaseException as error:
                    messages.put(error)

            reader = threading.Thread(target=read_protocol, daemon=True)
            reader.start()
            notifications: list[dict[str, object]] = []
            sent_methods: list[str] = []

            def send(message: dict[str, object]) -> None:
                method = message.get("method")
                if isinstance(method, str):
                    sent_methods.append(method)
                process.stdin.write(json.dumps(message, separators=(",", ":")) + "\n")
                process.stdin.flush()

            def await_response(request_id: int) -> dict[str, object]:
                deadline = time.monotonic() + 20.0
                while True:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise AssertionError(f"timed out waiting for response {request_id}")
                    item = messages.get(timeout=remaining)
                    if isinstance(item, BaseException):
                        raise item
                    if item.get("id") == request_id and "method" not in item:
                        if "error" in item:
                            raise AssertionError(item["error"])
                        return item
                    notifications.append(item)

            send(
                {
                    "id": 1,
                    "method": "initialize",
                    "params": {
                        "clientInfo": {"name": "offline-gate-test", "version": "1"},
                        "capabilities": {"experimentalApi": True},
                    },
                }
            )
            await_response(1)
            send({"method": "initialized"})
            send(
                {
                    "id": 2,
                    "method": "thread/start",
                    "params": {
                        "approvalPolicy": "never",
                        "config": {
                            codex_isolated.ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True
                        },
                        "cwd": str(workspace),
                        "dynamicTools": [
                            codex_isolated.SubmissionBarrier.dynamic_tool_spec()
                        ],
                        "ephemeral": False,
                        "experimentalRawEvents": True,
                        "historyMode": "legacy",
                        "model": "gpt-5.6-sol",
                        "sandbox": "danger-full-access",
                    },
                }
            )
            thread_response = await_response(2)
            thread_id = str(thread_response["result"]["thread"]["id"])
            self.assertEqual(thread_response["result"]["reasoningEffort"], "ultra")
            gate.bind_root(
                thread_id,
                run_id="pinned-offline-gate",
                model="gpt-5.6-sol",
                reasoning_effort="ultra",
            )
            effective_prompt = "offline provider gate buffering test"
            gate.bind_prompt_release(
                codex_isolated.authenticated_record(
                    {
                        "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
                        "effective_prompt_sha256": hashlib.sha256(
                            effective_prompt.encode("utf-8")
                        ).hexdigest(),
                        "root_thread_id": thread_id,
                        "run_id": "pinned-offline-gate",
                        "model": "gpt-5.6-sol",
                        "reasoning_effort": "ultra",
                    },
                    "release_sha256",
                )
            )
            ledger = AttemptUsageLedger(
                self.root / "pinned-gate-usage.json",
                10_000,
                thread_id,
                fork_policy=policy,
                provider_gate=gate,
                provider_gate_artifact_path=gate_final,
            )
            notifications.clear()
            send(
                {
                    "id": 3,
                    "method": "turn/start",
                    "params": {
                        "approvalPolicy": "never",
                        "cwd": str(workspace),
                        "effort": "ultra",
                        "input": [{"type": "text", "text": effective_prompt}],
                        "model": "gpt-5.6-sol",
                        "sandboxPolicy": {"type": "dangerFullAccess"},
                        "threadId": thread_id,
                    },
                }
            )
            turn_response = await_response(3)
            ledger.root_turn_id = str(turn_response["result"]["turn"]["id"])

            crossing_event: dict[str, object] | None = None

            def observe(item: dict[str, object]) -> None:
                nonlocal crossing_event
                if ledger.observe(item):
                    crossing_event = item

            already_seen = list(notifications)
            notifications.clear()
            for item in already_seen:
                notifications.append(item)
                observe(item)
            deadline = time.monotonic() + 20.0
            while crossing_event is None:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    stderr = process.stderr.read() if process.stderr is not None else ""
                    raise AssertionError(f"timed out waiting for gate crossing: {stderr}")
                item = messages.get(timeout=remaining)
                if isinstance(item, BaseException):
                    raise item
                notifications.append(item)
                observe(item)

            self.assertEqual(len(upstream_requests), 2)
            self.assertEqual(crossing_event["method"], "rawResponse/completed")
            crossing_params = crossing_event["params"]
            self.assertEqual(crossing_params["responseId"], crossing_response_id)
            self.assertEqual(
                crossing_params["usage"],
                {
                    "inputTokens": 9_000,
                    "cachedInputTokens": 100,
                    "cacheWriteInputTokens": 50,
                    "outputTokens": 1_000,
                    "reasoningOutputTokens": 500,
                    "totalTokens": 10_000,
                },
            )

            gate.stop()
            terminal = gate.snapshot()
            self.assertEqual(terminal["active_handler_count"], 0)
            self.assertTrue(terminal["handlers_quiescent"])
            record = gate.finalize()
            gate_finalized = True
            verified = codex_isolated.validate_provider_gate_artifact(gate_final)
            self.assertEqual(record, verified)
            self.assertTrue(
                codex_isolated._provider_gate_matches_ledger(
                    verified,
                    terminal,
                    ledger,
                    close_reason=codex_isolated.PROVIDER_GATE_CLOSE_TOKEN_LIMIT,
                )
            )
            ledger.attach_provider_gate_final(
                verified,
                terminal,
                exact_for_usage=True,
            )

            teardown = codex_isolated._stop_child(
                process,
                process_group=True,
                immediate=True,
            )
            if process.stdout is not None:
                process.stdout.close()
            if process.stderr is not None:
                process.stderr.close()
            process = None
            ledger.attach_adapter_teardown(teardown)
            ledger.publish(drain_complete=False)
            self.assertTrue(teardown["completed"])
            self.assertTrue(teardown["process_group_isolated"])
            self.assertTrue(teardown["immediate"])

            self.assertEqual(
                upstream_paths,
                ["/backend-api/codex/responses", "/backend-api/codex/responses"],
            )
            calls = verified["calls"]
            self.assertEqual(verified["setup_requests"], [])
            self.assertEqual(
                [call["admission_mode"] for call in calls],
                ["EXCLUSIVE", "EXCLUSIVE"],
            )
            self.assertTrue(all(call["open_before"] == 0 for call in calls))
            below, crossing = calls
            self.assertEqual(below["release_kind"], "byte_identity")
            for call in calls:
                self.assertIsNone(call["upstream_content_type"])
                self.assertEqual(call["upstream_content_type_occurrences"], 0)
                authentication = call["upstream_sse_authentication"]
                self.assertTrue(authentication["complete"])
                self.assertEqual(
                    authentication["content_type_basis"],
                    "authenticated_stream_request_header_absent",
                )
                self.assertTrue(
                    authentication["downstream_content_type_synthesized"]
                )
                self.assertEqual(
                    authentication["completed_event_index"],
                    authentication["json_event_count"] - 1,
                )
            self.assertEqual(
                below["upstream_body_sha256"], hashlib.sha256(first_body).hexdigest()
            )
            self.assertEqual(
                below["released_body_sha256"], below["upstream_body_sha256"]
            )
            self.assertEqual(below["released_body_bytes"], len(first_body))
            self.assertEqual(
                crossing["release_kind"], "sanitized_crossing_completion"
            )
            self.assertEqual(
                crossing["upstream_body_sha256"],
                hashlib.sha256(crossing_body).hexdigest(),
            )
            sanitized = provider_token_gate.sanitized_completion_body(
                crossing_response_id, crossing_usage
            )
            self.assertEqual(
                crossing["released_sanitized_body_utf8"],
                sanitized.decode("utf-8"),
            )
            self.assertEqual(
                crossing["released_body_sha256"], hashlib.sha256(sanitized).hexdigest()
            )
            self.assertTrue(crossing["client_release_complete"])
            self.assertEqual(
                crossing["appserver_crossbind"]["normalized_usage"],
                ledger.responses[crossing_response_id]["usage"],
            )
            self.assertEqual(
                set(crossing["appserver_crossbind"]["normalized_usage"]),
                provider_token_gate.PROVIDER_GATE_NORMALIZED_USAGE_KEYS,
            )
            self.assertEqual(
                crossing["appserver_crossbind"]["event_sequence"],
                ledger.responses[crossing_response_id]["sequence"],
            )
            self.assertEqual(terminal["close_reason"], "token_limit")
            self.assertTrue(terminal["crossing_closed"])
            self.assertEqual(terminal["open_request_ids"], [])
            self.assertTrue(terminal["no_post_close_upstream"])
            self.assertTrue(all(verified["invariants"].values()), verified)

            raw_items = [
                item.get("params", {}).get("item", {})
                for item in notifications
                if item.get("method") == "rawResponseItem/completed"
            ]
            observed_action_ids = {
                value
                for item in raw_items
                if isinstance(item, dict)
                for key in ("id", "call_id")
                if isinstance(value := item.get(key), str)
            }
            self.assertTrue(
                any(item.get("call_id") == spawn_call_id for item in raw_items)
            )
            self.assertTrue(crossing_action_ids.isdisjoint(observed_action_ids))
            self.assertFalse((workspace / "crossing-exec-ran").exists())
            self.assertFalse((workspace / "crossing-candidate.lean").exists())
            self.assertNotIn("turn/interrupt", sent_methods)
            self.assertEqual(len(upstream_requests), 2)
            usage_snapshot = ledger.snapshot(drain_complete=False)
            self.assertTrue(usage_snapshot["measurement_exact"], usage_snapshot)
            self.assertEqual(usage_snapshot["response_count"], 2)
            self.assertEqual(
                usage_snapshot["first_crossing"]["response_id"],
                crossing_response_id,
            )
        finally:
            if process is not None:
                teardown = codex_isolated._stop_child(
                    process,
                    process_group=True,
                    immediate=True,
                )
                if process.stdout is not None:
                    process.stdout.close()
                if process.stderr is not None:
                    process.stderr.close()
            if gate is not None and not gate_finalized:
                with contextlib.suppress(Exception):
                    gate.close(codex_isolated.PROVIDER_GATE_CLOSE_SYSTEM_ERROR)
                    gate.stop()
                    gate.finalize()
            upstream.shutdown()
            upstream.server_close()
            upstream_thread.join(timeout=2)

    def test_pinned_app_server_gate_sanitizes_remote_compaction_crossing(self) -> None:
        """Exercise the v3 compaction crossing through the pinned app-server."""

        frozen_codex = (
            TOOLS.parent.parent
            / "scratch_pad"
            / "highambench_environment"
            / "codex-0.146.0-alpha.9.2"
        )
        if not frozen_codex.is_file():
            self.skipTest("pinned Codex binary is unavailable")

        def usage(total: int) -> dict[str, object]:
            return {
                "input_tokens": total - 5,
                "input_tokens_details": {
                    "cached_tokens": 2,
                    "cache_write_tokens": 1,
                },
                "output_tokens": 5,
                "output_tokens_details": {"reasoning_tokens": 1},
                "total_tokens": total,
            }

        def sse(events: list[dict[str, object]]) -> bytes:
            return "".join(
                f"event: {event['type']}\ndata: "
                + json.dumps(event, separators=(",", ":"))
                + "\n\n"
                for event in events
            ).encode("utf-8")

        first_response_id = "resp_compaction_probe_initial"
        compact_response_id = "resp_compaction_probe_crossing"
        first_usage = usage(40)
        compact_usage = usage(100)
        first_body = sse(
            [
                {
                    "type": "response.output_item.done",
                    "item": {
                        "type": "message",
                        "id": "msg_compaction_probe_initial",
                        "status": "completed",
                        "role": "assistant",
                        "content": [
                            {
                                "type": "output_text",
                                "text": "HIGHAMBENCH_COMPACTION_READY",
                                "annotations": [],
                            }
                        ],
                    },
                },
                {
                    "type": "response.completed",
                    "response": {"id": first_response_id, "usage": first_usage},
                },
            ]
        )
        compact_body = sse(
            [
                {
                    "type": "response.output_item.done",
                    "item": {
                        "type": "compaction",
                        "encrypted_content": "opaque-compaction-probe",
                    },
                },
                {
                    "type": "response.completed",
                    "response": {
                        "id": compact_response_id,
                        "usage": compact_usage,
                    },
                },
            ]
        )
        served = [first_body, compact_body]
        upstream_headers: list[dict[str, str]] = []
        upstream_paths: list[str] = []

        class UpstreamHandler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def do_POST(self) -> None:  # noqa: N802
                length = int(self.headers.get("Content-Length", "0"))
                self.rfile.read(length)
                upstream_paths.append(self.path)
                upstream_headers.append(
                    {name.lower(): value for name, value in self.headers.items()}
                )
                index = len(upstream_paths) - 1
                if index >= len(served):
                    raise AssertionError("post-crossing provider request escaped")
                body = served[index]
                self.send_response(200)
                if index == 0:
                    self.send_header("Content-Type", "text/event-stream")
                self.send_header("Content-Encoding", "identity")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, _format: str, *_args: object) -> None:
                return

        try:
            upstream = ThreadingHTTPServer(("127.0.0.1", 0), UpstreamHandler)
        except PermissionError:
            self.skipTest("loopback sockets are unavailable in this sandbox")
        upstream_thread = threading.Thread(target=upstream.serve_forever, daemon=True)
        upstream_thread.start()

        gate: codex_isolated.ProviderTokenGate | None = None
        process: subprocess.Popen[str] | None = None
        finalized = False
        try:
            upstream_port = int(upstream.server_address[1])
            gate_live = self.root / "pinned-compact-gate.live.json"
            gate_final = self.root / "pinned-compact-gate.json"
            gate = codex_isolated.ProviderTokenGate(
                gate_live,
                gate_final,
                token_limit=100,
                response_bound=codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND,
                model_catalog_sha256="a" * 64,
                model_entry_sha256="b" * 64,
                capability_nonce="e" * 32,
                _connection_factory=lambda: http.client.HTTPConnection(
                    "127.0.0.1", upstream_port, timeout=10
                ),
            )
            gate_base_url = gate.start()

            home = self.root / "pinned-compact-home"
            codex_home = home / ".codex"
            codex_home.mkdir(parents=True)
            (codex_home / "auth.json").write_text(
                '{"OPENAI_API_KEY":"offline-test-key"}\n', encoding="utf-8"
            )
            (codex_home / "auth.json").chmod(0o600)
            policy_root = self.root / "pinned-compact-policy"
            policy_root.mkdir()
            hooks_source, helper_source, policy = (
                codex_isolated._prepare_ultra_fork_policy(policy_root, str(home))
            )
            shutil.copyfile(hooks_source, codex_home / "hooks.json")
            shutil.copyfile(
                helper_source,
                codex_home / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME,
            )
            (codex_home / "hooks.json").chmod(0o444)
            (
                codex_home / codex_isolated.ULTRA_FORK_POLICY_HELPER_FILENAME
            ).chmod(0o555)
            workspace = self.root / "pinned-compact-workspace"
            workspace.mkdir()
            model_catalog = policy_root / "offline-model-catalog.json"
            model_catalog.write_text(
                json.dumps(
                    {
                        "models": [
                            {
                                "slug": "gpt-5.6-sol",
                                "display_name": "GPT-5.6-Sol (compaction fixture)",
                                "description": "Pinned compaction crossing fixture.",
                                "default_reasoning_level": "ultra",
                                "supported_reasoning_levels": [
                                    {"effort": "ultra", "description": "Offline"}
                                ],
                                "shell_type": "shell_command",
                                "visibility": "list",
                                "supported_in_api": True,
                                "priority": 1,
                                "additional_speed_tiers": [],
                                "service_tiers": [],
                                "availability_nux": None,
                                "upgrade": None,
                                "base_instructions": "Offline compaction gate test.",
                                "include_skills_usage_instructions": False,
                                "include_plugin_usage_instructions": False,
                                "default_reasoning_summary": "none",
                                "support_verbosity": False,
                                "default_verbosity": None,
                                "apply_patch_tool_type": None,
                                "web_search_tool_type": "text",
                                "truncation_policy": {"mode": "tokens", "limit": 10_000},
                                "supports_parallel_tool_calls": True,
                                "supports_image_detail_original": False,
                                "context_window": 272_000,
                                "max_context_window": 272_000,
                                "comp_hash": "offline-compaction-gate",
                                "effective_context_window_percent": 95,
                                "experimental_supported_tools": [],
                                "input_modalities": ["text"],
                                "supports_search_tool": False,
                                "use_responses_lite": False,
                                "tool_mode": "code_mode_only",
                                "multi_agent_version": "v2",
                            }
                        ]
                    },
                    separators=(",", ":"),
                )
                + "\n",
                encoding="utf-8",
            )
            provider = codex_isolated._provider_gate_config(gate_base_url)
            command = [
                str(frozen_codex),
                "app-server",
                "--stdio",
                "--strict-config",
                "--config",
                f'model_provider="{codex_isolated.PROVIDER_GATE_PROVIDER_ID}"',
                "--config",
                "model_catalog_json=" + json.dumps(str(model_catalog)),
                "--config",
                f"model_providers.{codex_isolated.PROVIDER_GATE_PROVIDER_ID}={provider}",
                "--config",
                'model="gpt-5.6-sol"',
                "--config",
                'model_reasoning_effort="ultra"',
                "--config",
                f"model_context_window={codex_isolated.PROVIDER_RESPONSE_TOKEN_BOUND}",
                "--config",
                'approval_policy="never"',
                "--config",
                'sandbox_mode="danger-full-access"',
                "--config",
                'history.persistence="none"',
                "--disable",
                "enable_request_compression",
                "--enable",
                "remote_compaction_v2",
                "--enable",
                "hooks",
                "--enable",
                "multi_agent",
            ]
            process = subprocess.Popen(
                command,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
                cwd=workspace,
                env={
                    "CODEX_HOME": str(codex_home),
                    "HOME": str(home),
                    "OPENAI_API_KEY": "offline-test-key",
                    "PATH": "/usr/bin:/bin",
                },
                start_new_session=True,
            )
            assert process.stdin is not None and process.stdout is not None
            messages: queue.Queue[dict[str, object] | BaseException] = queue.Queue()

            def read_protocol() -> None:
                try:
                    for line in process.stdout:
                        parsed = json.loads(line)
                        if isinstance(parsed, dict):
                            messages.put(parsed)
                except BaseException as error:
                    messages.put(error)

            threading.Thread(target=read_protocol, daemon=True).start()
            notifications: list[dict[str, object]] = []

            def send(message: dict[str, object]) -> None:
                process.stdin.write(json.dumps(message, separators=(",", ":")) + "\n")
                process.stdin.flush()

            def next_message() -> dict[str, object]:
                item = messages.get(timeout=20)
                if isinstance(item, BaseException):
                    raise item
                return item

            class QueueReader:
                def get(self, timeout: float | None = None) -> dict[str, object]:
                    item = messages.get(timeout=timeout)
                    if isinstance(item, BaseException):
                        raise item
                    return item

            def await_response(request_id: int) -> dict[str, object]:
                while True:
                    item = next_message()
                    if item.get("id") == request_id and "method" not in item:
                        if "error" in item:
                            raise AssertionError(item["error"])
                        return item
                    notifications.append(item)

            send(
                {
                    "id": 1,
                    "method": "initialize",
                    "params": {
                        "clientInfo": {"name": "offline-compact-test", "version": "1"},
                        "capabilities": {"experimentalApi": True},
                    },
                }
            )
            await_response(1)
            send({"method": "initialized"})
            send(
                {
                    "id": 2,
                    "method": "thread/start",
                    "params": {
                        "approvalPolicy": "never",
                        "config": {
                            codex_isolated.ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True
                        },
                        "cwd": str(workspace),
                        "dynamicTools": [
                            codex_isolated.SubmissionBarrier.dynamic_tool_spec()
                        ],
                        "ephemeral": False,
                        "experimentalRawEvents": True,
                        "historyMode": "legacy",
                        "model": "gpt-5.6-sol",
                        "sandbox": "danger-full-access",
                    },
                }
            )
            thread_response = await_response(2)
            thread_id = str(thread_response["result"]["thread"]["id"])
            gate.bind_root(
                thread_id,
                run_id="pinned-offline-compaction",
                model="gpt-5.6-sol",
                reasoning_effort="ultra",
            )
            effective_prompt = "return the readiness marker"
            gate.bind_prompt_release(
                codex_isolated.authenticated_record(
                    {
                        "protocol_version": codex_isolated.PROMPT_RELEASE_PROTOCOL_VERSION,
                        "effective_prompt_sha256": hashlib.sha256(
                            effective_prompt.encode("utf-8")
                        ).hexdigest(),
                        "root_thread_id": thread_id,
                        "run_id": "pinned-offline-compaction",
                        "model": "gpt-5.6-sol",
                        "reasoning_effort": "ultra",
                    },
                    "release_sha256",
                )
            )
            ledger = AttemptUsageLedger(
                self.root / "pinned-compact-usage.json",
                100,
                thread_id,
                fork_policy=policy,
                provider_gate=gate,
                provider_gate_artifact_path=gate_final,
            )

            def observe(item: dict[str, object]) -> None:
                ledger.observe(item)

            for item in list(notifications):
                observe(item)
            notifications.clear()
            send(
                {
                    "id": 3,
                    "method": "turn/start",
                    "params": {
                        "approvalPolicy": "never",
                        "cwd": str(workspace),
                        "effort": "ultra",
                        "input": [{"type": "text", "text": effective_prompt}],
                        "model": "gpt-5.6-sol",
                        "sandboxPolicy": {"type": "dangerFullAccess"},
                        "threadId": thread_id,
                    },
                }
            )
            turn_response = await_response(3)
            ledger.root_turn_id = str(turn_response["result"]["turn"]["id"])
            for item in list(notifications):
                observe(item)
            notifications.clear()
            while ledger.root_terminal_status() != "completed":
                item = next_message()
                notifications.append(item)
                observe(item)
            self.assertIsNone(ledger.first_crossing)
            self.assertEqual(gate.snapshot()["completed_tokens"], 40)

            def observe_compaction(item: dict[str, object]) -> None:
                notifications.append(item)
                observe(item)

            codex_isolated._drive_provider_gate_compaction_canary(
                process.stdin,
                QueueReader(),  # type: ignore[arg-type]
                ledger,
                gate,
                thread_id=thread_id,
                token_limit=100,
                on_notification=observe_compaction,  # type: ignore[arg-type]
            )

            # The completed compaction is not published until its sealed gate
            # call can be attached.  This prevents the live runner from seeing
            # a transient second response with a null provider edge.
            intermediate_usage = json.loads(ledger.output.read_text())
            self.assertEqual(intermediate_usage["response_count"], 1)
            self.assertEqual(
                intermediate_usage["response_ids"], [first_response_id]
            )

            gate.stop()
            terminal = gate.snapshot()
            verified = gate.finalize()
            finalized = True
            self.assertEqual(
                verified,
                codex_isolated.validate_provider_gate_artifact(gate_final),
            )
            self.assertTrue(
                codex_isolated._provider_gate_matches_ledger(
                    verified,
                    terminal,
                    ledger,
                    close_reason=codex_isolated.PROVIDER_GATE_CLOSE_TOKEN_LIMIT,
                )
            )
            teardown = codex_isolated._stop_child(
                process, process_group=True, immediate=True
            )
            process.stdout.close()
            if process.stderr is not None:
                process.stderr.close()
            process = None
            ledger.attach_provider_gate_final(verified, terminal, exact_for_usage=True)
            ledger.attach_adapter_teardown(teardown)
            ledger.publish(drain_complete=False)
            usage_snapshot = ledger.snapshot(drain_complete=False)

            self.assertEqual(
                upstream_paths,
                ["/backend-api/codex/responses", "/backend-api/codex/responses"],
            )
            metadata = [
                json.loads(headers["x-codex-turn-metadata"])
                for headers in upstream_headers
            ]
            self.assertEqual([item["request_kind"] for item in metadata], ["turn", "compaction"])
            for item in metadata:
                self.assertTrue(
                    all(
                        isinstance(item.get(key), str) and item[key]
                        for key in provider_token_gate.PROVIDER_GATE_REQUEST_METADATA_KEYS
                    ),
                    item,
                )
            first_call, compact_call = verified["calls"]
            self.assertEqual(first_call["release_kind"], "byte_identity")
            self.assertEqual(first_call["upstream_content_type_occurrences"], 1)
            self.assertFalse(
                first_call["upstream_sse_authentication"][
                    "downstream_content_type_synthesized"
                ]
            )
            self.assertEqual(
                compact_call["release_kind"],
                provider_token_gate.RELEASE_SANITIZED_COMPACTION_CROSSING,
            )
            self.assertIsNone(compact_call["upstream_content_type"])
            self.assertEqual(compact_call["upstream_content_type_occurrences"], 0)
            self.assertEqual(
                compact_call["upstream_sse_authentication"]["content_type_basis"],
                "authenticated_stream_request_header_absent",
            )
            self.assertTrue(
                compact_call["upstream_sse_authentication"][
                    "downstream_content_type_synthesized"
                ]
            )
            self.assertEqual(compact_call["request_metadata"]["request_kind"], "compaction")
            self.assertEqual(
                compact_call["released_sanitized_events"][0],
                {
                    "type": "response.output_item.done",
                    "item": {
                        "type": "compaction",
                        "encrypted_content": "opaque-compaction-probe",
                    },
                },
            )
            self.assertEqual(len(compact_call["released_sanitized_events"]), 2)
            self.assertEqual(terminal["crossing"]["request_kind"], "compaction")
            self.assertEqual(ledger.first_crossing["response_id"], compact_response_id)
            self.assertEqual(ledger.first_crossing["tokens"], 140)
            self.assertEqual(
                compact_call["appserver_crossbind"]["normalized_usage"],
                ledger.responses[compact_response_id]["usage"],
            )
            self.assertEqual(
                set(compact_call["appserver_crossbind"]["normalized_usage"]),
                provider_token_gate.PROVIDER_GATE_NORMALIZED_USAGE_KEYS,
            )
            compact_raw_responses = [
                item
                for item in notifications
                if item.get("method") == "rawResponse/completed"
                and item.get("params", {}).get("responseId")
                == compact_response_id
            ]
            self.assertEqual(len(compact_raw_responses), 1)
            self.assertEqual(
                set(compact_raw_responses[0]["params"]["usage"]),
                {
                    "inputTokens",
                    "cachedInputTokens",
                    "cacheWriteInputTokens",
                    "outputTokens",
                    "reasoningOutputTokens",
                    "totalTokens",
                },
            )
            self.assertTrue(usage_snapshot["measurement_exact"], usage_snapshot)
            self.assertFalse(usage_snapshot["drain_complete"])
            self.assertFalse(usage_snapshot["accounting_complete"])
            self.assertFalse(usage_snapshot["cumulative_projection_complete"])
            self.assertTrue(usage_snapshot["descendant_accounting_complete"])
            self.assertTrue(usage_snapshot["spawn_linkage_complete"])
            self.assertTrue(usage_snapshot["fork_policy_complete"])
            self.assertEqual(usage_snapshot["thread_count"], 1)
            self.assertEqual(usage_snapshot["response_count"], 2)
            self.assertEqual(usage_snapshot["active_thread_ids"], [thread_id])
            root_projection = usage_snapshot["threads"][0]
            self.assertEqual(root_projection["thread_id"], thread_id)
            self.assertEqual(root_projection["turn_status"], "inProgress")
            self.assertNotEqual(
                root_projection["active_turn_id"], usage_snapshot["root_turn_id"]
            )
            self.assertEqual(
                usage_snapshot["response_ledger"][1]["turn_id"],
                root_projection["active_turn_id"],
            )
            self.assertFalse(
                any(item.get("method") == "turn/interrupt" for item in notifications)
            )
            self.assertEqual(len(upstream_paths), 2)
        finally:
            if process is not None:
                codex_isolated._stop_child(
                    process, process_group=True, immediate=True
                )
                if process.stdout is not None:
                    process.stdout.close()
                if process.stderr is not None:
                    process.stderr.close()
            if gate is not None and not finalized:
                with contextlib.suppress(Exception):
                    gate.close(codex_isolated.PROVIDER_GATE_CLOSE_SYSTEM_ERROR)
                    gate.stop()
                    gate.finalize()
            upstream.shutdown()
            upstream.server_close()
            upstream_thread.join(timeout=2)

    def test_compaction_crossing_publication_waits_for_gate_attachment(self) -> None:
        usage_path = self.root / "pending-compaction-usage.json"
        stable = b'{"stable":true}\n'
        usage_path.write_bytes(stable)
        ledger = AttemptUsageLedger(
            usage_path,
            100,
            "root-thread",
            provider_gate=mock.Mock(),
        )
        ledger.compaction_canary_authorized = True
        ledger.compaction_turn_id = "compact-turn"
        ledger.compaction_response_id = "compact-response"
        ledger.first_crossing = {"response_id": "compact-response"}

        ledger.publish()
        self.assertEqual(usage_path.read_bytes(), stable)

        ledger.provider_gate_final = {"attached": True}
        with mock.patch.object(
            ledger, "snapshot", return_value={"attached": True}
        ):
            ledger.publish()
        self.assertEqual(json.loads(usage_path.read_text()), {"attached": True})

        ledger.provider_gate_final = None
        with mock.patch.object(
            ledger, "snapshot", return_value={"final_drain": True}
        ):
            ledger.publish(drain_complete=True)
        self.assertEqual(json.loads(usage_path.read_text()), {"final_drain": True})

    def test_condition_l_requires_both_library_mounts(self) -> None:
        args = self.codex_args("L")
        args.library_olean = None
        with self.assertRaisesRegex(RuntimeError, "condition L requires"):
            bubblewrap_command(args, self.state_home)
        lean_args = self.lean_args("L")
        lean_args.library_source = None
        with self.assertRaisesRegex(RuntimeError, "condition L requires"):
            namespace_prefix(lean_args)

    def test_codex_usage_output_must_be_outside_model_workspace(self) -> None:
        args = self.codex_args("N")
        args.usage_output = self.workspace / "usage.json"
        with self.assertRaisesRegex(RuntimeError, "outside the model-writable workspace"):
            run_codex_isolated(args)

    def test_materialized_root_attestation_is_mandatory(self) -> None:
        codex_isolated._require_materialized_thread(
            {"thread": {"id": "root", "ephemeral": False}}
        )
        for bad in (
            {"thread": {"id": "root", "ephemeral": True}},
            {"thread": {"id": "root"}},
            {},
        ):
            with self.subTest(bad=bad), self.assertRaisesRegex(
                RuntimeError, "materialized root thread|thread record"
            ):
                codex_isolated._require_materialized_thread(bad)

    def test_state_cleanup_retries_and_fails_closed(self) -> None:
        state = self.root / "retry-state"
        state.mkdir()
        (state / "rollout.jsonl").write_text("private\n", encoding="utf-8")
        real_rmtree = shutil.rmtree
        calls = 0

        def flaky_rmtree(path: Path) -> None:
            nonlocal calls
            calls += 1
            if calls < 3:
                raise OSError("transient NFS cleanup race")
            real_rmtree(path)

        with mock.patch.object(
            codex_isolated.shutil, "rmtree", side_effect=flaky_rmtree
        ), mock.patch.object(codex_isolated.time, "sleep"):
            codex_isolated._remove_state_root(state)
        self.assertEqual(calls, 3)
        self.assertFalse(state.exists())

        stuck = self.root / "stuck-state"
        stuck.mkdir()
        with mock.patch.object(
            codex_isolated.shutil,
            "rmtree",
            side_effect=OSError("persistent cleanup failure"),
        ), mock.patch.object(codex_isolated.time, "sleep"):
            with self.assertRaisesRegex(
                RuntimeError, "could not remove temporary Codex state directory"
            ):
                codex_isolated._remove_state_root(stuck)
        self.assertTrue(stuck.exists())

    def test_mock_ultra_protocol_requests_raw_events_and_materialized_thread(self) -> None:
        prompt_file = self.root / "ultra-prompt.md"
        context_file = self.root / "ultra-context.md"
        target_file = self.root / "UltraTarget.lean"
        auth_file = self.root / "ultra-auth.json"
        state_parent = self.root / "ultra-states"
        usage_output = self.root / "ultra-trusted-logs" / "usage.json"
        prompt_file.write_text("Write the Ultra proof.", encoding="utf-8")
        context_file.write_text("Fixed Ultra context.", encoding="utf-8")
        target_file.write_text(
            "theorem ultra_fixed : True := by\n  sorry\n", encoding="utf-8"
        )
        auth_file.write_text('{"token":"test-only"}\n', encoding="utf-8")
        challenge_path = codex_isolated.submission_barrier_paths(usage_output)[
            "challenge"
        ]
        challenge_path.parent.mkdir(parents=True, exist_ok=True)
        challenge_path.write_text(
            json.dumps(
                codex_isolated.authenticated_record(
                    {
                        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                        "kind": "highambench_submission_challenge",
                        "run_id": "mock-ultra",
                        "attempt_nonce": "test-nonce",
                        "validator_contract_sha256": "a" * 64,
                        **codex_isolated.nested_submission_exec_yield_record(),
                    },
                    "challenge_sha256",
                )
            )
            + "\n",
            encoding="utf-8",
        )

        events = [
            json.dumps({"id": 1, "result": {"codexHome": "/state/.codex"}})
            + "\n",
            json.dumps(
                {
                    "method": "thread/started",
                    "params": {"thread": {"id": "ultra-root"}},
                }
            )
            + "\n",
            json.dumps(
                {
                    "id": 2,
                    "result": {
                        "thread": {"id": "ultra-root", "ephemeral": False},
                        "model": "test-model",
                        "reasoningEffort": "ultra",
                    },
                }
            )
            + "\n",
            json.dumps(
                turn_event("turn/started", "ultra-root", "ultra-turn", "inProgress")
            )
            + "\n",
            json.dumps({"id": 3, "result": {"turn": {"id": "ultra-turn"}}})
            + "\n",
            json.dumps(
                raw_response_event(
                    "ultra-response",
                    "ultra-root",
                    "ultra-turn",
                    input_tokens=12,
                    cached_input_tokens=4,
                    cache_write_input_tokens=1,
                    output_tokens=3,
                    reasoning_output_tokens=2,
                )
            )
            + "\n",
            json.dumps(
                cumulative_usage_event(
                    "ultra-root",
                    "ultra-turn",
                    input_tokens=12,
                    cached_input_tokens=4,
                    cache_write_input_tokens=1,
                    output_tokens=3,
                    reasoning_output_tokens=2,
                )
            )
            + "\n",
            json.dumps(
                turn_event("turn/completed", "ultra-root", "ultra-turn", "completed")
            )
            + "\n",
        ]

        class RecordingInput(io.StringIO):
            def __init__(self, temporary_auth: Path) -> None:
                super().__init__()
                self.temporary_auth = temporary_auth
                self.messages: list[dict[str, object]] = []

            def write(self, value: str) -> int:
                message = json.loads(value)
                if message.get("method") == "turn/start":
                    if self.temporary_auth.exists():
                        raise AssertionError("turn/start was sent before auth removal")
                self.messages.append(message)
                return len(value)

        class FakeProcess:
            def __init__(self, command: list[str]) -> None:
                state_source = next(
                    Path(source)
                    for _kind, source, destination, _index in mounts(command)
                    if destination == "/u501/tester"
                )
                self.stdin = RecordingInput(state_source / ".codex" / "auth.json")
                self.stdout = io.StringIO("".join(events))
                self.returncode: int | None = None
                self.terminated = False

            def poll(self) -> int | None:
                return self.returncode

            def terminate(self) -> None:
                self.terminated = True
                self.returncode = -15

            def kill(self) -> None:
                self.returncode = -9

            def wait(self, timeout: float | None = None) -> int:
                del timeout
                if self.returncode is None:
                    self.returncode = 0
                return self.returncode

        args = self.codex_args("N")
        args.reasoning_effort = "ultra"
        args.prompt_file = prompt_file
        args.context_file = context_file
        args.target_file = target_file
        args.usage_output = usage_output
        args.auth_file = auth_file
        args.state_parent = state_parent
        go_thread = self.enable_prompt_handshake(args, usage_output)
        created: list[FakeProcess] = []

        def fake_popen(command: list[str], **_kwargs: object) -> FakeProcess:
            adjacent = set(zip(command, command[1:]))
            self.assertIn(("--enable", "multi_agent"), adjacent)
            process = FakeProcess(command)
            created.append(process)
            return process

        class FakeProviderTokenGate:
            """In-memory gate for this app-server protocol fixture.

            The proxy transport itself has focused integration coverage below;
            this test only needs the app-server side of the public gate API and
            must remain runnable in test sandboxes that forbid loopback binds.
            """

            def __init__(self, *_args: object, token_limit: int, **_kwargs: object) -> None:
                self.token_limit = token_limit
                self.completed_tokens = 0
                self.close_reason: str | None = None
                self.bound_root: tuple[str, str, str, str] | None = None
                self.prompt_release: dict[str, object] | None = None

            def start(self) -> str:
                return (
                    "http://127.0.0.1:23456/"
                    + "e" * 32
                    + "/backend-api/codex"
                )

            def bind_root(
                self,
                root_thread_id: str,
                *,
                run_id: str,
                model: str,
                reasoning_effort: str,
            ) -> None:
                self.bound_root = (
                    root_thread_id,
                    run_id,
                    model,
                    reasoning_effort,
                )

            def bind_prompt_release(self, record: Mapping[str, object]) -> None:
                self.prompt_release = dict(record)

            def crossbind_appserver_response(
                self,
                _response_id: str,
                usage: Mapping[str, object],
                **_identity: object,
            ) -> None:
                self.completed_tokens += int(usage["total_tokens"])

            def close(self, reason: str) -> dict[str, object]:
                self.close_reason = reason
                return {
                    "won": True,
                    "requested_reason": reason,
                    "effective_reason": reason,
                    "phase": "CLOSED",
                    "sequence": 1,
                }

            def snapshot(self) -> dict[str, object]:
                return {
                    "phase": "CLOSED" if self.close_reason else "CONCURRENT",
                    "close_reason": self.close_reason,
                    "completed_tokens": self.completed_tokens,
                    "crossing": None,
                    "crossing_closed": False,
                    "open_request_ids": [],
                    "all_complete": True,
                    "no_post_close_upstream": True,
                    "poisoned": False,
                    "poison_reasons": [],
                    "sequence": 1,
                }

        def fake_finalize_gate(
            gate: FakeProviderTokenGate,
            ledger: codex_isolated.AttemptUsageLedger,
            _artifact_path: Path,
            *,
            close_reason: str,
            drain_complete: bool,
        ) -> dict[str, object]:
            gate.close(close_reason)
            terminal = gate.snapshot()
            record: dict[str, object] = {
                "record_sha256": "f" * 64,
                "calls": [],
                "state": terminal,
            }
            ledger.attach_provider_gate_final(
                record,
                terminal,
                exact_for_usage=True,
            )
            ledger.publish(drain_complete=drain_complete)
            return record

        with (
            mock.patch.object(codex_isolated.subprocess, "Popen", side_effect=fake_popen),
            mock.patch.object(
                codex_isolated,
                "ProviderTokenGate",
                FakeProviderTokenGate,
            ),
            mock.patch.object(
                codex_isolated,
                "_finalize_provider_gate_for_ledger",
                side_effect=fake_finalize_gate,
            ),
            mock.patch.dict(
                os.environ,
                {NETWORK_VIOLATION_MARKER_ENV: str(self.network_marker)},
            ),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            self.assertEqual(run_codex_isolated(args), 0)
        go_thread.join(timeout=2)

        self.assertEqual(len(created), 1)
        self.assertEqual(created[0].returncode, 0)
        self.assertFalse(created[0].terminated)
        messages = created[0].stdin.messages
        self.assertEqual(
            [message.get("method") for message in messages],
            ["initialize", "initialized", "thread/start", "turn/start"],
        )
        self.assertEqual(
            messages[0]["params"]["capabilities"],
            {"experimentalApi": True},
        )
        thread_params = messages[2]["params"]
        self.assertEqual(
            set(thread_params),
            {
                "approvalPolicy",
                "config",
                "cwd",
                "ephemeral",
                "experimentalRawEvents",
                "historyMode",
                "dynamicTools",
                "model",
                "sandbox",
            },
        )
        self.assertIs(thread_params["ephemeral"], False)
        self.assertEqual(
            thread_params["config"],
            {codex_isolated.ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True},
        )
        self.assertIs(thread_params["experimentalRawEvents"], True)
        self.assertEqual(thread_params["historyMode"], "legacy")
        self.assertEqual(
            thread_params["dynamicTools"][0]["name"], "submit_proof"
        )
        self.assertEqual(messages[3]["params"]["effort"], "ultra")
        snapshot = json.loads(usage_output.read_text(encoding="utf-8"))
        self.assertEqual(snapshot["measurement_source"], codex_isolated.ULTRA_USAGE_MEASUREMENT_SOURCE)
        self.assertEqual(snapshot["usage_scope"], codex_isolated.ULTRA_USAGE_SCOPE)
        self.assertEqual(snapshot["thread_count"], 1)
        self.assertEqual(snapshot["response_count"], 1)
        self.assertEqual(snapshot["total_tokens"], 15)
        self.assertTrue(snapshot["drain_complete"])
        self.assertTrue(snapshot["measurement_exact"])
        release = codex_isolated.read_authenticated_record_file(
            args.prompt_release_output, "release_sha256"
        )
        self.assertEqual(release["kind"], codex_isolated.PROMPT_RELEASED_KIND)
        self.assertEqual(release["root_thread_id"], "ultra-root")
        self.assertEqual(release["turn_start_write_state"], "flushed")
        self.assertLessEqual(
            release["released_at_monotonic_ns"],
            release["turn_start_flushed_at_monotonic_ns"],
        )
        self.assertEqual(
            release["effective_prompt_sha256"],
            hashlib.sha256(
                build_prompt(prompt_file, context_file, target_file).encode("utf-8")
            ).hexdigest(),
        )
        self.assertEqual(list(state_parent.iterdir()), [])

    def test_ultra_error_cleanup_seals_poison_and_publishes_inexact_usage(self) -> None:
        """A gate/app-server mismatch must leave authenticated failure evidence."""

        try:
            socket_probe = ThreadingHTTPServer(
                ("127.0.0.1", 0), BaseHTTPRequestHandler
            )
        except PermissionError:
            self.skipTest("loopback sockets are unavailable in this sandbox")
        else:
            socket_probe.server_close()

        prompt_file = self.root / "poison-prompt.md"
        context_file = self.root / "poison-context.md"
        target_file = self.root / "PoisonTarget.lean"
        auth_file = self.root / "poison-auth.json"
        state_parent = self.root / "poison-states"
        usage_output = self.root / "poison-logs" / "usage.json"
        prompt_file.write_text("Exercise gate mismatch cleanup.", encoding="utf-8")
        context_file.write_text("Fixed context.", encoding="utf-8")
        target_file.write_text("theorem poison_target : True := by\n  sorry\n", encoding="utf-8")
        auth_file.write_text('{"token":"test-only"}\n', encoding="utf-8")
        challenge_path = codex_isolated.submission_barrier_paths(usage_output)[
            "challenge"
        ]
        challenge_path.parent.mkdir(parents=True, exist_ok=True)
        challenge_path.write_text(
            json.dumps(
                codex_isolated.authenticated_record(
                    {
                        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
                        "kind": "highambench_submission_challenge",
                        "run_id": "direct-adapter-test",
                        "attempt_nonce": "test-nonce",
                        "validator_contract_sha256": "a" * 64,
                        **codex_isolated.nested_submission_exec_yield_record(),
                    },
                    "challenge_sha256",
                )
            )
            + "\n",
            encoding="utf-8",
        )
        events = [
            json.dumps({"id": 1, "result": {"codexHome": "/state/.codex"}}) + "\n",
            json.dumps(
                {
                    "method": "thread/started",
                    "params": {"thread": {"id": "poison-root"}},
                }
            )
            + "\n",
            json.dumps(
                {
                    "id": 2,
                    "result": {
                        "thread": {"id": "poison-root", "ephemeral": False},
                        "model": "test-model",
                        "reasoningEffort": "ultra",
                    },
                }
            )
            + "\n",
            json.dumps(
                turn_event(
                    "turn/started", "poison-root", "poison-turn", "inProgress"
                )
            )
            + "\n",
            json.dumps({"id": 3, "result": {"turn": {"id": "poison-turn"}}})
            + "\n",
            # There was no corresponding provider admission.  Cross-binding
            # this app-server identity must poison the gate and abort the run.
            json.dumps(
                raw_response_event(
                    "unknown-provider-response",
                    "poison-root",
                    "poison-turn",
                    input_tokens=5,
                    cached_input_tokens=1,
                    cache_write_input_tokens=1,
                    output_tokens=2,
                    reasoning_output_tokens=1,
                )
            )
            + "\n",
        ]

        class FakeProcess:
            def __init__(self, command: list[str]) -> None:
                state_source = next(
                    Path(source)
                    for _kind, source, destination, _index in mounts(command)
                    if destination == "/u501/tester"
                )
                self.stdin = io.StringIO()
                self.stdout = io.StringIO("".join(events))
                self.returncode: int | None = None
                self.temporary_auth = state_source / ".codex" / "auth.json"

            def poll(self) -> int | None:
                return self.returncode

            def terminate(self) -> None:
                self.returncode = -15

            def kill(self) -> None:
                self.returncode = -9

            def wait(self, timeout: float | None = None) -> int:
                del timeout
                if self.returncode is None:
                    self.returncode = 0
                return self.returncode

        args = self.codex_args("N")
        args.reasoning_effort = "ultra"
        args.prompt_file = prompt_file
        args.context_file = context_file
        args.target_file = target_file
        args.usage_output = usage_output
        args.auth_file = auth_file
        args.state_parent = state_parent
        go_thread = self.enable_prompt_handshake(args, usage_output)
        created: list[FakeProcess] = []

        def fake_popen(command: list[str], **_kwargs: object) -> FakeProcess:
            process = FakeProcess(command)
            created.append(process)
            return process

        with (
            mock.patch.object(codex_isolated.subprocess, "Popen", side_effect=fake_popen),
            mock.patch.dict(
                os.environ,
                {NETWORK_VIOLATION_MARKER_ENV: str(self.network_marker)},
            ),
            contextlib.redirect_stdout(io.StringIO()),
            self.assertRaisesRegex(
                provider_token_gate.ProviderGateError,
                "response ID is unknown",
            ),
        ):
            run_codex_isolated(args)
        go_thread.join(timeout=2)

        self.assertEqual(len(created), 1)
        self.assertEqual(created[0].returncode, -15)
        gate_path = codex_isolated.provider_gate_paths(usage_output)["final"]
        artifact = codex_isolated.validate_provider_gate_artifact(gate_path)
        self.assertEqual(artifact["state"]["phase"], "POISONED")
        self.assertEqual(artifact["state"]["close_reason"], "poison")
        self.assertIn(
            "unknown_appserver_response_crossbind",
            artifact["state"]["poison_reasons"],
        )
        self.assertTrue(artifact["state"]["handlers_quiescent"])
        self.assertFalse(artifact["invariants"]["not_poisoned"])
        usage = json.loads(usage_output.read_text(encoding="utf-8"))
        self.assertFalse(usage["measurement_exact"])
        self.assertFalse(usage["provider_token_gate"]["exact_for_usage"])
        self.assertTrue(usage["provider_token_gate"]["final_attached"])
        self.assertEqual(
            usage["provider_token_gate"]["record_sha256"],
            artifact["record_sha256"],
        )
        self.assertEqual(
            usage["provider_token_gate"]["terminal"], artifact["state"]
        )
        self.assertTrue(usage["adapter_teardown"]["completed"])
        self.assertTrue(usage["adapter_teardown"]["immediate"])
        self.assertEqual(list(state_parent.iterdir()), [])

    def test_mock_app_server_protocol_streams_cumulative_usage_and_removes_auth(self) -> None:
        prompt_file = self.root / "prompt.md"
        context_file = self.root / "context.md"
        target_file = self.root / "Target.lean"
        auth_file = self.root / "auth.json"
        state_parent = self.root / "states"
        usage_output = self.root / "trusted-logs" / "usage.json"
        prompt_file.write_text("Write the proof.", encoding="utf-8")
        context_file.write_text("Fixed context.", encoding="utf-8")
        target_file.write_text("theorem fixed : True := by\n  sorry\n", encoding="utf-8")
        auth_file.write_text('{"token":"test-only"}\n', encoding="utf-8")

        events = [
            "mock app-server diagnostic\n",
            json.dumps({"id": 1, "result": {"codexHome": "/state/.codex"}}) + "\n",
            json.dumps(
                {
                    "method": "thread/started",
                    "params": {"thread": {"id": "thread-1"}},
                }
            )
            + "\n",
            json.dumps(
                {
                    "id": 2,
                    "result": {
                        "thread": {"id": "thread-1", "ephemeral": False}
                    },
                }
            )
            + "\n",
            json.dumps(
                {
                    "method": "turn/started",
                    "params": {
                        "threadId": "thread-1",
                        "turn": {"id": "turn-1", "status": "inProgress"},
                    },
                }
            )
            + "\n",
            json.dumps({"id": 3, "result": {"turn": {"id": "turn-1"}}})
            + "\n",
        ]
        for input_tokens, cached_tokens, output_tokens in ((20, 5, 3), (31, 8, 7)):
            events.append(
                json.dumps(
                    {
                        "method": "thread/tokenUsage/updated",
                        "params": {
                            "threadId": "thread-1",
                            "turnId": "turn-1",
                            "tokenUsage": {
                                "last": {
                                    "inputTokens": input_tokens,
                                    "cachedInputTokens": cached_tokens,
                                    "outputTokens": output_tokens,
                                    "reasoningOutputTokens": 1,
                                    "totalTokens": input_tokens + output_tokens,
                                },
                                "total": {
                                    "inputTokens": input_tokens,
                                    "cachedInputTokens": cached_tokens,
                                    "outputTokens": output_tokens,
                                    "reasoningOutputTokens": 1,
                                    "totalTokens": input_tokens + output_tokens,
                                },
                            },
                        },
                    }
                )
                + "\n"
            )
        events.append(
            json.dumps(
                {
                    "method": "turn/completed",
                    "params": {
                        "threadId": "thread-1",
                        "turn": {"id": "turn-1", "status": "completed"},
                    },
                }
            )
            + "\n"
        )

        class RecordingInput(io.StringIO):
            def __init__(self, temporary_auth: Path) -> None:
                super().__init__()
                self.temporary_auth = temporary_auth
                self.messages: list[dict[str, object]] = []

            def write(self, value: str) -> int:
                message = json.loads(value)
                if message.get("method") == "turn/start":
                    if self.temporary_auth.exists():
                        raise AssertionError("turn/start was sent before auth removal")
                self.messages.append(message)
                return len(value)

        class FakeProcess:
            def __init__(self, command: list[str]) -> None:
                state_source = next(
                    Path(source)
                    for _kind, source, destination, _index in mounts(command)
                    if destination == "/u501/tester"
                )
                self.stdin = RecordingInput(state_source / ".codex" / "auth.json")
                self.stdout = io.StringIO("".join(events))
                self.returncode: int | None = None
                self.terminated = False

            def poll(self) -> int | None:
                return self.returncode

            def terminate(self) -> None:
                self.terminated = True
                self.returncode = -15

            def kill(self) -> None:
                self.returncode = -9

            def wait(self, timeout: float | None = None) -> int:
                del timeout
                if self.returncode is None:
                    self.returncode = 0
                return self.returncode

        args = self.codex_args("N")
        args.prompt_file = prompt_file
        args.context_file = context_file
        args.target_file = target_file
        args.usage_output = usage_output
        args.auth_file = auth_file
        args.state_parent = state_parent
        # The second live notification crosses this cap.  The trusted adapter
        # must persist it and stop without consuming a later usage update.
        args.token_limit = 35
        go_thread = self.enable_prompt_handshake(args, usage_output)
        created: list[FakeProcess] = []

        def fake_popen(command: list[str], **_kwargs: object) -> FakeProcess:
            self.assertIn("app-server", command)
            self.assertIn("--stdio", command)
            self.assertEqual(
                command.count("features.rollout_budget.limit_tokens=4321"), 1
            )
            self.assertNotIn("features.rollout_budget.limit_tokens=35", command)
            process = FakeProcess(command)
            created.append(process)
            return process

        audit = io.StringIO()
        with (
            mock.patch.object(codex_isolated.subprocess, "Popen", side_effect=fake_popen),
            mock.patch.object(codex_isolated.os, "replace", wraps=os.replace) as replace,
            mock.patch.dict(
                os.environ,
                {NETWORK_VIOLATION_MARKER_ENV: str(self.network_marker)},
            ),
            contextlib.redirect_stdout(audit),
        ):
            self.assertEqual(run_codex_isolated(args), 0)
        go_thread.join(timeout=2)

        self.assertEqual(len(created), 1)
        process = created[0]
        self.assertEqual(process.returncode, 0)
        self.assertFalse(process.terminated)
        self.assertEqual(replace.call_count, 2)
        self.assertFalse(usage_output.with_suffix(".json.tmp").exists())
        self.assertEqual(
            json.loads(usage_output.read_text(encoding="utf-8")),
            {
                "input_tokens": 31,
                "cached_input_tokens": 8,
                "output_tokens": 7,
                "measurement_source": TOKEN_USAGE_MEASUREMENT_SOURCE,
                "live_cumulative": True,
                "input_includes_cached": True,
                "notification_sequence": 2,
                "observed_at_unix_ns": mock.ANY,
            },
        )
        self.assertIn("mock app-server diagnostic", audit.getvalue())
        self.assertIn('"thread/tokenUsage/updated"', audit.getvalue())
        self.assertNotIn('"turn/completed"', audit.getvalue())
        self.assertEqual(
            [message.get("method") for message in process.stdin.messages],
            ["initialize", "initialized", "thread/start", "turn/start"],
        )
        self.assertEqual(
            process.stdin.messages[0]["params"]["capabilities"],
            {"experimentalApi": False},
        )
        thread_params = process.stdin.messages[2]["params"]
        self.assertEqual(
            set(thread_params),
            {"approvalPolicy", "cwd", "ephemeral", "model", "sandbox"},
        )
        self.assertEqual(thread_params["approvalPolicy"], "never")
        self.assertEqual(thread_params["sandbox"], "danger-full-access")
        self.assertIs(thread_params["ephemeral"], False)
        self.assertEqual(thread_params["cwd"], "/workspace")
        turn_params = process.stdin.messages[3]["params"]
        self.assertEqual(
            set(turn_params),
            {
                "approvalPolicy",
                "cwd",
                "effort",
                "input",
                "model",
                "sandboxPolicy",
                "threadId",
            },
        )
        self.assertEqual(turn_params["sandboxPolicy"], {"type": "dangerFullAccess"})
        self.assertEqual(turn_params["effort"], "medium")
        self.assertEqual(turn_params["model"], "test-model")
        self.assertEqual(
            turn_params["input"],
            [
                {
                    "type": "text",
                    "text": build_prompt(
                        args.prompt_file, args.context_file, args.target_file
                    ),
                }
            ],
        )
        self.assertEqual(list(state_parent.iterdir()), [])


class OfflineShellTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("cc"), "C compiler is unavailable")
    @unittest.skipUnless(platform.machine() == "x86_64", "seccomp launcher is x86-64 only")
    def test_launcher_preserves_bash_lc_argument_shape_and_blocks_sockets(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            executable = root / "offline-shell"
            compiled = subprocess.run(
                [
                    shutil.which("cc") or "cc",
                    "-std=c11",
                    "-O2",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    str(TOOLS / "offline_shell.c"),
                    "-o",
                    str(executable),
                ],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout)
            marker = root / "network-violation.marker"
            marker.write_bytes(b"")
            launcher_environment = {
                "HOME": str(root),
                "PATH": "/usr/bin:/bin",
                "SHELL": str(executable),
                NETWORK_VIOLATION_MARKER_ENV: str(marker),
            }
            socket_check = (
                "import errno,socket,sys; "
                "\ntry: socket.socket()"
                "\nexcept OSError as error: "
                "sys.exit(0 if error.errno == errno.EPERM else 2)"
                "\nsys.exit(3)"
            )
            direct = subprocess.run(
                [sys.executable, "-c", socket_check],
                cwd=root,
                env={"HOME": str(root), "PATH": "/usr/bin:/bin"},
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            shaped = subprocess.run(
                [
                    str(executable),
                    "-lc",
                    'printf "%s|%s|%s" "$0" "$1" '
                    '"${HIGHAMBENCH_NETWORK_VIOLATION_MARKER-unset}"',
                    "shape-zero",
                    "shape-one",
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(shaped.returncode, 0, shaped.stdout)
            self.assertTrue(
                shaped.stdout.endswith("shape-zero|shape-one|unset"), shaped.stdout
            )
            if direct.returncode == 3:
                self.assertEqual(marker.read_bytes(), b"", shaped.stdout)
            else:
                marker.write_bytes(b"")
            blocked = subprocess.run(
                [
                    str(executable),
                    "-c",
                    f"{shlex.quote(sys.executable)} -c {shlex.quote(socket_check)}",
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(blocked.returncode, 0, blocked.stdout)
            if direct.returncode == 3:
                self.assertEqual(marker.read_bytes(), b"N")
            else:
                # Some test sandboxes already deny socket() with a higher-
                # priority outer seccomp rule, so the inner listener cannot
                # observe that call.  The unsandboxed regression path above is
                # exercised whenever the host itself permits socket creation.
                self.assertEqual(direct.returncode, 0, direct.stdout)

            marker.write_bytes(b"")
            ordinary_signals = subprocess.run(
                [
                    str(executable),
                    "-c",
                    "sleep 5 & victim=$!; "
                    "kill -TERM \"$victim\"; wait \"$victim\" 2>/dev/null || :; "
                    "timeout 0.05 sleep 5; test $? -eq 124",
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(ordinary_signals.returncode, 0, ordinary_signals.stdout)
            self.assertEqual(marker.read_bytes(), b"", ordinary_signals.stdout)

            marker.write_bytes(b"")
            blocked_kill = subprocess.run(
                [
                    str(executable),
                    "-c",
                    'kill -KILL "$PPID" 2>/dev/null; test "$?" -ne 0',
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(blocked_kill.returncode, 0, blocked_kill.stdout)
            self.assertGreaterEqual(len(marker.read_bytes()), 1)
            self.assertEqual(set(marker.read_bytes()), {ord("N")})

            marker.write_bytes(b"")
            inherited_source = root / "inherited.txt"
            inherited_source.write_text("secret", encoding="utf-8")
            source_fd = os.open(inherited_source, os.O_RDONLY)
            inherited_fd = 77
            os.dup2(source_fd, inherited_fd, inheritable=True)
            os.close(source_fd)
            try:
                closed_fd = subprocess.run(
                    [
                        str(executable),
                        "-c",
                        f"test ! -e /proc/self/fd/{inherited_fd} && "
                        f"test ! -e /proc/$PPID/fd/{inherited_fd}",
                    ],
                    cwd=root,
                    env=launcher_environment,
                    pass_fds=(inherited_fd,),
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    check=False,
                )
            finally:
                os.close(inherited_fd)
            self.assertEqual(closed_fd.returncode, 0, closed_fd.stdout)


if __name__ == "__main__":
    unittest.main()
