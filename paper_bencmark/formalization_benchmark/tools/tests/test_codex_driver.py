from __future__ import annotations

import json
import hashlib
import os
from pathlib import Path
import shutil
import sys
import tempfile
import threading
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from codex_driver import (  # noqa: E402
    CodexDriver,
    ProviderCapabilityError,
    _normalize_raw_usage,
    _normalize_usage_breakdown,
)
from common import BenchmarkError  # noqa: E402


FAKE_APP_SERVER = r'''
import hashlib
import json
import os
from pathlib import Path
import sys

state = Path(os.environ["CODEX_HOME"])
workspace = Path.cwd()
(state / "config.toml").write_text("fixture = true\n", encoding="utf-8")
(state / "skills" / ".system" / "fixture").mkdir(parents=True, exist_ok=True)
(state / "skills" / ".system" / "fixture" / "SKILL.md").write_text(
    "trusted system skill\n", encoding="utf-8"
)
(state / "tmp" / "arg0").mkdir(parents=True, exist_ok=True)
temporary_link = state / "tmp" / "arg0" / "apply_patch"
if not temporary_link.exists() and not temporary_link.is_symlink():
    temporary_link.symlink_to(workspace / "does-not-exist")

def receive():
    line = sys.stdin.readline()
    if not line:
        return None
    return json.loads(line)

def send(value):
    print(json.dumps(value, separators=(",", ":")), flush=True)

initialize = receive()
assert initialize is not None
assert initialize["method"] == "initialize"
send({"id": initialize["id"], "result": {"serverInfo": {"name": "fake"}}})
initialized = receive()
assert initialized is not None and initialized["method"] == "initialized"
assert "agents.enabled=false" in sys.argv
assert "multi_agent" in sys.argv and "multi_agent_v2" in sys.argv
config_read_count = 0
global_feature_count = 0
thread_feature_count = 0

def capability_response(request):
    global config_read_count, global_feature_count, thread_feature_count
    method = request["method"]
    if method == "config/read":
        config_read_count += 1
        assert request["params"]["includeLayers"] is True
        enabled = (workspace / "capability-config-drift").exists()
        origin_type = (
            "user" if (workspace / "capability-origin-drift").exists()
            else "sessionFlags"
        )
        flags = {
            "agents": {"enabled": enabled},
            "features": {"multi_agent": False, "multi_agent_v2": False},
        }
        send({"id": request["id"], "result": {
            "config": flags,
            "origins": {
                key: {"name": {"type": origin_type}, "version": "1"}
                for key in (
                    "agents.enabled", "features.multi_agent", "features.multi_agent_v2"
                )
            },
            "layers": [{
                "name": {"type": "sessionFlags"}, "version": "1", "config": flags,
            }],
        }})
        return True
    if method == "experimentalFeature/list":
        scoped = request["params"].get("threadId")
        if scoped is None:
            global_feature_count += 1
        else:
            assert scoped in ("thread-test", "thread-fork-test")
            thread_feature_count += 1
        enabled = (
            (workspace / "capability-feature-enabled").exists()
            or (scoped is not None and (workspace / "capability-thread-feature-enabled").exists())
        )
        entries = [
            {"name": name, "stage": "stable", "enabled": enabled and name == "multi_agent",
             "defaultEnabled": name == "multi_agent"}
            for name in ("multi_agent", "multi_agent_v2")
        ]
        if (workspace / "capability-feature-missing").exists():
            entries.pop()
        if (workspace / "capability-feature-duplicate").exists():
            entries.append(dict(entries[0]))
        send({"id": request["id"], "result": {"data": entries, "nextCursor": None}})
        return True
    return False

thread_request = receive()
while thread_request is not None and capability_response(thread_request):
    thread_request = receive()
assert thread_request is not None
assert thread_request["method"] in ("thread/start", "thread/fork")
if thread_request["method"] == "thread/start":
    assert thread_request["params"]["config"] == {
        "agents": {"enabled": False},
        "features": {"multi_agent": False, "multi_agent_v2": False},
    }
else:
    assert thread_request["params"]["threadId"] == "thread-test"
    assert thread_request["params"]["lastTurnId"] == "turn-1"
assert (state / "auth.json").is_file()
thread_id = (
    "thread-fork-test" if thread_request["method"] == "thread/fork" else "thread-test"
)
ephemeral = bool(thread_request["params"].get("ephemeral", False))
thread = {
    "id": thread_id,
    "ephemeral": ephemeral,
    "model": "test-model",
}
raw_events_enabled = not (
    thread_request["method"] == "thread/fork"
    and (workspace / "fork-no-raw-events").exists()
)
send({"method": "thread/started", "params": {"thread": thread}})
send({"id": thread_request["id"], "result": {"thread": thread}})
turn_number = 0
cumulative = {
    "inputTokens": 0,
    "cachedInputTokens": 0,
    "cacheWriteInputTokens": 0,
    "outputTokens": 0,
    "reasoningOutputTokens": 0,
    "totalTokens": 0,
}
if thread_request["method"] == "thread/fork":
    cumulative = {
        "inputTokens": 10,
        "cachedInputTokens": 2,
        "cacheWriteInputTokens": 1,
        "outputTokens": 5,
        "reasoningOutputTokens": 2,
        "totalTokens": 15,
    }
    fork_baseline = dict(cumulative)
    if (workspace / "fork-baseline-mismatch").exists():
        fork_baseline["totalTokens"] += 1
    send({
        "method": "thread/tokenUsage/updated",
        "params": {
            "threadId": thread_id,
            "turnId": (
                "wrong-source-turn"
                if (workspace / "fork-baseline-turn-mismatch").exists()
                else "turn-1"
            ),
            "tokenUsage": {"total": fork_baseline, "last": dict(cumulative)},
        },
    })
late_pending = False
late_turn_id = None
exit_code_on_eof = 0
late_on_eof = False
while True:
    turn_request = receive()
    if turn_request is None:
        if late_on_eof:
            send({"method": "rawResponse/completed", "params": {"late": True}})
        print("stderr emitted at app-server shutdown", file=sys.stderr, flush=True)
        raise SystemExit(exit_code_on_eof)
    if capability_response(turn_request):
        continue
    if turn_request["method"] == "thread/backgroundTerminals/clean":
        send({"id": turn_request["id"], "result": {}})
        list_request = receive()
        assert list_request is not None
        assert list_request["method"] == "thread/backgroundTerminals/list"
        send({"id": list_request["id"], "result": {"data": [], "nextCursor": None}})
        continue
    if turn_request["method"] == "thread/read":
        if late_pending:
            late_raw = {
                "inputTokens": 4,
                "cachedInputTokens": 1,
                "cacheWriteInputTokens": 0,
                "outputTokens": 2,
                "reasoningOutputTokens": 1,
                "totalTokens": 6,
            }
            if raw_events_enabled:
                send({
                    "method": "rawResponse/completed",
                    "params": {
                        "responseId": "response-late-" + str(late_turn_id),
                        "threadId": thread_id,
                        "turnId": late_turn_id,
                        "usage": late_raw,
                    },
                })
            for field in cumulative:
                cumulative[field] += late_raw[field]
            send({
                "method": "thread/tokenUsage/updated",
                "params": {
                    "threadId": thread_id,
                    "turnId": late_turn_id,
                    "tokenUsage": {"total": dict(cumulative), "last": late_raw},
                },
            })
            late_pending = False
        send({"id": turn_request["id"], "result": {"thread": thread}})
        continue
    assert turn_request["method"] == "turn/start"
    turn_number += 1
    prompt_text = turn_request["params"]["input"][0]["text"]
    if prompt_text == "bad-shutdown":
        exit_code_on_eof = 7
    if prompt_text == "late-on-close":
        late_on_eof = True
    auth_present = (state / "auth.json").is_file()
    auth_sha256 = hashlib.sha256((state / "auth.json").read_bytes()).hexdigest()
    with (workspace / "observations.jsonl").open("a", encoding="utf-8") as stream:
        stream.write(json.dumps({
            "thread_method": thread_request["method"],
            "turn_number": turn_number,
            "server_pid": os.getpid(),
            "auth_present_at_turn_start": auth_present,
            "auth_sha256_at_turn_start": auth_sha256,
            "output_schema": turn_request["params"].get("outputSchema"),
            "thread_sandbox": thread_request["params"].get("sandbox"),
            "experimental_raw_events": thread_request["params"].get("experimentalRawEvents"),
            "history_mode": thread_request["params"].get("historyMode"),
            "turn_sandbox_policy": turn_request["params"].get("sandboxPolicy"),
            "thread_start_config": thread_request["params"].get("config"),
            "config_read_count": config_read_count,
            "global_feature_count": global_feature_count,
            "thread_feature_count": thread_feature_count,
        }) + "\n")
    if not auth_present:
        raise SystemExit(9)
    if prompt_text == "rotate-auth":
        (state / "auth.json").write_text(
            '{"token":"rotated-credential-value"}\n', encoding="utf-8"
        )
    turn_id = "turn-" + str(turn_number)
    send({
        "method": "turn/started",
        "params": {"threadId": thread_id, "turn": {"id": turn_id}},
    })
    send({"id": turn_request["id"], "result": {"turn": {"id": turn_id}}})
    if prompt_text == "collab-started":
        send({"method": "item/started", "params": {
            "threadId": thread_id, "turnId": turn_id,
            "item": {"id": "subagent", "type": "collabAgentToolCall", "tool": "spawnAgent"},
        }})
    if prompt_text == "collab-raw":
        send({"method": "rawResponseItem/completed", "params": {
            "threadId": thread_id, "turnId": turn_id,
            "item": {"type": "function_call", "namespace": "functions.collaboration",
                     "name": "spawn_agent"},
        }})
    if prompt_text == "foreign-thread":
        send({"method": "item/started", "params": {
            "threadId": "another-thread", "turnId": turn_id,
            "item": {"type": "agentMessage", "text": "foreign"},
        }})
    if prompt_text == "foreign-thread-started":
        send({"method": "thread/started", "params": {
            "thread": {"id": "child-thread", "ephemeral": False},
        }})
    send({
        "method": "item/completed",
        "params": {
            "completedAtMs": 1,
            "threadId": thread_id,
            "turnId": turn_id,
            "item": {"id": "message-" + turn_id, "type": "agentMessage", "text": turn_id},
        },
    })
    if raw_events_enabled:
        send({
            "method": "rawResponseItem/completed",
            "params": {
                "threadId": thread_id,
                "turnId": turn_id,
                "item": {
                    "id": "reasoning-" + turn_id,
                    "type": "reasoning",
                    "summary": [{"type": "summary_text", "text": "visible summary"}],
                    "content": [{"type": "reasoning_text", "text": "hidden reasoning"}],
                    "encrypted_content": "encrypted-hidden-payload",
                },
            },
        })
    if prompt_text == "missing-usage":
        send({
            "method": "turn/completed",
            "params": {
                "threadId": thread_id,
                "turn": {"id": turn_id, "status": "completed"},
            },
        })
        continue
    raw = (
        {
            "inputTokens": 15,
            "cachedInputTokens": 3,
            "cacheWriteInputTokens": 1,
            "outputTokens": 3,
            "reasoningOutputTokens": 1,
            "totalTokens": 18,
        }
        if turn_number == 2
        else {
            "inputTokens": 10,
            "cachedInputTokens": 2,
            "cacheWriteInputTokens": 1,
            "outputTokens": 5,
            "reasoningOutputTokens": 2,
            "totalTokens": 15,
        }
    )
    if prompt_text == "multi-usage":
        earlier = {
            "inputTokens": 4,
            "cachedInputTokens": 1,
            "cacheWriteInputTokens": 0,
            "outputTokens": 2,
            "reasoningOutputTokens": 1,
            "totalTokens": 6,
        }
        if raw_events_enabled:
            send({
                "method": "rawResponse/completed",
                "params": {
                    "responseId": "response-earlier-" + turn_id,
                    "threadId": thread_id,
                    "turnId": turn_id,
                    "usage": earlier,
                },
            })
        for field in cumulative:
            cumulative[field] += earlier[field]
        send({
            "method": "thread/tokenUsage/updated",
            "params": {
                "threadId": thread_id,
                "turnId": turn_id,
                "tokenUsage": {"total": dict(cumulative), "last": earlier},
            },
        })
    if prompt_text == "context-compaction":
        compaction_id = "compaction-" + turn_id
        compaction_raw = {
            "inputTokens": 100,
            "cachedInputTokens": 80,
            "cacheWriteInputTokens": 0,
            "outputTokens": 20,
            "reasoningOutputTokens": 0,
            "totalTokens": 120,
        }
        send({
            "method": "item/started",
            "params": {
                "threadId": thread_id,
                "turnId": turn_id,
                "item": {"id": compaction_id, "type": "contextCompaction"},
            },
        })
        if raw_events_enabled:
            send({
                "method": "rawResponse/completed",
                "params": {
                    "responseId": "response-compaction-" + turn_id,
                    "threadId": thread_id,
                    "turnId": turn_id,
                    "usage": compaction_raw,
                },
            })
        send({
            "method": "item/completed",
            "params": {
                "threadId": thread_id,
                "turnId": turn_id,
                "item": {"id": compaction_id, "type": "contextCompaction"},
            },
        })
    if raw_events_enabled:
        send({
            "method": "rawResponse/completed",
            "params": {
                "responseId": "response-" + turn_id,
                "threadId": thread_id,
                "turnId": turn_id,
                "usage": raw,
            },
        })
    for field in cumulative:
        cumulative[field] += raw[field]
    reported = dict(cumulative)
    reported_last = dict(raw)
    if prompt_text == "bad-usage":
        reported["totalTokens"] += 1
    if (workspace / "fork-last-usage-mismatch").exists():
        reported_last["inputTokens"] += 1
        reported_last["totalTokens"] += 1
    send({
        "method": "thread/tokenUsage/updated",
        "params": {
            "threadId": thread_id,
            "turnId": turn_id,
            "tokenUsage": {"total": reported, "last": reported_last},
        },
    })
    if (workspace / "fork-duplicate-usage").exists():
        send({
            "method": "thread/tokenUsage/updated",
            "params": {
                "threadId": thread_id,
                "turnId": turn_id,
                "tokenUsage": {"total": reported, "last": reported_last},
            },
        })
    if prompt_text == "late-usage":
        late_pending = True
        late_turn_id = turn_id
    send({
        "method": "turn/completed",
        "params": {"threadId": thread_id, "turn": {"id": turn_id, "status": "completed"}},
    })
    cleanup_request = receive()
    assert cleanup_request is not None
    assert cleanup_request["method"] == "thread/backgroundTerminals/clean"
    assert cleanup_request["params"]["threadId"] == thread_id
    send({"id": cleanup_request["id"], "result": {}})
    list_request = receive()
    assert list_request is not None
    assert list_request["method"] == "thread/backgroundTerminals/list"
    assert list_request["params"]["threadId"] == thread_id
    send({"id": list_request["id"], "result": {"data": [], "nextCursor": None}})
'''


class CodexDriverProtocolTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.auth = self.root / "source-auth.json"
        self.auth.write_text('{"token":"fixture"}\n', encoding="utf-8")
        self.codex = self.root / "fake-codex"
        self.codex.write_text(f"#!{sys.executable}\n" + FAKE_APP_SERVER, encoding="utf-8")
        self.codex.chmod(0o700)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def driver(self, **overrides: object) -> CodexDriver:
        options: dict[str, object] = {
            "codex_binary": self.codex,
            "model": "test-model",
            "reasoning_effort": "high",
            "state_root": self.root / "state",
            "auth_file": self.auth,
            "disable_features": ["multi_agent"],
        }
        options.update(overrides)
        return CodexDriver(**options)  # type: ignore[arg-type]

    def test_empty_top_level_codex_mount_point_is_inert(self) -> None:
        (self.workspace / ".codex").mkdir()
        CodexDriver._assert_safe_workspace(self.workspace)

    def test_populated_codex_control_directory_is_rejected(self) -> None:
        control = self.workspace / ".codex"
        control.mkdir()
        (control / "config.toml").write_text("model = 'test'\n", encoding="utf-8")
        with self.assertRaisesRegex(Exception, "forbidden workspace control surface"):
            CodexDriver._assert_safe_workspace(self.workspace)

    def test_nested_empty_codex_directory_is_rejected(self) -> None:
        nested = self.workspace / "nested" / ".codex"
        nested.mkdir(parents=True)
        with self.assertRaisesRegex(Exception, "forbidden workspace control surface"):
            CodexDriver._assert_safe_workspace(self.workspace)

    def test_app_server_retains_private_auth_and_resumes_same_thread(self) -> None:
        schema = self.root / "schema.json"
        schema.write_text('{"type":"object"}\n', encoding="utf-8")
        driver = self.driver()
        first = driver.run_turn(
            prompt="first",
            workspace=self.workspace,
            artifact_dir=self.root / "artifacts-1",
            timeout_seconds=5,
            output_schema=schema,
        )
        self.assertEqual(first.exit_code, 0)
        self.assertEqual(first.thread_id, "thread-test")
        self.assertEqual(first.final_message, "turn-1")
        self.assertEqual(first.usage["total_tokens"], 15)
        self.assertEqual(first.usage["reasoning_output_tokens"], 2)
        self.assertTrue(first.usage_complete)
        self.assertTrue((self.root / "state" / "auth.json").is_file())
        self.assertEqual(first.command[1:3], ["app-server", "--stdio"])
        self.assertIn("agents.enabled=false", first.command)
        self.assertIn("multi_agent", first.command)
        self.assertIn("multi_agent_v2", first.command)

        second = driver.run_turn(
            prompt="repair",
            workspace=self.workspace,
            artifact_dir=self.root / "artifacts-2",
            timeout_seconds=5,
            thread_id=first.thread_id,
        )
        self.assertEqual(second.exit_code, 0)
        self.assertEqual(second.thread_id, first.thread_id)
        self.assertEqual(second.final_message, "turn-2")
        self.assertTrue(second.usage_complete)
        self.assertEqual(
            second.usage,
            {
                "input_tokens": 15,
                "cached_input_tokens": 3,
                "cache_write_input_tokens": 1,
                "output_tokens": 3,
                "reasoning_output_tokens": 1,
                "total_tokens": 18,
            },
        )
        self.assertTrue((self.root / "state" / "auth.json").is_file())

        observations = [
            json.loads(line)
            for line in (self.workspace / "observations.jsonl").read_text(encoding="utf-8").splitlines()
        ]
        self.assertEqual([item["thread_method"] for item in observations], ["thread/start", "thread/start"])
        self.assertEqual([item["turn_number"] for item in observations], [1, 2])
        self.assertEqual([item["config_read_count"] for item in observations], [1, 2])
        self.assertEqual([item["global_feature_count"] for item in observations], [1, 2])
        self.assertEqual([item["thread_feature_count"] for item in observations], [1, 2])
        self.assertEqual(len({item["server_pid"] for item in observations}), 1)
        self.assertTrue(all(item["auth_present_at_turn_start"] for item in observations))
        self.assertTrue(all(item["experimental_raw_events"] for item in observations))
        self.assertTrue(all(item["history_mode"] == "legacy" for item in observations))
        self.assertTrue(all(item["thread_sandbox"] == "workspace-write" for item in observations))
        self.assertTrue(
            all(item["turn_sandbox_policy"]["type"] == "workspaceWrite" for item in observations)
        )
        self.assertEqual(observations[0]["output_schema"], {"type": "object"})
        turn_record = json.loads(
            (self.root / "artifacts-1" / "turn.json").read_text(encoding="utf-8")
        )
        self.assertFalse(turn_record["temporary_auth_removed_before_turn_start"])
        self.assertTrue(turn_record["private_auth_retained_for_refresh"])
        self.assertEqual(turn_record["transport"], "codex-app-server-stdio")
        self.assertEqual(turn_record["raw_response_count"], 1)
        self.assertTrue(turn_record["capability_attestation"]["passed"])
        self.assertEqual(
            turn_record["capability_attestation"]["thread_start_config"],
            observations[0]["thread_start_config"],
        )
        self.assertGreaterEqual(turn_record["event_trace_redactions"], 2)
        events_text = (self.root / "artifacts-1" / "events.jsonl").read_text(
            encoding="utf-8"
        )
        self.assertIn("visible summary", events_text)
        self.assertNotIn("hidden reasoning", events_text)
        self.assertNotIn("encrypted-hidden-payload", events_text)
        self.assertEqual(
            (self.root / "artifacts-1" / "last_message.txt").read_text(encoding="utf-8"),
            "turn-1",
        )
        self.assertIsNotNone(first.active_ended_perf_ns)
        second_record = json.loads(
            (self.root / "artifacts-2" / "turn.json").read_text(encoding="utf-8")
        )
        self.assertTrue(second_record["app_server_process_reused"])
        self.assertTrue(second_record["capability_attestation"]["passed"])
        self.assertTrue(second_record["capability_attestation"]["reused_thread"])
        self.assertTrue(second_record["background_terminal_cleanup"]["verified_empty"])
        self.assertTrue(
            second_record["post_terminal_telemetry_settle"][
                "thread_read_ordering_barrier"
            ]
        )
        self.assertFalse(
            second_record["background_terminal_cleanup"][
                "excluded_from_contestant_measurement"
            ]
        )
        self.assertTrue(
            second_record["post_terminal_telemetry_settle"][
                "excluded_from_contestant_measurement"
            ]
        )
        close_artifacts = self.root / "formalizer-session-close"
        driver.close(artifact_dir=close_artifacts)
        self.assertFalse((self.root / "state" / "auth.json").exists())
        shutdown = json.loads(
            (close_artifacts / "shutdown.json").read_text(encoding="utf-8")
        )
        self.assertTrue(shutdown["graceful"])
        self.assertEqual(shutdown["returncode"], 0)
        self.assertTrue(shutdown["stdout_drained_to_eof"])
        self.assertEqual(shutdown["late_stdout_line_count"], 0)
        self.assertIn(
            "stderr emitted at app-server shutdown",
            (close_artifacts / "stderr-after-last-turn.log").read_text(
                encoding="utf-8"
            ),
        )

    def test_fork_starts_from_frozen_parent_and_meters_only_child_turn(self) -> None:
        checkpoint = self.root / "checkpoint"
        checkpoint.mkdir()
        scout = self.driver(state_root=checkpoint / "state")
        source = scout.run_turn(
            prompt="scout",
            workspace=self.workspace,
            artifact_dir=self.root / "scout-artifacts",
            timeout_seconds=5,
        )
        scout.close(artifact_dir=self.root / "scout-close")
        self.assertEqual(source.thread_id, "thread-test")
        source_turn = json.loads(
            (self.root / "scout-artifacts" / "turn.json").read_text(
                encoding="utf-8"
            )
        )["turn_id"]

        seed = self.root / "seed"
        shutil.copytree(checkpoint, seed, symlinks=True)
        task_workspace = self.root / "task-workspace"
        task_workspace.mkdir()
        forked = self.driver(
            state_root=seed / "state",
            fork_source_thread_id=source.thread_id,
            fork_source_last_turn_id=source_turn,
            fork_source_cumulative_usage=source.usage,
        )
        child = forked.run_turn(
            prompt="task",
            workspace=task_workspace,
            artifact_dir=self.root / "task-artifacts",
            timeout_seconds=5,
        )
        self.assertEqual(child.thread_id, "thread-fork-test")
        self.assertEqual(child.usage["total_tokens"], 15)
        self.assertTrue(child.usage_complete)
        child_record = json.loads(
            (self.root / "task-artifacts" / "turn.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(
            child_record["capability_attestation"]["thread_creation"]["method"],
            "thread/fork",
        )
        self.assertEqual(
            child_record["fork_provenance"]["source_thread_id"], "thread-test"
        )
        self.assertEqual(
            child_record["fork_cumulative_usage_semantics"], "parent_inherited"
        )
        baseline = child_record["capability_attestation"][
            "fork_baseline_usage_notification"
        ]
        self.assertTrue(baseline["accepted"])
        self.assertTrue(baseline["excluded_from_contestant_usage"])
        self.assertTrue(baseline["excluded_from_contestant_time"])
        self.assertEqual(baseline["source_turn_id"], "turn-1")
        self.assertEqual(baseline["source_cumulative_usage"], source.usage)
        forked.close(artifact_dir=self.root / "task-close")

    def test_fork_without_raw_events_uses_exact_cumulative_response_usage(self) -> None:
        checkpoint = self.root / "notification-checkpoint"
        checkpoint.mkdir()
        scout = self.driver(state_root=checkpoint / "state")
        source = scout.run_turn(
            prompt="scout",
            workspace=self.workspace,
            artifact_dir=self.root / "notification-scout",
            timeout_seconds=5,
        )
        scout.close(artifact_dir=self.root / "notification-scout-close")
        source_turn = json.loads(
            (self.root / "notification-scout" / "turn.json").read_text()
        )["turn_id"]
        seed = self.root / "notification-seed"
        shutil.copytree(checkpoint, seed, symlinks=True)
        task_workspace = self.root / "notification-workspace"
        task_workspace.mkdir()
        (task_workspace / "fork-no-raw-events").touch()
        forked = self.driver(
            state_root=seed / "state",
            fork_source_thread_id=source.thread_id,
            fork_source_last_turn_id=source_turn,
            fork_source_cumulative_usage=source.usage,
        )

        child = forked.run_turn(
            prompt="multi-usage",
            workspace=task_workspace,
            artifact_dir=self.root / "notification-task",
            timeout_seconds=5,
        )
        self.assertTrue(child.usage_complete)
        self.assertEqual(child.usage["total_tokens"], 21)
        child_record = json.loads(
            (self.root / "notification-task" / "turn.json").read_text()
        )
        self.assertEqual(child_record["raw_response_count"], 0)
        self.assertEqual(child_record["cumulative_usage_notification_count"], 2)
        self.assertTrue(child_record["fork_notification_fallback_admitted"])
        self.assertEqual(
            child_record["usage_measurement_mode"],
            "fork_cumulative_notifications",
        )
        self.assertEqual(
            sum(
                item["last_usage"]["total_tokens"]
                for item in child_record["cumulative_usage_notifications"]
            ),
            child.usage["total_tokens"],
        )
        self.assertTrue(
            all(
                not item["received_after_turn_completed"]
                for item in child_record["cumulative_usage_notifications"]
            )
        )

        repair = forked.run_turn(
            prompt="repair",
            workspace=task_workspace,
            artifact_dir=self.root / "notification-repair",
            timeout_seconds=5,
            thread_id=child.thread_id,
        )
        self.assertTrue(repair.usage_complete)
        self.assertEqual(repair.usage["total_tokens"], 18)
        repair_record = json.loads(
            (self.root / "notification-repair" / "turn.json").read_text()
        )
        self.assertEqual(
            repair_record["usage_measurement_mode"],
            "fork_cumulative_notifications",
        )
        forked.close(artifact_dir=self.root / "notification-close")

    def test_fork_notification_usage_fails_closed_on_unmetered_compaction(self) -> None:
        checkpoint = self.root / "compaction-notification-checkpoint"
        checkpoint.mkdir()
        scout = self.driver(state_root=checkpoint / "state")
        source = scout.run_turn(
            prompt="scout",
            workspace=self.workspace,
            artifact_dir=self.root / "compaction-notification-scout",
            timeout_seconds=5,
        )
        scout.close()
        source_turn = json.loads(
            (self.root / "compaction-notification-scout" / "turn.json").read_text()
        )["turn_id"]
        seed = self.root / "compaction-notification-seed"
        shutil.copytree(checkpoint, seed, symlinks=True)
        workspace = self.root / "compaction-notification-workspace"
        workspace.mkdir()
        (workspace / "fork-no-raw-events").touch()
        forked = self.driver(
            state_root=seed / "state",
            fork_source_thread_id=source.thread_id,
            fork_source_last_turn_id=source_turn,
            fork_source_cumulative_usage=source.usage,
        )
        result = forked.run_turn(
            prompt="context-compaction",
            workspace=workspace,
            artifact_dir=self.root / "compaction-notification-task",
            timeout_seconds=5,
        )
        self.assertEqual(result.failure_kind, "telemetry_invalid")
        self.assertFalse(result.usage_complete)
        record = json.loads(
            (self.root / "compaction-notification-task" / "turn.json").read_text()
        )
        self.assertIn("context compaction", record["protocol_error"])
        self.assertEqual(record["context_compaction_item_count"], 1)
        forked.close()

    def test_fork_notification_usage_rejects_last_delta_mismatch(self) -> None:
        checkpoint = self.root / "invalid-notification-checkpoint"
        checkpoint.mkdir()
        scout = self.driver(state_root=checkpoint / "state")
        source = scout.run_turn(
            prompt="scout",
            workspace=self.workspace,
            artifact_dir=self.root / "invalid-notification-scout",
            timeout_seconds=5,
        )
        scout.close()
        source_turn = json.loads(
            (self.root / "invalid-notification-scout" / "turn.json").read_text()
        )["turn_id"]
        marker = "fork-last-usage-mismatch"
        seed = self.root / f"{marker}-seed"
        shutil.copytree(checkpoint, seed, symlinks=True)
        workspace = self.root / f"{marker}-workspace"
        workspace.mkdir()
        (workspace / "fork-no-raw-events").touch()
        (workspace / marker).touch()
        forked = self.driver(
            state_root=seed / "state",
            fork_source_thread_id=source.thread_id,
            fork_source_last_turn_id=source_turn,
            fork_source_cumulative_usage=source.usage,
        )
        result = forked.run_turn(
            prompt="task",
            workspace=workspace,
            artifact_dir=self.root / f"{marker}-artifacts",
            timeout_seconds=5,
        )
        self.assertEqual(result.failure_kind, "telemetry_invalid")
        self.assertFalse(result.usage_complete)
        record = json.loads(
            (self.root / f"{marker}-artifacts" / "turn.json").read_text()
        )
        self.assertIn(
            "last-response usage disagrees",
            record["protocol_error"],
        )
        forked.close()

    def test_exact_duplicate_usage_notification_is_idempotent(self) -> None:
        workspace = self.root / "duplicate-usage-workspace"
        workspace.mkdir()
        (workspace / "fork-duplicate-usage").touch()
        driver = self.driver(state_root=self.root / "duplicate-usage-state")
        result = driver.run_turn(
            prompt="task",
            workspace=workspace,
            artifact_dir=self.root / "duplicate-usage-artifacts",
            timeout_seconds=5,
        )
        self.assertEqual(result.exit_code, 0)
        self.assertTrue(result.usage_complete)
        self.assertEqual(result.usage["total_tokens"], 15)
        record = json.loads(
            (self.root / "duplicate-usage-artifacts" / "turn.json").read_text()
        )
        self.assertEqual(record["cumulative_usage_notification_count"], 1)
        self.assertEqual(record["duplicate_cumulative_usage_notification_count"], 1)
        duplicate = record["duplicate_cumulative_usage_notifications"][0]
        self.assertEqual(duplicate["duplicate_of_sequence"], 1)
        self.assertFalse(duplicate["received_after_turn_completed"])
        driver.close()

    def test_provider_free_fork_preflight_accepts_only_frozen_parent_baseline(self) -> None:
        checkpoint = self.root / "fork-preflight-checkpoint"
        checkpoint.mkdir()
        scout = self.driver(state_root=checkpoint / "state")
        source = scout.run_turn(
            prompt="scout",
            workspace=self.workspace,
            artifact_dir=self.root / "fork-preflight-scout",
            timeout_seconds=5,
        )
        scout.close(artifact_dir=self.root / "fork-preflight-scout-close")
        source_turn = json.loads(
            (self.root / "fork-preflight-scout" / "turn.json").read_text()
        )["turn_id"]
        seed = self.root / "fork-preflight-seed"
        shutil.copytree(checkpoint, seed, symlinks=True)
        preflight_workspace = self.root / "fork-preflight-workspace"
        preflight_workspace.mkdir()
        forked = self.driver(
            state_root=seed / "state",
            fork_source_thread_id=source.thread_id,
            fork_source_last_turn_id=source_turn,
            fork_source_cumulative_usage=source.usage,
        )
        record = forked.preflight(
            workspace=preflight_workspace,
            artifact_dir=self.root / "fork-preflight-artifacts",
            timeout_seconds=5,
        )
        self.assertFalse(record["turn_start_sent"])
        self.assertEqual(
            record["capability_attestation"]["thread_creation"]["method"],
            "thread/fork",
        )
        baseline = record["capability_attestation"][
            "fork_baseline_usage_notification"
        ]
        self.assertTrue(baseline["accepted"])
        self.assertEqual(baseline["source_cumulative_usage"], source.usage)
        self.assertFalse((preflight_workspace / "observations.jsonl").exists())
        forked.close()

    def test_fork_rejects_mismatched_inherited_usage_before_task_turn(self) -> None:
        checkpoint = self.root / "fork-rejection-checkpoint"
        checkpoint.mkdir()
        scout = self.driver(state_root=checkpoint / "state")
        source = scout.run_turn(
            prompt="scout",
            workspace=self.workspace,
            artifact_dir=self.root / "fork-rejection-scout",
            timeout_seconds=5,
        )
        scout.close(artifact_dir=self.root / "fork-rejection-scout-close")
        source_turn = json.loads(
            (self.root / "fork-rejection-scout" / "turn.json").read_text()
        )["turn_id"]
        for index, marker in enumerate(
            ("fork-baseline-mismatch", "fork-baseline-turn-mismatch")
        ):
            with self.subTest(marker=marker):
                seed = self.root / f"fork-rejection-seed-{index}"
                shutil.copytree(checkpoint, seed, symlinks=True)
                workspace = self.root / f"fork-rejection-workspace-{index}"
                workspace.mkdir()
                (workspace / marker).touch()
                forked = self.driver(
                    state_root=seed / "state",
                    fork_source_thread_id=source.thread_id,
                    fork_source_last_turn_id=source_turn,
                    fork_source_cumulative_usage=source.usage,
                )
                result = forked.run_turn(
                    prompt="task",
                    workspace=workspace,
                    artifact_dir=self.root / f"fork-rejection-artifacts-{index}",
                    timeout_seconds=5,
                )
                self.assertEqual(result.failure_kind, "provider_capability_violation")
                self.assertIsNone(result.active_started_perf_ns)
                self.assertEqual(result.usage["total_tokens"], 0)
                self.assertFalse((workspace / "observations.jsonl").exists())
                forked.close()

    def test_context_compaction_usage_is_exact_but_not_in_cumulative_cross_check(self) -> None:
        driver = self.driver()
        result = driver.run_turn(
            prompt="context-compaction",
            workspace=self.workspace,
            artifact_dir=self.root / "compaction-artifacts",
            timeout_seconds=5,
        )
        self.assertTrue(result.usage_complete)
        self.assertEqual(result.usage["total_tokens"], 135)
        self.assertEqual(result.thread_cumulative_usage["total_tokens"], 15)
        record = json.loads(
            (self.root / "compaction-artifacts" / "turn.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(record["context_compaction_response_count"], 1)
        self.assertEqual(record["context_compaction_usage"]["total_tokens"], 120)
        self.assertEqual(
            record["cumulative_usage_expected_from_raw_responses"],
            record["cumulative_usage_delta_cross_check"],
        )
        driver.close(artifact_dir=self.root / "compaction-close")

    def test_late_raw_usage_is_drained_before_next_repair(self) -> None:
        driver = self.driver()
        first = driver.run_turn(
            prompt="late-usage",
            workspace=self.workspace,
            artifact_dir=self.root / "late-artifacts-1",
            timeout_seconds=5,
        )
        self.assertEqual(
            first.usage,
            {
                "input_tokens": 14,
                "cached_input_tokens": 3,
                "cache_write_input_tokens": 1,
                "output_tokens": 7,
                "reasoning_output_tokens": 3,
                "total_tokens": 21,
            },
        )
        self.assertTrue(first.usage_complete)
        second = driver.run_turn(
            prompt="repair",
            workspace=self.workspace,
            artifact_dir=self.root / "late-artifacts-2",
            timeout_seconds=5,
            thread_id=first.thread_id,
        )
        self.assertEqual(second.usage["total_tokens"], 18)
        self.assertTrue(second.usage_complete)
        driver.close()

    def test_driver_owned_control_state_stays_outside_artifacts_and_is_removed(self) -> None:
        driver = self.driver(state_root=None)
        owned = driver._owned_control_root
        self.assertIsNotNone(owned)
        assert owned is not None
        self.assertTrue(owned.is_dir())
        result = driver.run_turn(
            prompt="first",
            workspace=self.workspace,
            artifact_dir=self.root / "artifacts-private-control",
            timeout_seconds=5,
        )
        self.assertEqual(result.exit_code, 0)
        self.assertTrue((driver.state_root / "auth.json").is_file())
        driver.close()
        self.assertFalse(owned.exists())

    def test_refresh_rotation_is_shared_and_reloaded_before_repair(self) -> None:
        driver = self.driver()
        first = driver.run_turn(
            prompt="rotate-auth",
            workspace=self.workspace,
            artifact_dir=self.root / "rotate-first",
            timeout_seconds=5,
        )
        self.assertEqual(first.exit_code, 0)
        rotated = b'{"token":"rotated-credential-value"}\n'
        self.assertEqual(self.auth.read_bytes(), rotated)

        auditor_rotation = b'{"token":"auditor-rotated-credential"}\n'
        self.auth.write_bytes(auditor_rotation)
        second = driver.run_turn(
            prompt="repair",
            workspace=self.workspace,
            artifact_dir=self.root / "rotate-second",
            timeout_seconds=5,
            thread_id=first.thread_id,
        )
        self.assertEqual(second.exit_code, 0)
        observations = [
            json.loads(line)
            for line in (self.workspace / "observations.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
        ]
        self.assertEqual(
            observations[-1]["auth_sha256_at_turn_start"],
            hashlib.sha256(auditor_rotation).hexdigest(),
        )
        driver.close()

    def test_unrotated_concurrent_driver_cannot_overwrite_newer_auth(self) -> None:
        first = self.driver(state_root=self.root / "parallel-state-first")
        second = self.driver(state_root=self.root / "parallel-state-second")
        first_private = first._stage_auth()
        second._stage_auth()
        rotated = b'{"token":"first-concurrent-rotation"}\n'
        first_private.write_bytes(rotated)
        first._sync_private_auth_to_storage()
        second._sync_private_auth_to_storage()
        self.assertEqual(self.auth.read_bytes(), rotated)
        self.assertEqual(
            (second.state_root / "auth.json").read_bytes(), rotated
        )
        second._sync_private_auth_to_storage()
        self.assertEqual(self.auth.read_bytes(), rotated)
        first.close()
        second.close()

    def test_divergent_concurrent_rotations_fail_without_lost_update(self) -> None:
        first = self.driver(state_root=self.root / "divergent-state-first")
        second = self.driver(state_root=self.root / "divergent-state-second")
        first_private = first._stage_auth()
        second_private = second._stage_auth()
        rotations = {
            b'{"token":"concurrent-rotation-a"}\n',
            b'{"token":"concurrent-rotation-b"}\n',
        }
        first_private.write_bytes(sorted(rotations)[0])
        second_private.write_bytes(sorted(rotations)[1])
        barrier = threading.Barrier(2)
        errors: list[BaseException] = []
        errors_lock = threading.Lock()

        def sync(driver: CodexDriver) -> None:
            barrier.wait(timeout=2)
            try:
                driver._sync_private_auth_to_storage()
            except BaseException as error:
                with errors_lock:
                    errors.append(error)

        threads = [
            threading.Thread(target=sync, args=(first,)),
            threading.Thread(target=sync, args=(second,)),
        ]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(timeout=2)
            self.assertFalse(thread.is_alive())

        self.assertEqual(len(errors), 1)
        self.assertIsInstance(errors[0], BenchmarkError)
        self.assertIn("rotation conflict", str(errors[0]))
        self.assertIn(self.auth.read_bytes(), rotations)
        first.close()
        second.close()

    def test_nonzero_app_server_shutdown_is_archived_and_rejected(self) -> None:
        driver = self.driver()
        result = driver.run_turn(
            prompt="bad-shutdown",
            workspace=self.workspace,
            artifact_dir=self.root / "bad-shutdown-turn",
            timeout_seconds=5,
        )
        self.assertEqual(result.exit_code, 0)
        close_artifacts = self.root / "bad-shutdown-close"
        with self.assertRaisesRegex(Exception, "did not exit cleanly"):
            driver.close(artifact_dir=close_artifacts)
        shutdown = json.loads(
            (close_artifacts / "shutdown.json").read_text(encoding="utf-8")
        )
        self.assertFalse(shutdown["graceful"])
        self.assertEqual(shutdown["returncode"], 7)

    def test_protocol_message_flushed_only_at_close_rejects_condition(self) -> None:
        driver = self.driver()
        result = driver.run_turn(
            prompt="late-on-close",
            workspace=self.workspace,
            artifact_dir=self.root / "late-close-turn",
            timeout_seconds=5,
        )
        self.assertEqual(result.exit_code, 0)
        close_root = self.root / "late-close-session"
        with self.assertRaisesRegex(Exception, "after the final telemetry boundary"):
            driver.close(artifact_dir=close_root)
        shutdown = json.loads(
            (close_root / "shutdown.json").read_text(encoding="utf-8")
        )
        self.assertTrue(shutdown["stdout_drained_to_eof"])
        self.assertEqual(shutdown["late_stdout_line_count"], 1)

    def test_provider_free_preflight_stops_before_turn_start(self) -> None:
        driver = self.driver()
        record = driver.preflight(
            workspace=self.workspace,
            artifact_dir=self.root / "preflight-artifacts",
            timeout_seconds=5,
        )
        self.assertFalse(record["provider_call_permitted"])
        self.assertFalse(record["turn_start_sent"])
        self.assertTrue(record["temporary_auth_removed_after_thread_start"])
        self.assertEqual(record["thread_id"], "thread-test")
        self.assertTrue(record["capability_attestation"]["passed"])
        self.assertEqual(
            set(record["capability_attestation"]["thread_features"]["features"]),
            {"multi_agent", "multi_agent_v2"},
        )
        self.assertFalse((self.root / "state" / "auth.json").exists())
        self.assertFalse((self.workspace / "observations.jsonl").exists())

    def test_preflight_rejects_unattested_capabilities_before_provider_turn(self) -> None:
        for index, marker in enumerate((
            "capability-config-drift",
            "capability-origin-drift",
            "capability-feature-enabled",
            "capability-feature-missing",
            "capability-feature-duplicate",
            "capability-thread-feature-enabled",
        )):
            with self.subTest(marker=marker):
                flag = self.workspace / marker
                flag.touch()
                artifact_dir = self.root / f"rejected-preflight-{index}"
                driver = self.driver(state_root=self.root / f"rejected-state-{index}")
                with self.assertRaisesRegex(ProviderCapabilityError, "preflight failed"):
                    driver.preflight(
                        workspace=self.workspace,
                        artifact_dir=artifact_dir,
                        timeout_seconds=5,
                    )
                record = json.loads((artifact_dir / "preflight.json").read_text())
                self.assertEqual(record["failure_kind"], "provider_capability_violation")
                self.assertFalse(record["turn_start_sent"])
                self.assertFalse((self.workspace / "observations.jsonl").exists())
                flag.unlink()
                driver.close()

    def test_repair_rechecks_capabilities_and_stops_before_turn_start(self) -> None:
        driver = self.driver()
        first = driver.run_turn(
            prompt="first", workspace=self.workspace,
            artifact_dir=self.root / "capability-first", timeout_seconds=5,
        )
        self.assertEqual(first.exit_code, 0)
        (self.workspace / "capability-thread-feature-enabled").touch()
        second = driver.run_turn(
            prompt="repair", workspace=self.workspace,
            artifact_dir=self.root / "capability-repair", timeout_seconds=5,
            thread_id=first.thread_id,
        )
        self.assertEqual(second.failure_kind, "provider_capability_violation")
        self.assertEqual(second.exit_code, 70)
        self.assertIsNone(second.active_started_perf_ns)
        self.assertEqual(
            len((self.workspace / "observations.jsonl").read_text().splitlines()), 1
        )
        record = json.loads((self.root / "capability-repair" / "turn.json").read_text())
        self.assertFalse(record["capability_attestation"].get("passed", False))
        driver.close()

    def test_collaboration_and_foreign_threads_are_provider_capability_failures(self) -> None:
        for index, prompt in enumerate((
            "collab-started", "collab-raw", "foreign-thread", "foreign-thread-started"
        )):
            with self.subTest(prompt=prompt):
                driver = self.driver(state_root=self.root / f"violation-state-{index}")
                artifacts = self.root / f"violation-{index}"
                result = driver.run_turn(
                    prompt=prompt, workspace=self.workspace,
                    artifact_dir=artifacts, timeout_seconds=5,
                )
                self.assertEqual(result.failure_kind, "provider_capability_violation")
                self.assertEqual(result.exit_code, 70)
                record = json.loads((artifacts / "turn.json").read_text())
                self.assertTrue(record["capability_attestation"]["passed"])
                self.assertIn(
                    "thread" if "foreign" in prompt else "collaboration",
                    record["protocol_error"].lower(),
                )
                driver.close()

    def test_bwrap_shape_forces_controlled_passwd_and_clears_environment(self) -> None:
        toolchain = self.root / "toolchain"
        toolchain.mkdir()
        packages = self.root / "packages"
        (packages / "mathlib" / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
        bwrap = self.root / "bwrap"
        offline_shell = self.root / "offline-shell"
        for executable in (bwrap, offline_shell):
            executable.write_text("fixture\n", encoding="utf-8")
            executable.chmod(0o500)
        host = self.codex.with_name("codex-code-mode-host")
        host.write_bytes(b"matching code-mode host")
        host.chmod(0o500)
        artifacts = self.root / "shape-artifacts"
        artifacts.mkdir()
        driver = self.driver(
            bwrap_binary=bwrap,
            code_mode_host_sha256=hashlib.sha256(host.read_bytes()).hexdigest(),
            offline_shell=offline_shell,
            toolchain_root=toolchain,
            packages_root=packages,
        )
        inner = driver._app_server_command("/codex")
        command = driver._bwrap_command(
            inner,
            workspace=self.workspace,
            artifact_dir=artifacts,
            output_schema=None,
        )
        self.assertIn("--clearenv", command)
        self.assertIn(
            ["--ro-bind", str((driver._identity_root / "passwd").resolve()), "/etc/passwd"],
            [command[index : index + 3] for index in range(len(command) - 2)],
        )
        self.assertGreater(command.index("/etc/passwd"), command.index("/etc"))
        self.assertIn(
            ["--ro-bind", str(host.resolve()), "/codex-code-mode-host"],
            [command[index : index + 3] for index in range(len(command) - 2)],
        )
        self.assertEqual(driver.code_mode_host, host.resolve())
        self.assertIn(
            ["--setenv", "SHELL", "/offline-bash"],
            [command[index : index + 3] for index in range(len(command) - 2)],
        )
        self.assertIn(
            ["--setenv", "USER", "bench"],
            [command[index : index + 3] for index in range(len(command) - 2)],
        )
        self.assertEqual(command[-len(inner) :], inner)
        self.assertEqual(inner[:3], ["/codex", "app-server", "--stdio"])
        self.assertNotIn("/artifacts", command)
        self.assertNotIn(str(self.auth), command)
        passwd = (driver._identity_root / "passwd").read_text(encoding="utf-8")
        self.assertEqual(passwd.split(":")[-1], "/offline-bash\n")
        driver.close()

    def test_bwrap_fails_closed_for_missing_or_unpinned_code_mode_host(self) -> None:
        toolchain = self.root / "toolchain"
        toolchain.mkdir()
        packages = self.root / "packages"
        packages.mkdir()
        bwrap = self.root / "bwrap"
        offline_shell = self.root / "offline-shell"
        for executable in (bwrap, offline_shell):
            executable.write_bytes(b"fixture")
            executable.chmod(0o500)
        options = {
            "bwrap_binary": bwrap,
            "offline_shell": offline_shell,
            "toolchain_root": toolchain,
            "packages_root": packages,
        }
        host = self.codex.with_name("codex-code-mode-host")
        digest = hashlib.sha256(b"matching code-mode host").hexdigest()
        with self.assertRaisesRegex(BenchmarkError, "pinned code-mode host SHA-256"):
            self.driver(**options)
        with self.assertRaisesRegex(BenchmarkError, "missing or unsafe"):
            self.driver(**options, code_mode_host_sha256=digest)
        host.write_bytes(b"matching code-mode host")
        host.chmod(0o500)
        with self.assertRaisesRegex(BenchmarkError, "does not match deployment"):
            self.driver(**options, code_mode_host_sha256="0" * 64)
        host.chmod(0o400)
        with self.assertRaisesRegex(BenchmarkError, "not a safe executable"):
            self.driver(**options, code_mode_host_sha256=digest)
        host.unlink()
        real_host = self.root / "unverified-host"
        real_host.write_bytes(b"matching code-mode host")
        real_host.chmod(0o500)
        host.symlink_to(real_host)
        with self.assertRaisesRegex(BenchmarkError, "missing or unsafe"):
            self.driver(**options, code_mode_host_sha256=digest)
        self.assertFalse((self.root / "state").exists())

    def test_bwrap_reauthenticates_code_mode_host_before_launch(self) -> None:
        toolchain = self.root / "toolchain"
        toolchain.mkdir()
        packages = self.root / "packages"
        packages.mkdir()
        bwrap = self.root / "bwrap"
        offline_shell = self.root / "offline-shell"
        for executable in (bwrap, offline_shell):
            executable.write_bytes(b"fixture")
            executable.chmod(0o500)
        host = self.codex.with_name("codex-code-mode-host")
        host.write_bytes(b"matching code-mode host")
        host.chmod(0o500)
        driver = self.driver(
            bwrap_binary=bwrap,
            code_mode_host_sha256=hashlib.sha256(host.read_bytes()).hexdigest(),
            offline_shell=offline_shell,
            toolchain_root=toolchain,
            packages_root=packages,
        )
        host.chmod(0o700)
        host.write_bytes(b"replaced code-mode host")
        artifacts = self.root / "refused-artifacts"
        artifacts.mkdir()
        with self.assertRaisesRegex(BenchmarkError, "does not match deployment"):
            driver._bwrap_command(
                driver._app_server_command("/codex"),
                workspace=self.workspace,
                artifact_dir=artifacts,
                output_schema=None,
            )
        self.assertFalse((artifacts / "network_violations.bin").exists())
        driver.close()

    def test_bwrap_can_mount_compiled_library_without_source_or_atlas(self) -> None:
        toolchain = self.root / "toolchain-olean-only"
        toolchain.mkdir()
        packages = self.root / "packages-olean-only"
        mathlib_olean = packages / "mathlib" / ".lake" / "build" / "lib" / "lean"
        mathlib_olean.mkdir(parents=True)
        library_olean = self.root / "library-olean-only"
        library_olean.mkdir()
        bwrap = self.root / "bwrap-olean-only"
        offline_shell = self.root / "offline-shell-olean-only"
        for executable in (bwrap, offline_shell):
            executable.write_bytes(b"fixture")
            executable.chmod(0o500)
        host = self.codex.with_name("codex-code-mode-host")
        if not host.exists():
            host.write_bytes(b"matching code-mode host")
            host.chmod(0o500)
        driver = self.driver(
            bwrap_binary=bwrap,
            code_mode_host_sha256=hashlib.sha256(host.read_bytes()).hexdigest(),
            offline_shell=offline_shell,
            toolchain_root=toolchain,
            packages_root=packages,
            library_olean=library_olean,
        )
        artifacts = self.root / "olean-only-artifacts"
        artifacts.mkdir()
        command = driver._bwrap_command(
            driver._app_server_command("/codex"),
            workspace=self.workspace,
            artifact_dir=artifacts,
            output_schema=None,
        )
        rendered = "\n".join(command)
        self.assertIn("/library-olean", rendered)
        self.assertNotIn("/library/NumStability", rendered)
        self.assertNotIn("/library-index", rendered)
        driver.close()

    def test_malformed_telemetry_fails_closed_and_removes_auth(self) -> None:
        driver = self.driver()
        result = driver.run_turn(
            prompt="bad-usage",
            workspace=self.workspace,
            artifact_dir=self.root / "bad-artifacts",
            timeout_seconds=5,
        )
        self.assertNotEqual(result.exit_code, 0)
        self.assertEqual(result.usage["total_tokens"], 15)
        self.assertFalse((self.root / "state" / "auth.json").exists())
        self.assertFalse((self.root / ".state-usage.json").exists())
        record = json.loads(
            (self.root / "bad-artifacts" / "turn.json").read_text(encoding="utf-8")
        )
        self.assertIn("malformed cumulative usage", record["protocol_error"])

    def test_missing_post_terminal_telemetry_is_not_charged_as_time_limit(self) -> None:
        driver = self.driver()
        with mock.patch("codex_driver.POST_TERMINAL_TELEMETRY_TIMEOUT_SECONDS", 0.05):
            result = driver.run_turn(
                prompt="missing-usage",
                workspace=self.workspace,
                artifact_dir=self.root / "artifacts-missing-usage",
                timeout_seconds=30,
            )
        self.assertEqual(result.exit_code, 70)
        self.assertFalse(result.timed_out)
        self.assertFalse(result.usage_complete)
        self.assertEqual(result.failure_kind, "telemetry_invalid")
        record = json.loads(
            (self.root / "artifacts-missing-usage" / "turn.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertIn("telemetry", record["protocol_error"])
        driver.close()

    def test_security_sensitive_control_baseline_detects_mutation(self) -> None:
        driver = self.driver()
        first = driver.run_turn(
            prompt="first",
            workspace=self.workspace,
            artifact_dir=self.root / "baseline-artifacts",
            timeout_seconds=5,
        )
        self.assertEqual(first.exit_code, 0)
        baseline = self.root / ".state-control-baseline.json"
        self.assertTrue(baseline.is_file())
        (self.root / "state" / "config.toml").write_text(
            "fixture = false\n", encoding="utf-8"
        )
        with self.assertRaisesRegex(Exception, "control state changed"):
            driver.run_turn(
                prompt="repair",
                workspace=self.workspace,
                artifact_dir=self.root / "mutated-artifacts",
                timeout_seconds=5,
                thread_id=first.thread_id,
            )
        (self.root / "state" / "config.toml").write_text(
            "fixture = true\n", encoding="utf-8"
        )
        driver.close()

    def test_usage_rejects_overlapping_cache_breakdown(self) -> None:
        malformed = {
            "inputTokens": 10,
            "cachedInputTokens": 7,
            "cacheWriteInputTokens": 4,
            "outputTokens": 2,
            "reasoningOutputTokens": 1,
            "totalTokens": 12,
        }
        self.assertIsNone(_normalize_usage_breakdown(malformed))
        self.assertIsNone(_normalize_raw_usage(malformed))

    def test_usage_applies_documented_cache_write_schema_default(self) -> None:
        without_optional_cache_write = {
            "inputTokens": 10,
            "cachedInputTokens": 2,
            "outputTokens": 3,
            "reasoningOutputTokens": 1,
            "totalTokens": 13,
        }
        expected = {
            "input_tokens": 10,
            "cached_input_tokens": 2,
            "cache_write_input_tokens": 0,
            "output_tokens": 3,
            "reasoning_output_tokens": 1,
            "total_tokens": 13,
        }
        self.assertEqual(_normalize_raw_usage(without_optional_cache_write), expected)
        self.assertEqual(
            _normalize_usage_breakdown(without_optional_cache_write), expected
        )

    def test_cold_resume_is_rejected_for_exact_raw_metering(self) -> None:
        driver = self.driver()
        first = driver.run_turn(
            prompt="first",
            workspace=self.workspace,
            artifact_dir=self.root / "cold-first",
            timeout_seconds=5,
        )
        driver.close()
        replacement = self.driver()
        with self.assertRaisesRegex(Exception, "cold thread/resume"):
            replacement.run_turn(
                prompt="repair",
                workspace=self.workspace,
                artifact_dir=self.root / "cold-repair",
                timeout_seconds=5,
                thread_id=first.thread_id,
            )


if __name__ == "__main__":
    unittest.main()
