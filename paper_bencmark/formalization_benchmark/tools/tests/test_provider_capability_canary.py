from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from codex_driver import TurnResult  # noqa: E402
from audit_controller import (  # noqa: E402
    _validate_adjudication,
    _validate_judgment,
    _validate_translation,
)
from common import (  # noqa: E402
    BenchmarkError,
    sha256_file,
    tree_manifest,
    write_json_atomic,
)
from deployment import Deployment  # noqa: E402
import provider_capability_canary as canary  # noqa: E402


USAGE = {
    "input_tokens": 10,
    "cached_input_tokens": 2,
    "cache_write_input_tokens": 1,
    "output_tokens": 3,
    "reasoning_output_tokens": 1,
    "total_tokens": 13,
}
COMMAND_CGROUP = {
    "path": "/sys/fs/cgroup/test/highambench-commands",
    "memory_max": str(24 * 1024 * 1024 * 1024),
    "memory_swap_max": "0",
    "pids_max": "384",
    "cpu_weight": "100",
}
LIMIT_DELTA = {
    "memory_events.max": 0,
    "memory_events.oom": 0,
    "memory_events.oom_kill": 0,
    "pids_events.max": 0,
}


class FakeDriver:
    calls: list[dict] = []
    turn_overrides: dict = {}
    result_overrides: dict = {}
    role_result_overrides: dict = {}
    trace_mode: str = "normal"
    role_trace_modes: dict[str, str] = {}

    def __init__(self, **options):
        self.options = options
        self.ephemeral = False
        self.thread_id = "qualification-" + options["model"]

    def run_turn(self, **options):
        self.calls.append({"driver": self.options, "turn": options})
        self.ephemeral = options["ephemeral"]
        artifact_dir = options["artifact_dir"]
        role = artifact_dir.parent.name
        expected = (
            canary.EXPECTED_OUTPUT
            if role == canary.WARM_FORK_ROLE
            else next(item[-1] for item in canary.ROLES if item[0] == role)
        )
        warm_fork = self.options.get("fork_source_thread_id") is not None
        mode = self.role_trace_modes.get(role, self.trace_mode)
        source = options["workspace"] / canary.INPUT_NAME
        source_text = source.read_text(encoding="utf-8")
        artifact_dir.mkdir(parents=True)
        events = []
        if mode != "missing-read":
            if mode.startswith("function-call"):
                events.extend([
                    {"method": "rawResponseItem/completed", "params": {"item": {
                        "callId": "read-call", "type": "function_call",
                        "name": "exec_command",
                        "arguments": {"cmd": f"cat {canary.INPUT_NAME}"},
                    }}},
                    {"method": "rawResponseItem/completed", "params": {"item": {
                        "callId": "read-call", "type": "function_call_output",
                        "output": source_text,
                    }}},
                ])
            else:
                events.append(
                    {
                        "method": "item/started" if mode == "no-completed-read" else "item/completed",
                        "params": {
                            "item": {
                                "id": "read-tool",
                                "type": "commandExecution",
                                "command": f"cat {canary.INPUT_NAME}",
                                "aggregatedOutput": source_text,
                                "status": "completed",
                                "exitCode": 1 if mode == "failed-tool" else 0,
                            }
                        },
                    }
                )
        if self.options["workspace_writable"]:
            output = options["workspace"] / canary.OUTPUT_NAME
            if mode != "missing-output":
                written = (
                    {**expected, "weighted_sum": 206}
                    if mode == "wrong-output"
                    else expected
                )
                output.write_text(json.dumps(written), encoding="utf-8")
            if mode != "missing-write":
                if mode.startswith("function-call"):
                    events.append(
                        {"method": "rawResponseItem/completed", "params": {"item": {
                            "callId": "write-call", "type": "function_call",
                            "name": "apply_patch",
                            "arguments": {"patch": f"*** Add File: {canary.OUTPUT_NAME}"},
                        }}}
                    )
                    if mode == "function-call":
                        events.append({"method": "rawResponseItem/completed", "params": {"item": {
                            "callId": "write-call", "type": "function_call_output",
                            "output": "Success. Updated the following files",
                        }}})
                else:
                    events.append(
                        {
                            "method": "item/completed",
                            "params": {
                                "item": {
                                    "id": "write-tool",
                                    "type": "fileChange",
                                    "changes": [{"path": canary.OUTPUT_NAME, "kind": "add"}],
                                    "status": "completed",
                                }
                            },
                        }
                    )
        elif mode == "read-only-write":
            (options["workspace"] / "unexpected.txt").write_text(
                "written", encoding="utf-8"
            )
        if mode == "warning-event":
            events.append(
                {"method": "item/completed", "params": {"item": {
                    "id": "warning", "type": "agentMessage",
                    "text": "Warning: Code Mode failed to start",
                }}}
            )
        if mode == "benign-code-mode":
            events.append(
                {"method": "item/completed", "params": {"item": {
                    "id": "helper", "type": "codeModeToolCall",
                    "command": "/codex-code-mode-host", "error": None,
                    "status": "completed",
                }}}
            )
        if mode == "truncated-tool-catalog":
            events.append(
                {"method": "item/completed", "params": {"item": {
                    "id": "catalog", "type": "custom_tool_call_output",
                    "output": (
                        "Warning: truncated output (original token count: 30039)\n"
                        + "Other available tools. " * 100
                        + "Code Mode disabled is an example of a warning. "
                        + "The phrase tool execution failed is also documented here."
                    ),
                    "status": "completed",
                }}}
            )
        if mode == "diagnostic-event":
            events.append(
                {"method": "warning", "params": {"message": "Code Mode disabled"}}
            )
        if mode == "failed-output-wrapper":
            events.append(
                {"method": "item/completed", "params": {"item": {
                    "id": "failed-output", "type": "custom_tool_call_output",
                    "output": "Script failed: sandbox command could not run",
                    "status": "completed",
                }}}
            )
        if mode == "failed-function-tool":
            events.append(
                {"method": "item/completed", "params": {"item": {
                    "id": "another-tool", "type": "function_call_output",
                    "isError": True, "output": "Tool execution failed",
                }}}
            )
        events.append(
            {"method": "item/completed", "params": {"item": {
                "id": "final-message", "type": "agentMessage",
                "text": json.dumps(expected),
            }}}
        )
        (artifact_dir / "events.jsonl").write_text(
            "".join(json.dumps(event) + "\n" for event in events), encoding="utf-8"
        )
        stderr = artifact_dir / "stderr.log"
        stderr.write_text(
            "Warning: Code Mode unavailable\n" if mode == "warning-stderr"
            else (
                "2026-09-16T15:02:43.872554Z ERROR codex_core::tools::router: "
                "error=failed to spawn code-mode host /codex-code-mode-host: "
                "No such file or directory (os error 2)\n"
            ) if mode == "missing-host-stderr"
            else "Tool execution failed\n" if mode == "failed-tool-stderr"
            else "",
            encoding="utf-8",
        )
        result_options = {
            "thread_id": self.thread_id,
            "exit_code": 0,
            "timed_out": False,
            "wall_seconds": 0.5,
            "usage": dict(USAGE),
            "usage_complete": True,
            "final_message": json.dumps(expected),
            "event_count": len(events),
            "command": ["fake-codex"],
            "active_started_perf_ns": 10,
            "active_ended_perf_ns": 20,
            "failure_kind": None,
        }
        result_options.update(self.result_overrides)
        result_options.update(self.role_result_overrides.get(role, {}))
        result = TurnResult(**result_options)
        record = {
            "schema_version": 3,
            "thread_id": self.thread_id,
            "persistent_app_server_session": not self.ephemeral,
            "terminal_status": "completed",
            "exit_code": 0,
            "timed_out": False,
            "failure_kind": None,
            "usage_complete": True,
            "usage": dict(USAGE),
            "usage_measurement_mode": (
                "fork_cumulative_notifications"
                if warm_fork
                else "raw_response_events"
            ),
            "raw_response_count": 0 if warm_fork else 1,
            "cumulative_usage_notification_count": 1,
            "fork_notification_fallback_admitted": warm_fork,
            "event_count": len(events),
            "events_sha256": sha256_file(artifact_dir / "events.jsonl"),
            "stderr_sha256": sha256_file(stderr),
            "cumulative_usage_delta_cross_check": dict(USAGE),
            "cumulative_usage_expected_from_measurement": dict(USAGE),
            "capability_attestation": {
                "passed": True,
                "fork_baseline_usage_notification": (
                    {"accepted": True} if warm_fork else None
                ),
            },
            "protocol_error": None,
            "network_violation_attempts": 0,
            "event_archive_violated": False,
            "generated_command_cgroup": {
                "before": dict(COMMAND_CGROUP),
                "after": dict(COMMAND_CGROUP),
                "limit_event_delta": dict(LIMIT_DELTA),
                "violated": False,
            },
            "workspace_resource_ceiling": {"violated": False},
        }
        record.update(self.turn_overrides)
        write_json_atomic(artifact_dir / "turn.json", record, mode=0o400)
        return result

    def close(self, *, artifact_dir):
        if self.ephemeral:
            return
        artifact_dir.mkdir(parents=True)
        stderr = artifact_dir / "stderr-after-last-turn.log"
        stderr.write_bytes(b"")
        write_json_atomic(
            artifact_dir / "shutdown.json",
            {
                "thread_id": self.thread_id,
                "graceful": True,
                "returncode": 0,
                "forced_signal": None,
                "stdout_drained_to_eof": True,
                "late_stdout_line_count": 0,
                "stderr_sha256": sha256_file(stderr),
            },
            mode=0o400,
        )


class ProviderCapabilityCanaryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.run_root = self.root / "runs"
        self.run_root.mkdir()
        self.codex = self.root / "codex"
        self.codex.write_bytes(b"fake-codex")
        self.auth = self.root / "auth.json"
        self.auth.write_text(
            json.dumps({"token": "a-private-test-token-0123456789"}),
            encoding="utf-8",
        )
        self.manifest_path = self.root / "manifest.json"
        self.manifest_path.write_text("{}\n", encoding="utf-8")
        self.deployment_path = self.root / "deployment.json"
        write_json_atomic(
            self.deployment_path,
            {
                "pilot_id": "test-pilot",
                "manifest_payload_sha256": "b" * 64,
                "release_manifest_sha256": sha256_file(self.manifest_path),
                "run_root": str(self.run_root),
                "codex_binary_sha256": sha256_file(self.codex),
                "code_mode_host_sha256": "a" * 64,
                "hardware_identity": {"fixture": True},
            },
        )
        self.deployment = Deployment(
            path=self.deployment_path,
            run_root=self.run_root,
            pdf_root=self.root,
            codex_binary=self.codex,
            auth_file=self.auth,
            bwrap_binary=self.root / "bwrap",
            offline_shell=self.root / "offline-shell",
            toolchain_root=self.root / "lean",
            packages_root=self.root / "packages",
            library_source=self.root / "library",
            library_olean=self.root / "olean",
            library_snapshot_record=self.root / "library-snapshot.json",
            runtime_snapshot_record=self.root / "runtime-snapshot.json",
            strict_hardware=True,
            code_mode_host_sha256="a" * 64,
        )
        self.manifest = {
            "pilot_id": "test-pilot",
            "manifest_payload_sha256": "b" * 64,
        }
        self.config = {
            "pilot_id": "test-pilot",
            "formalizer_model": "exact-formalizer",
            "formalizer_reasoning_effort": "ultra",
            "audit_model": "exact-auditor",
            "audit_reasoning_effort": "high",
            "command_resource_envelope": {
                "memory_bytes": 24 * 1024 * 1024 * 1024,
                "tasks_max": 384,
                "command_cpu_weight": 100,
            },
        }
        for path in (
            self.deployment.library_source,
            self.deployment.library_olean,
            self.deployment.toolchain_root,
            self.deployment.packages_root,
        ):
            path.mkdir(parents=True, exist_ok=True)
        warm_root = (
            self.run_root
            / "warm-roots"
            / self.manifest["manifest_payload_sha256"]
        )
        checkpoint = warm_root / "checkpoint"
        (checkpoint / "state").mkdir(parents=True)
        (checkpoint / "state" / "fixture.txt").write_text(
            "frozen scout state\n", encoding="utf-8"
        )
        write_json_atomic(
            warm_root / "warm-root.json",
            {
                "schema_version": "formalization-warm-root-1",
                "status": "READY",
                "pilot_id": self.config["pilot_id"],
                "manifest_payload_sha256": self.manifest[
                    "manifest_payload_sha256"
                ],
                "source_thread_id": "scout-thread",
                "source_last_turn_id": "scout-turn",
                "source_cumulative_usage": dict(USAGE),
                "checkpoint_manifest": tree_manifest(checkpoint),
            },
            mode=0o400,
        )
        FakeDriver.calls = []
        FakeDriver.turn_overrides = {}
        FakeDriver.result_overrides = {}
        FakeDriver.role_result_overrides = {}
        FakeDriver.trace_mode = "normal"
        FakeDriver.role_trace_modes = {}
        self.patches = [
            mock.patch.object(canary, "CodexDriver", FakeDriver),
            mock.patch.object(canary, "MANIFEST_PATH", self.manifest_path),
            mock.patch.object(
                canary, "verify_manifest", return_value=(self.manifest, self.config)
            ),
            mock.patch.object(
                canary, "snapshot_hardware", return_value={"admitted": True}
            ),
            mock.patch.object(canary, "verify_frozen_hardware_identity"),
            mock.patch.object(
                canary, "command_cgroup_snapshot", return_value=dict(COMMAND_CGROUP)
            ),
        ]
        for patcher in self.patches:
            patcher.start()

    def tearDown(self) -> None:
        for patcher in reversed(self.patches):
            patcher.stop()
        self.temporary.cleanup()

    def test_qualifies_exact_roles_off_benchmark_and_reuses_sealed_result(self) -> None:
        first = canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(first["status"], "PASSED")
        self.assertEqual(len(FakeDriver.calls), len(canary.ROLES) + 1)
        formalizer, auditor, *remaining = FakeDriver.calls
        audit_schemas = remaining[:-1]
        warm_fork = remaining[-1]
        self.assertEqual(
            (formalizer["driver"]["model"], formalizer["driver"]["reasoning_effort"]),
            ("exact-formalizer", "ultra"),
        )
        self.assertEqual(
            (auditor["driver"]["model"], auditor["driver"]["reasoning_effort"]),
            ("exact-auditor", "high"),
        )
        self.assertTrue(formalizer["driver"]["workspace_writable"])
        self.assertEqual(
            formalizer["driver"]["code_mode_host_sha256"],
            self.deployment.code_mode_host_sha256,
        )
        self.assertFalse(formalizer["turn"]["ephemeral"])
        self.assertFalse(auditor["driver"]["workspace_writable"])
        self.assertTrue(auditor["turn"]["ephemeral"])
        self.assertEqual(
            formalizer["turn"]["output_schema"].name, "output_schema.json"
        )
        self.assertEqual(
            json.loads(formalizer["turn"]["output_schema"].read_text()),
            canary.OUTPUT_SCHEMA,
        )
        self.assertEqual(len(audit_schemas), 4)
        for audit_role, schema_name, expected in canary.AUDIT_SCHEMA_PROBES:
            call = next(
                item
                for item in audit_schemas
                if item["turn"]["artifact_dir"].parent.name
                == f"audit-schema-{audit_role}"
            )
            self.assertEqual(call["driver"]["model"], "exact-auditor")
            self.assertTrue(call["turn"]["ephemeral"])
            self.assertEqual(
                call["turn"]["output_schema"].read_bytes(),
                (canary.AUDIT_SCHEMAS / schema_name).read_bytes(),
            )
            self.assertNotIn(json.dumps(expected), call["turn"]["prompt"])
            self.assertEqual(
                json.loads(
                    (call["turn"]["workspace"] / canary.INPUT_NAME).read_text()
                )["expected_output"],
                expected,
            )
        self.assertEqual(
            warm_fork["turn"]["artifact_dir"].parent.name,
            canary.WARM_FORK_ROLE,
        )
        self.assertEqual(
            warm_fork["driver"]["fork_source_thread_id"], "scout-thread"
        )
        self.assertEqual(
            warm_fork["driver"]["fork_source_last_turn_id"], "scout-turn"
        )
        for role, outcome in first["record"]["role_outcomes"].items():
            self.assertGreaterEqual(outcome["workspace_tool_probe"]["read_tool_items"], 1)
            self.assertEqual(
                outcome["workspace_tool_probe"]["write_tool_items"] >= 1,
                role in {"formalizer", canary.WARM_FORK_ROLE},
            )
        self.assertEqual(first["record"]["provider_turns"], 7)
        self.assertEqual(first["record"]["provider_calls"], 7)
        self.assertEqual(
            first["record"]["role_outcomes"][canary.WARM_FORK_ROLE][
                "usage_measurement_mode"
            ],
            "fork_cumulative_notifications",
        )
        self.assertFalse(first["record"]["charged_to_contestant"])
        self.assertFalse((self.run_root / "pairs").exists())
        self.assertFalse((self.run_root / "index").exists())
        second = canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(second["record_sha256"], first["record_sha256"])
        self.assertEqual(len(FakeDriver.calls), 7)

    def test_function_call_tool_trace_is_accepted_when_file_is_checked(self) -> None:
        FakeDriver.trace_mode = "function-call"
        result = canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(result["status"], "PASSED")
        self.assertEqual(len(FakeDriver.calls), 7)

    def test_raw_function_call_without_tool_result_is_not_a_write(self) -> None:
        FakeDriver.trace_mode = "function-call-no-write-result"
        with self.assertRaisesRegex(BenchmarkError, "file-write tool"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_benign_code_mode_tool_name_is_not_a_startup_warning(self) -> None:
        FakeDriver.trace_mode = "benign-code-mode"
        result = canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(result["status"], "PASSED")

    def test_truncated_tool_catalog_is_not_a_code_mode_startup_warning(self) -> None:
        FakeDriver.trace_mode = "truncated-tool-catalog"
        result = canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(result["status"], "PASSED")

    def test_auditor_schema_probes_satisfy_audit_contracts(self) -> None:
        for role, _schema, expected in canary.AUDIT_SCHEMA_PROBES:
            if role == "blind-translation":
                _validate_translation(
                    expected,
                    canary.SYNTHETIC_SEMANTIC_SHA256,
                    [],
                )
            elif role == "adjudicator":
                _validate_adjudication(
                    expected,
                    paper_sha256=canary.SYNTHETIC_PAPER_SHA256,
                    semantic_sha256=canary.SYNTHETIC_SEMANTIC_SHA256,
                    trigger=["synthetic disagreement"],
                )
            else:
                _validate_judgment(
                    expected,
                    role=role,
                    paper_sha256=canary.SYNTHETIC_PAPER_SHA256,
                    semantic_sha256=canary.SYNTHETIC_SEMANTIC_SHA256,
                    dependencies=[],
                )

    def test_incomplete_telemetry_fails_closed_and_does_not_retry(self) -> None:
        FakeDriver.turn_overrides = {"usage_complete": False}
        with self.assertRaisesRegex(BenchmarkError, "capability gate"):
            canary.run_provider_capability_canary(self.deployment)
        FakeDriver.turn_overrides = {}
        with self.assertRaisesRegex(BenchmarkError, "failed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)
        self.assertFalse((self.run_root / "index").exists())

    def test_capability_violation_fails_closed_before_auditor(self) -> None:
        FakeDriver.turn_overrides = {
            "failure_kind": "provider_capability_violation",
            "capability_attestation": {"passed": False},
        }
        with self.assertRaisesRegex(BenchmarkError, "capability gate"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_wrong_parallel_check_output_fails_closed(self) -> None:
        FakeDriver.result_overrides = {"final_message": '{"weighted_sum": 206, "reversed_text": "LACIREMUN"}'}
        with self.assertRaisesRegex(BenchmarkError, "wrong checkable output"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_missing_completed_file_read_fails_closed(self) -> None:
        FakeDriver.trace_mode = "no-completed-read"
        with self.assertRaisesRegex(BenchmarkError, "file-read tool"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_missing_file_write_tool_fails_even_with_correct_file(self) -> None:
        FakeDriver.trace_mode = "missing-write"
        with self.assertRaisesRegex(BenchmarkError, "file-write tool"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_missing_file_write_fails_even_with_correct_final_json(self) -> None:
        FakeDriver.trace_mode = "missing-output"
        with self.assertRaisesRegex(BenchmarkError, "file-write is missing"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_wrong_file_write_fails_even_with_correct_final_json(self) -> None:
        FakeDriver.trace_mode = "wrong-output"
        with self.assertRaisesRegex(BenchmarkError, "wrong content"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_paper_facing_schema_role_must_read_file(self) -> None:
        FakeDriver.role_trace_modes = {"audit-schema-blind-translation": "missing-read"}
        with self.assertRaisesRegex(BenchmarkError, "file-read tool"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 3)

    def test_read_only_role_cannot_write_an_unexpected_workspace_file(self) -> None:
        FakeDriver.role_trace_modes = {"auditor": "read-only-write"}
        with self.assertRaisesRegex(BenchmarkError, "read-only workspace was written"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 2)

    def test_code_mode_warning_in_event_fails_closed(self) -> None:
        FakeDriver.trace_mode = "warning-event"
        with self.assertRaisesRegex(BenchmarkError, "Code Mode warning"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_code_mode_warning_in_stderr_fails_closed(self) -> None:
        FakeDriver.trace_mode = "warning-stderr"
        with self.assertRaisesRegex(BenchmarkError, "Code Mode warning"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_missing_code_mode_host_stderr_fails_closed(self) -> None:
        FakeDriver.trace_mode = "missing-host-stderr"
        with self.assertRaisesRegex(BenchmarkError, "Code Mode warning"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_explicit_code_mode_diagnostic_event_fails_closed(self) -> None:
        FakeDriver.trace_mode = "diagnostic-event"
        with self.assertRaisesRegex(BenchmarkError, "Code Mode warning"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_failed_command_tool_fails_closed(self) -> None:
        FakeDriver.trace_mode = "failed-tool"
        with self.assertRaisesRegex(BenchmarkError, "tool failed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_failed_function_tool_fails_closed(self) -> None:
        FakeDriver.trace_mode = "failed-function-tool"
        with self.assertRaisesRegex(BenchmarkError, "tool failed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_failed_tool_output_wrapper_fails_closed(self) -> None:
        FakeDriver.trace_mode = "failed-output-wrapper"
        with self.assertRaisesRegex(BenchmarkError, "tool failed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_failed_tool_stderr_fails_closed(self) -> None:
        FakeDriver.trace_mode = "failed-tool-stderr"
        with self.assertRaisesRegex(BenchmarkError, "tool failed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_missing_command_cgroup_attestation_blocks_paid_calls(self) -> None:
        with mock.patch.object(canary, "command_cgroup_snapshot", return_value=None):
            with self.assertRaisesRegex(BenchmarkError, "command cgroup"):
                canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(FakeDriver.calls, [])

    def test_wrong_turn_cgroup_fails_closed(self) -> None:
        FakeDriver.turn_overrides = {
            "generated_command_cgroup": {
                "before": {**COMMAND_CGROUP, "memory_max": "max"},
                "after": dict(COMMAND_CGROUP),
                "limit_event_delta": dict(LIMIT_DELTA),
                "violated": False,
            }
        }
        with self.assertRaisesRegex(BenchmarkError, "command cgroup"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 1)

    def test_tampered_sealed_role_artifacts_are_rejected(self) -> None:
        first = canary.run_provider_capability_canary(self.deployment)
        artifact = (
            Path(first["record_path"]).parent
            / "roles"
            / "formalizer"
            / "turn"
            / "events.jsonl"
        )
        artifact.write_text("tampered\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkError, "sealed evidence changed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 7)

    def test_auditor_schema_probe_fails_closed_without_an_official_pair(self) -> None:
        FakeDriver.role_result_overrides = {
            "audit-schema-blind-translation": {"exit_code": 70, "final_message": ""}
        }
        with self.assertRaisesRegex(BenchmarkError, "did not complete exactly"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 3)
        record = next((self.run_root / "qualifications").rglob("qualification.json"))
        self.assertEqual(json.loads(record.read_text())["status"], "FAILED")
        self.assertFalse((self.run_root / "pairs").exists())
        self.assertFalse((self.run_root / "index").exists())
        with self.assertRaisesRegex(BenchmarkError, "failed"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(len(FakeDriver.calls), 3)

    def test_deployment_release_mismatch_blocks_paid_calls(self) -> None:
        self.manifest_path.write_text('{"changed":true}\n', encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkError, "identity mismatch"):
            canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(FakeDriver.calls, [])


if __name__ == "__main__":
    unittest.main()
