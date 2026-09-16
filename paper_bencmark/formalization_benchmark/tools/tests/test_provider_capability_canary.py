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
from common import BenchmarkError, sha256_file, write_json_atomic  # noqa: E402
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

    def __init__(self, **options):
        self.options = options
        self.ephemeral = False
        self.thread_id = "qualification-" + options["model"]

    def run_turn(self, **options):
        self.calls.append({"driver": self.options, "turn": options})
        self.ephemeral = options["ephemeral"]
        artifact_dir = options["artifact_dir"]
        role = artifact_dir.parent.name
        expected = next(item[-1] for item in canary.ROLES if item[0] == role)
        artifact_dir.mkdir(parents=True)
        (artifact_dir / "events.jsonl").write_text("{}\n", encoding="utf-8")
        result_options = {
            "thread_id": self.thread_id,
            "exit_code": 0,
            "timed_out": False,
            "wall_seconds": 0.5,
            "usage": dict(USAGE),
            "usage_complete": True,
            "final_message": json.dumps(expected),
            "event_count": 1,
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
            "raw_response_count": 1,
            "event_count": 1,
            "cumulative_usage_delta_cross_check": dict(USAGE),
            "capability_attestation": {"passed": True},
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
        FakeDriver.calls = []
        FakeDriver.turn_overrides = {}
        FakeDriver.result_overrides = {}
        FakeDriver.role_result_overrides = {}
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
        self.assertEqual(len(FakeDriver.calls), len(canary.ROLES))
        formalizer, auditor, *audit_schemas = FakeDriver.calls
        self.assertEqual(
            (formalizer["driver"]["model"], formalizer["driver"]["reasoning_effort"]),
            ("exact-formalizer", "ultra"),
        )
        self.assertEqual(
            (auditor["driver"]["model"], auditor["driver"]["reasoning_effort"]),
            ("exact-auditor", "high"),
        )
        self.assertTrue(formalizer["driver"]["workspace_writable"])
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
            self.assertIn(
                json.dumps(expected, sort_keys=True, separators=(",", ":")),
                call["turn"]["prompt"],
            )
        self.assertEqual(first["record"]["provider_turns"], 6)
        self.assertEqual(first["record"]["provider_calls"], 6)
        self.assertFalse(first["record"]["charged_to_contestant"])
        self.assertFalse((self.run_root / "pairs").exists())
        self.assertFalse((self.run_root / "index").exists())
        second = canary.run_provider_capability_canary(self.deployment)
        self.assertEqual(second["record_sha256"], first["record_sha256"])
        self.assertEqual(len(FakeDriver.calls), 6)

    def test_auditor_schema_probes_satisfy_audit_contracts(self) -> None:
        for role, _schema, expected in canary.AUDIT_SCHEMA_PROBES:
            if role == "blind-translation":
                _validate_translation(expected, canary.SYNTHETIC_SEMANTIC_SHA256)
            elif role == "adjudicator":
                _validate_adjudication(
                    expected,
                    paper_sha256=canary.SYNTHETIC_PAPER_SHA256,
                    semantic_sha256=canary.SYNTHETIC_SEMANTIC_SHA256,
                )
            else:
                _validate_judgment(
                    expected,
                    role=role,
                    paper_sha256=canary.SYNTHETIC_PAPER_SHA256,
                    semantic_sha256=canary.SYNTHETIC_SEMANTIC_SHA256,
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
        self.assertEqual(len(FakeDriver.calls), 6)

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
