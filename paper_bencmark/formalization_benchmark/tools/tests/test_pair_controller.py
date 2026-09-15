from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import types
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import (  # noqa: E402
    BenchmarkError,
    file_tree_fingerprint,
    sha256_bytes,
    sha256_file,
    treatment_free_runtime_manifest,
    tree_manifest,
)
from deployment import Deployment  # noqa: E402
from manifest_control import verify_manifest  # noqa: E402
from pair_controller import PairController  # noqa: E402


class PairControllerDryRunTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        executable = self.root / "fake-tool"
        executable.write_text("#!/bin/sh\necho codex-cli-test\n", encoding="utf-8")
        executable.chmod(0o700)
        toolchain = self.root / "toolchain"
        (toolchain / "bin").mkdir(parents=True)
        lean = toolchain / "bin" / "lean"
        lean.write_text("#!/bin/sh\necho Lean-version-test\n", encoding="utf-8")
        lean.chmod(0o700)
        lake = toolchain / "bin" / "lake"
        lake.write_text("#!/bin/sh\necho Lake-version-test\n", encoding="utf-8")
        lake.chmod(0o700)
        packages = self.root / "packages"
        (packages / "mathlib" / ".lake" / "build" / "lib" / "lean").mkdir(
            parents=True
        )
        library_source = self.root / "library" / "source" / "NumStability"
        library_olean = self.root / "library" / "olean"
        library_build = self.root / "library" / "build"
        library_source.mkdir(parents=True)
        library_olean.mkdir(parents=True)
        library_build.mkdir(parents=True)
        (library_olean / "NumStability.olean").write_bytes(b"fixture-olean")
        build_output = library_build / "build-output.log"
        build_time = library_build / "gnu-time.txt"
        build_output.write_text("fixture build\n", encoding="utf-8")
        build_time.write_text("fixture time\n", encoding="utf-8")
        source_commit = "45813a95dacf577461bae13f033af0dbc985a225"
        mathlib_commit = "e8ea1afc32790ce1d4e1a4e45cc412ba9388716b"
        dependency_packages = [
            {
                "name": "mathlib",
                "manifest_revision": mathlib_commit,
                "head_commit": mathlib_commit,
                "git_clean": True,
                "olean": {
                    "present": True,
                    "file_count": 1,
                    "bytes": 13,
                    "tree_sha256": "d" * 64,
                },
            }
        ]
        dependency_closure = {
            "lake_manifest_sha256": "c" * 64,
            "package_count": 1,
            "dependency_olean_file_count": 1,
            "dependency_olean_bytes": 13,
            "closure_sha256": sha256_bytes(
                json.dumps(
                    dependency_packages, sort_keys=True, separators=(",", ":")
                ).encode("utf-8")
            ),
            "packages": dependency_packages,
        }
        git_state = {"head_commit": source_commit, "clean": True}
        source_tree_fingerprint = {
            "file_count": 0,
            "bytes": 0,
            "tree_sha256": "a" * 64,
        }
        root_module_fingerprint = {"bytes": 0, "sha256": "b" * 64}
        source_fingerprint = {
            "source_tree": source_tree_fingerprint,
            "root_module": root_module_fingerprint,
            "combined_sha256": sha256_bytes(
                json.dumps(
                    {
                        "source_tree": source_tree_fingerprint,
                        "root_module": root_module_fingerprint,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ),
        }
        project_configuration = {
            "lakefile.toml": {"bytes": 1, "sha256": "1" * 64},
            "lake-manifest.json": {"bytes": 1, "sha256": "c" * 64},
            "lean-toolchain": {
                "bytes": 1,
                "sha256": "2" * 64,
                "value": "leanprover/lean4:v4.29.0-rc3",
            },
        }
        cgroup = {
            "memory_current_bytes": 1024,
            "memory_peak_bytes": 2048,
            "memory_swap_current_bytes": 0,
            "pids_current": 2,
            "memory_events": {"max": 0, "oom": 0, "oom_kill": 0},
            "pids_events": {"max": 0},
            "cpu_stat": {"usage_usec": 1, "user_usec": 1, "system_usec": 0},
        }
        build_record = {
                    "schema_version": "numstability-setup-build-1",
                    "benchmark_charged": False,
                    "source_commit": source_commit,
                    "mathlib_commit": mathlib_commit,
                    "lean_toolchain": "leanprover/lean4:v4.29.0-rc3",
                    "logical_command": ["lake", "build", "NumStability"],
                    "build_environment": {
                        "CC": "/usr/bin/cc",
                        "HOME": "/nonexistent",
                        "LANG": "C",
                        "LC_ALL": "C",
                        "PATH": "/toolchain/bin:/usr/bin:/bin",
                        "TMPDIR": "/tmp",
                        "TZ": "UTC",
                    },
                    "tool_versions": {
                        "lake": "Lake-version-test",
                        "lean": "Lean-version-test",
                        "gnu_time": "time (GNU Time) test",
                    },
                    "tool_hashes": {
                        "lake_sha256": sha256_file(lake),
                        "lean_sha256": sha256_file(lean),
                        "gnu_time_sha256": sha256_file(Path("/usr/bin/time")),
                    },
                    "cache_state": {
                        "dependency_cache_prepared_before_measurement": True,
                        "project_cleaned_immediately_before_measurement": True,
                        "prebuild_project_tree": {
                            "present": False,
                            "file_count": 0,
                            "bytes": 0,
                            "tree_sha256": "f" * 64,
                        },
                        "dependency_closure_before": dependency_closure,
                        "dependency_closure_after": dependency_closure,
                        "dependency_closure_unchanged": True,
                    },
                    "source_inputs": {
                        "git_before": git_state,
                        "git_after": git_state,
                        "fingerprint_before": source_fingerprint,
                        "fingerprint_after": source_fingerprint,
                        "unchanged": True,
                    },
                    "project_configuration": {
                        "before": project_configuration,
                        "after": project_configuration,
                        "unchanged": True,
                    },
                    "returncode": 0,
                    "timed_out": False,
                    "output_limit_exceeded": False,
                    "resource_limit_exceeded": False,
                    "hardware_before": {"admitted": True, "cgroup_v2_path": "/fixture"},
                    "hardware_after": {"admitted": True, "cgroup_v2_path": "/fixture"},
                    "cgroup_before": cgroup,
                    "cgroup_after": cgroup,
                    "cgroup_counter_delta": {
                        "cpu_stat": {"usage_usec": 0, "user_usec": 0, "system_usec": 0},
                        "memory_events": {"max": 0, "oom": 0, "oom_kill": 0},
                        "pids_events": {"max": 0},
                    },
                    "generated_output_tree": {
                        "present": True,
                        **file_tree_fingerprint(library_olean),
                    },
                    "generated_olean": {
                        "present": True,
                        **file_tree_fingerprint(library_olean, suffix=".olean"),
                    },
                    "build_output": {
                        "relative_path": build_output.name,
                        "bytes": build_output.stat().st_size,
                        "sha256": sha256_file(build_output),
                    },
                    "gnu_time": {
                        "relative_path": build_time.name,
                        "bytes": build_time.stat().st_size,
                        "sha256": sha256_file(build_time),
                    },
                }
        (library_build / "build-record.json").write_text(
            json.dumps(build_record), encoding="utf-8"
        )
        snapshot = self.root / "library" / "snapshot.json"
        snapshot.write_text(
            json.dumps(
                {
                    "schema_version": "numstability-formalization-snapshot-1",
                    "commit": source_commit,
                    "source": tree_manifest(library_source.parent),
                    "olean": tree_manifest(library_olean),
                    "build": tree_manifest(library_build),
                }
            ),
            encoding="utf-8",
        )
        runtime_snapshot = self.root / "runtime-snapshot.json"
        runtime_snapshot.write_text(
            json.dumps(
                {
                    "schema_version": "formalization-runtime-snapshot-1",
                    "lean_toolchain": "leanprover/lean4:v4.29.0-rc3",
                    "mathlib_commit": mathlib_commit,
                    "toolchain": tree_manifest(toolchain),
                    "packages": tree_manifest(packages),
                    "condition_n_treatment_absence": treatment_free_runtime_manifest(
                        {"packages": packages, "toolchain": toolchain}
                    ),
                }
            ),
            encoding="utf-8",
        )
        auth = self.root / "auth.json"
        auth.write_text(
            '{"tokens":{"access_token":"fixture-secret-token-123456789"}}\n',
            encoding="utf-8",
        )
        pdf_root = self.root / "pdfs"
        pdf_root.mkdir()
        self.paper = pdf_root / "paper.pdf"
        self.paper.write_bytes(b"%PDF-1.4\nprovider-free fixture\n")
        deployment_record = self.root / "deployment.json"
        deployment_record.write_text("{}\n", encoding="utf-8")
        self.deployment = Deployment(
            path=deployment_record,
            run_root=self.root / "runs",
            pdf_root=pdf_root,
            codex_binary=executable,
            auth_file=auth,
            bwrap_binary=executable,
            offline_shell=executable,
            toolchain_root=toolchain,
            packages_root=packages,
            library_source=library_source,
            library_olean=library_olean,
            library_snapshot_record=snapshot,
            runtime_snapshot_record=runtime_snapshot,
            strict_hardware=False,
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def controller(self) -> PairController:
        controller = PairController(
            self.deployment, allow_unenforced_hardware=True
        )
        packet_path = ROOT / "packets" / "P01-T2.json"
        packet = json.loads(packet_path.read_text(encoding="utf-8"))

        def fixture_inputs(_self: PairController, task_id: str):
            self.assertEqual(task_id, "P01-T2")
            return self.paper, packet_path, packet

        controller._paper_and_packet = types.MethodType(fixture_inputs, controller)
        return controller

    @staticmethod
    def write_fake_shutdown(condition_root: Path) -> None:
        close_root = condition_root / "formalizer-session-close"
        close_root.mkdir(parents=True, exist_ok=True)
        stderr = close_root / "stderr-after-last-turn.log"
        stderr.write_bytes(b"")
        (close_root / "shutdown.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "thread_id": "synthetic-thread",
                    "returncode_before_close": None,
                    "returncode": 0,
                    "forced_signal": None,
                    "graceful": True,
                    "stdout_drained_to_eof": True,
                    "late_stdout_line_count": 0,
                    "stderr_scope": "synthetic fixture",
                    "stderr_bytes": 0,
                    "stderr_sha256": hashlib.sha256(b"").hexdigest(),
                }
            ),
            encoding="utf-8",
        )

    def test_release_manifest_and_provider_free_pair_staging(self) -> None:
        manifest, config = verify_manifest()
        self.assertEqual(manifest["task_ids"], config["task_ids"])
        controller = self.controller()
        first = controller.run("P01-T2", dry_run=True)
        self.assertEqual(first["status"], "DRY_RUN_COMPLETE")
        self.assertEqual(first["condition_order"], ["N", "L"])
        pair_root = Path(first["pair_root"])
        n_prompt = (pair_root / "conditions" / "N" / "prompt.txt").read_bytes()
        l_prompt = (pair_root / "conditions" / "L" / "prompt.txt").read_bytes()
        common = (ROOT / "prompts" / "formalizer.md").read_bytes()
        appendix = (ROOT / "prompts" / "condition_L.md").read_bytes()
        self.assertEqual(n_prompt, common)
        self.assertEqual(l_prompt, common + appendix)
        n_workspace = pair_root / "conditions" / "N" / "workspace"
        n_surface = b"".join(
            path.read_bytes() for path in n_workspace.rglob("*") if path.is_file()
        )
        self.assertNotIn(b"NumStability", n_surface)
        second = controller.run("P01-T2", dry_run=True)
        self.assertNotEqual(second["run_id"], first["run_id"])
        self.assertEqual(controller.status("P01-T2")["status"], "NOT_STARTED")
        self.assertFalse((self.deployment.run_root / "index" / "P01-T2.json").exists())
        self.assertEqual(
            len(list((self.deployment.run_root / "preflights").iterdir())), 2
        )

    def test_doctor_rejects_mutated_library_build_output(self) -> None:
        output = self.deployment.library_snapshot_record.parent / "build" / "build-output.log"
        output.write_text("mutated build evidence\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkError, "setup build evidence"):
            self.controller().run("P01-T2", dry_run=True)

    def test_reissuing_live_run_resumes_between_sealed_conditions(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {
                "status": "admitted",
                "task_id": task_id,
                "condition_order": ["N", "L"],
                "strict_hardware_enforced": True,
                "measurement_admissible": True,
            },
            controller,
        )
        calls: list[str] = []

        def interrupted_run_condition(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            calls.append(condition)
            if condition == "L":
                raise KeyboardInterrupt("synthetic host interruption")
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "ATTEMPT_LIMIT",
                "active_seconds": 12.5,
                "contestant_usage": {
                    "input_tokens": 10,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 5,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 15,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            state_path = (
                kwargs["pair_root"]
                / "conditions"
                / condition
                / "condition_state.json"
            )
            state_path.write_text(json.dumps(result), encoding="utf-8")
            self.write_fake_shutdown(state_path.parent)
            return result

        controller._run_condition = types.MethodType(
            interrupted_run_condition, controller
        )
        with self.assertRaises(KeyboardInterrupt):
            controller.run("P01-T2")
        interrupted = controller.status("P01-T2")
        run_id = interrupted["run_id"]
        self.assertEqual(interrupted["status"], "RUNNING")
        self.assertIn("N", interrupted["conditions"])

        def resumed_run_condition(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            calls.append(condition)
            self.assertEqual(condition, "L")
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "ACCEPTED_FAITHFUL",
                "active_seconds": 8.0,
                "contestant_usage": {
                    "input_tokens": 20,
                    "cached_input_tokens": 2,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 7,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 27,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            state_path = (
                kwargs["pair_root"]
                / "conditions"
                / condition
                / "condition_state.json"
            )
            state_path.write_text(json.dumps(result), encoding="utf-8")
            self.write_fake_shutdown(state_path.parent)
            return result

        controller._run_condition = types.MethodType(resumed_run_condition, controller)
        completed = controller.run("P01-T2")
        self.assertEqual(completed["status"], "COMPLETE")
        self.assertEqual(completed["run_id"], run_id)
        self.assertEqual(calls, ["N", "L", "L"])
        repeated = controller.run("P01-T2")
        self.assertEqual(repeated["run_id"], run_id)
        self.assertEqual(calls, ["N", "L", "L"])

    def test_official_run_rejects_unenforced_deployment(self) -> None:
        controller = self.controller()
        with self.assertRaisesRegex(
            RuntimeError, "require strict hardware and release enforcement"
        ):
            controller.run("P01-T2", dry_run=False)

    def test_terminal_condition_without_shutdown_is_unscored_pair_incident(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {
                "status": "admitted",
                "task_id": task_id,
                "condition_order": ["N", "L"],
            },
            controller,
        )

        def terminal_then_teardown_failure(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            self.assertEqual(condition, "N")
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "ACCEPTED_FAITHFUL",
                "active_seconds": 4.25,
                "contestant_usage": {
                    "input_tokens": 8,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 3,
                    "reasoning_output_tokens": 1,
                    "total_tokens": 11,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            state_path = (
                kwargs["pair_root"]
                / "conditions"
                / condition
                / "condition_state.json"
            )
            state_path.write_text(json.dumps(result), encoding="utf-8")
            raise BenchmarkError("synthetic missing shutdown evidence")

        controller._run_condition = types.MethodType(
            terminal_then_teardown_failure, controller
        )
        incident = controller.run("P01-T2")
        self.assertEqual(incident["status"], "PAIR_INCIDENT")
        self.assertEqual(incident["conditions"], {})
        partial = incident["partial_condition_evidence"]
        self.assertEqual(partial["status"], "ACCEPTED_FAITHFUL")
        self.assertIs(partial["scoreable"], False)
        self.assertEqual(incident["contestant_active_seconds_total"], 4.25)
        repeated = controller.run("P01-T2")
        self.assertEqual(repeated["run_id"], incident["run_id"])
        self.assertEqual(repeated["pair_report_sha256"], incident["pair_report_sha256"])

    def test_report_first_recovery_authenticates_recovered_terminal_condition(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {
                "status": "admitted",
                "task_id": task_id,
                "condition_order": ["N", "L"],
            },
            controller,
        )

        def terminal_then_failure(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "RULE_VIOLATION",
                "active_seconds": 2.0,
                "contestant_usage": {
                    "input_tokens": 2,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 1,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 3,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            state_path = (
                kwargs["pair_root"]
                / "conditions"
                / condition
                / "condition_state.json"
            )
            state_path.write_text(json.dumps(result), encoding="utf-8")
            raise BenchmarkError("synthetic post-terminal infrastructure failure")

        controller._run_condition = types.MethodType(terminal_then_failure, controller)
        import pair_controller as pair_module

        real_write_state = pair_module._write_state
        crashed = False

        def crash_after_report_before_terminal_state(path: Path, state: dict):
            nonlocal crashed
            if (
                not crashed
                and path.name == "pair_state.json"
                and state.get("status") == "PAIR_INCIDENT"
                and (path.parent / "pair_report.json").is_file()
            ):
                crashed = True
                raise KeyboardInterrupt("synthetic report-first crash")
            real_write_state(path, state)

        with mock.patch(
            "pair_controller._write_state",
            side_effect=crash_after_report_before_terminal_state,
        ):
            with self.assertRaises(KeyboardInterrupt):
                controller.run("P01-T2")

        reported = controller.status("P01-T2")
        self.assertEqual(reported["status"], "PAIR_INCIDENT")
        self.assertEqual(reported["conditions"]["N"]["status"], "RULE_VIOLATION")

        controller._run_condition = types.MethodType(
            lambda _self, **kwargs: self.fail("report recovery must not rerun a condition"),
            controller,
        )
        recovered = controller.run("P01-T2")
        self.assertEqual(recovered["status"], "PAIR_INCIDENT")
        self.assertEqual(recovered["conditions"]["N"]["status"], "RULE_VIOLATION")
        self.assertNotIn("partial_condition_evidence", recovered)
        self.assertEqual(recovered["contestant_active_seconds_total"], 2.0)

    def test_report_first_recovery_authenticates_partial_terminal_evidence(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {
                "status": "admitted",
                "task_id": task_id,
                "condition_order": ["N", "L"],
            },
            controller,
        )

        def unsealed_terminal_then_failure(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "ACCEPTED_FAITHFUL",
                "active_seconds": 3.5,
                "contestant_usage": {
                    "input_tokens": 5,
                    "cached_input_tokens": 1,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 2,
                    "reasoning_output_tokens": 1,
                    "total_tokens": 7,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            state_path = (
                kwargs["pair_root"]
                / "conditions"
                / condition
                / "condition_state.json"
            )
            state_path.write_text(json.dumps(result), encoding="utf-8")
            raise BenchmarkError("synthetic missing graceful shutdown")

        controller._run_condition = types.MethodType(
            unsealed_terminal_then_failure, controller
        )
        import pair_controller as pair_module

        real_write_state = pair_module._write_state
        crashed = False

        def crash_after_report_before_terminal_state(path: Path, state: dict):
            nonlocal crashed
            if (
                not crashed
                and path.name == "pair_state.json"
                and state.get("status") == "PAIR_INCIDENT"
                and (path.parent / "pair_report.json").is_file()
            ):
                crashed = True
                raise KeyboardInterrupt("synthetic report-first partial crash")
            real_write_state(path, state)

        with mock.patch(
            "pair_controller._write_state",
            side_effect=crash_after_report_before_terminal_state,
        ):
            with self.assertRaises(KeyboardInterrupt):
                controller.run("P01-T2")

        controller._run_condition = types.MethodType(
            lambda _self, **kwargs: self.fail("report recovery must not rerun a condition"),
            controller,
        )
        recovered = controller.run("P01-T2")
        self.assertEqual(recovered["status"], "PAIR_INCIDENT")
        self.assertEqual(recovered["conditions"], {})
        self.assertEqual(
            recovered["partial_condition_evidence"]["status"],
            "ACCEPTED_FAITHFUL",
        )
        self.assertIs(recovered["partial_condition_evidence"]["scoreable"], False)
        self.assertEqual(recovered["contestant_active_seconds_total"], 3.5)

    def test_crash_after_sealed_incident_cannot_resume_to_complete(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {
                "status": "admitted",
                "task_id": task_id,
                "condition_order": ["N", "L"],
            },
            controller,
        )
        calls: list[str] = []

        def incident_condition(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            calls.append(condition)
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "RULE_VIOLATION",
                "active_seconds": 1.0,
                "contestant_usage": {
                    "input_tokens": 1,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 1,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 2,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            state_path = (
                kwargs["pair_root"]
                / "conditions"
                / condition
                / "condition_state.json"
            )
            state_path.write_text(json.dumps(result), encoding="utf-8")
            return result

        controller._run_condition = types.MethodType(incident_condition, controller)
        import pair_controller as pair_module

        real_write_state = pair_module._write_state
        crashed = False

        def crash_after_summary(path: Path, state: dict):
            nonlocal crashed
            real_write_state(path, state)
            if (
                not crashed
                and path.name == "pair_state.json"
                and state.get("status") == "RUNNING"
                and state.get("conditions", {}).get("N", {}).get("status")
                == "RULE_VIOLATION"
            ):
                crashed = True
                raise KeyboardInterrupt("synthetic crash after sealed summary")

        with mock.patch("pair_controller._write_state", side_effect=crash_after_summary):
            with self.assertRaises(KeyboardInterrupt):
                controller.run("P01-T2")

        controller._run_condition = types.MethodType(
            lambda _self, **kwargs: self.fail("another condition must not run"),
            controller,
        )
        resumed = controller.run("P01-T2")
        self.assertEqual(resumed["status"], "PAIR_INCIDENT")
        self.assertEqual(resumed["conditions"]["N"]["status"], "RULE_VIOLATION")
        self.assertNotIn("L", resumed["conditions"])
        self.assertEqual(calls, ["N"])
        self.assertEqual(resumed["contestant_active_seconds_total"], 1.0)
        report = Path(resumed["pair_root"]) / "pair_report.json"
        self.assertTrue(report.is_file())
        self.assertEqual(
            resumed["pair_report_sha256"], hashlib.sha256(report.read_bytes()).hexdigest()
        )
        self.assertEqual(stat.S_IMODE(report.stat().st_mode), 0o400)
        self.assertEqual(
            stat.S_IMODE((Path(resumed["pair_state_path"])).stat().st_mode), 0o400
        )
        repeated = controller.run("P01-T2")
        self.assertEqual(repeated["run_id"], resumed["run_id"])
        self.assertEqual(repeated["pair_report_sha256"], resumed["pair_report_sha256"])

    def test_unsafe_workspace_is_quarantined_before_incident_sealing(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {
                "status": "admitted",
                "task_id": task_id,
                "condition_order": ["N", "L"],
            },
            controller,
        )

        def unsafe_condition(_self: PairController, **kwargs):
            condition = kwargs["condition"]
            self.assertEqual(condition, "N")
            condition_root = kwargs["pair_root"] / "conditions" / condition
            workspace = condition_root / "workspace"
            (workspace / "unreadable-file").write_bytes(b"sealed")
            (workspace / "unreadable-file").chmod(0)
            (workspace / "unreadable-directory").mkdir()
            (workspace / "unreadable-directory").chmod(0)
            (workspace / "outside-link").symlink_to(self.paper)
            os.mkfifo(workspace / "generated-fifo")
            with (workspace / "oversized-sparse").open("wb") as stream:
                stream.truncate(2 * 1024 * 1024 * 1024)
            result = {
                "schema_version": "formalization-condition-state-1",
                "task_id": "P01-T2",
                "condition": condition,
                "status": "RULE_VIOLATION",
                "active_seconds": 1.5,
                "contestant_usage": {
                    "input_tokens": 2,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 1,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 3,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "attempts": [{"attempt": 1}],
            }
            (condition_root / "condition_state.json").write_text(
                json.dumps(result), encoding="utf-8"
            )
            return result

        controller._run_condition = types.MethodType(unsafe_condition, controller)
        incident = controller.run("P01-T2")
        self.assertEqual(incident["status"], "PAIR_INCIDENT")
        self.assertEqual(incident["conditions"]["N"]["status"], "RULE_VIOLATION")
        condition_root = Path(incident["pair_root"]) / "conditions" / "N"
        replacement = condition_root / "workspace"
        self.assertTrue((replacement / "Candidate.lean").is_file())
        self.assertFalse(os.path.lexists(replacement / "outside-link"))
        records = list(condition_root.glob("workspace-quarantine-*.json"))
        self.assertEqual(len(records), 1)
        quarantine = json.loads(records[0].read_text(encoding="utf-8"))
        self.assertEqual(quarantine["status"], "quarantined")
        moved = Path(quarantine["quarantine_path"])
        self.assertTrue(os.path.lexists(moved / "outside-link"))
        self.assertTrue(os.path.lexists(moved / "generated-fifo"))
        self.assertEqual((moved / "oversized-sparse").stat().st_size, 2 * 1024**3)
        repeated = controller.run("P01-T2")
        self.assertEqual(repeated["pair_report_sha256"], incident["pair_report_sha256"])

    def test_submission_is_journaled_before_off_clock_validation(self) -> None:
        controller = self.controller()
        pair_root = self.root / "journal-pair"
        condition_root = pair_root / "conditions" / "N"
        condition_root.mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())

        class FakeDriver:
            def run_turn(fake_self, **kwargs):
                artifact_dir = kwargs["artifact_dir"]
                artifact_dir.mkdir(parents=True)
                for name in (
                    "turn.json",
                    "events.jsonl",
                    "stderr.log",
                    "prompt.md",
                    "last_message.txt",
                    "network_violations.bin",
                ):
                    (artifact_dir / name).write_bytes(b"{}\n" if name.endswith(".json") else b"")
                return types.SimpleNamespace(
                    exit_code=0,
                    timed_out=False,
                    active_started_perf_ns=1_000_000_000,
                    active_ended_perf_ns=2_000_000_000,
                    wall_seconds=1.0,
                    usage={
                        "input_tokens": 10,
                        "cached_input_tokens": 1,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 3,
                        "reasoning_output_tokens": 1,
                        "total_tokens": 13,
                    },
                    usage_complete=True,
                    thread_id="journal-thread",
                    failure_kind=None,
                )

            def assert_safe_control_surfaces(fake_self, workspace, **kwargs):
                return None

        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=KeyboardInterrupt("synthetic validation interruption"),
        ):
            with self.assertRaises(KeyboardInterrupt):
                controller._run_condition_impl(
                    pair_root=pair_root,
                    task_id="P01-T2",
                    condition="N",
                    paper_path=self.paper,
                    packet=packet,
                    driver=FakeDriver(),
                )

        state = json.loads(
            (condition_root / "condition_state.json").read_text(encoding="utf-8")
        )
        self.assertEqual(state["status"], "VALIDATING")
        self.assertEqual(len(state["attempts"]), 1)
        attempt = state["attempts"][0]
        self.assertEqual(attempt["status"], "SUBMISSION_FROZEN")
        self.assertEqual(attempt["journal_state"], "provisional")
        self.assertEqual(attempt["usage"]["total_tokens"], 13)
        candidate = Path(attempt["candidate"]["path"])
        self.assertTrue(candidate.is_file())
        self.assertEqual(
            hashlib.sha256(candidate.read_bytes()).hexdigest(),
            attempt["candidate"]["sha256"],
        )
        partial = controller._summarize_partial_condition(pair_root, "N", state)
        controller._verify_partial_condition(pair_root, partial)
        self.assertEqual(partial["submission_count"], 1)

    def test_turn_return_is_journaled_before_candidate_freeze(self) -> None:
        controller = self.controller()
        pair_root = self.root / "turn-return-pair"
        condition_root = pair_root / "conditions" / "N"
        condition_root.mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())

        class FakeDriver:
            def run_turn(fake_self, **kwargs):
                artifact_dir = kwargs["artifact_dir"]
                artifact_dir.mkdir(parents=True)
                for name in (
                    "turn.json",
                    "events.jsonl",
                    "stderr.log",
                    "prompt.md",
                    "last_message.txt",
                    "network_violations.bin",
                ):
                    (artifact_dir / name).write_bytes(
                        b'{"schema_version":3}\n' if name == "turn.json" else b""
                    )
                return types.SimpleNamespace(
                    exit_code=0,
                    timed_out=False,
                    active_started_perf_ns=1_000_000_000,
                    active_ended_perf_ns=2_500_000_000,
                    wall_seconds=2.0,
                    usage={
                        "input_tokens": 11,
                        "cached_input_tokens": 2,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 4,
                        "reasoning_output_tokens": 1,
                        "total_tokens": 15,
                    },
                    usage_complete=True,
                    thread_id="turn-return-thread",
                    failure_kind=None,
                )

            def assert_safe_control_surfaces(fake_self, workspace, **kwargs):
                return None

        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.freeze_candidate",
            side_effect=KeyboardInterrupt("synthetic freeze interruption"),
        ):
            with self.assertRaises(KeyboardInterrupt):
                controller._run_condition_impl(
                    pair_root=pair_root,
                    task_id="P01-T2",
                    condition="N",
                    paper_path=self.paper,
                    packet=packet,
                    driver=FakeDriver(),
                )

        state = json.loads(
            (condition_root / "condition_state.json").read_text(encoding="utf-8")
        )
        self.assertEqual(state["status"], "TURN_RETURNED")
        self.assertEqual(state["attempts"], [])
        self.assertEqual(state["active_seconds"], 1.5)
        self.assertEqual(state["contestant_usage"]["total_tokens"], 15)
        inflight = state["inflight_turn"]
        record = Path(inflight["turn_return_path"])
        self.assertTrue(record.is_file())
        self.assertEqual(sha256_file(record), inflight["turn_return_sha256"])
        partial = controller._summarize_partial_condition(pair_root, "N", state)
        controller._verify_partial_condition(pair_root, partial)
        self.assertEqual(partial["submission_count"], 0)


if __name__ == "__main__":
    unittest.main()
