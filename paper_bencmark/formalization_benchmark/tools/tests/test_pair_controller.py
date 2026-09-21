from __future__ import annotations

import hashlib
import json
import os
from dataclasses import replace
from pathlib import Path
import shutil
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
from codex_driver import TurnResult  # noqa: E402
from manifest_control import verify_manifest  # noqa: E402
from pair_controller import PairController  # noqa: E402
from pair_controller import _campaign_lock  # noqa: E402


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
                        "project_cleaned_before_cache_preparation": True,
                        "root_project_empty_immediately_before_measurement": True,
                        "post_clean_project_tree": {
                            "present": False,
                            "file_count": 0,
                            "bytes": 0,
                            "tree_sha256": "f" * 64,
                        },
                        "prebuild_project_tree": {
                            "present": False,
                            "file_count": 0,
                            "bytes": 0,
                            "tree_sha256": "f" * 64,
                        },
                        "dependency_cache_preparation": {
                            "logical_command": ["lake", "exe", "cache", "get"],
                            "returncode": 0,
                            "timed_out": False,
                            "output_limit_exceeded": False,
                            "resource_limit_exceeded": False,
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
        warm_root = (
            self.deployment.run_root
            / "warm-roots"
            / controller.manifest["manifest_payload_sha256"]
        )
        checkpoint = warm_root / "checkpoint"
        checkpoint.mkdir(parents=True, exist_ok=True)
        warm_record = warm_root / "warm-root.json"
        if not warm_record.exists():
            usage = {
                "input_tokens": 10,
                "cached_input_tokens": 2,
                "cache_write_input_tokens": 1,
                "output_tokens": 5,
                "reasoning_output_tokens": 2,
                "total_tokens": 15,
            }
            warm_record.write_text(
                json.dumps(
                    {
                        "schema_version": "formalization-warm-root-1",
                        "status": "READY",
                        "pilot_id": controller.config["pilot_id"],
                        "manifest_payload_sha256": controller.manifest[
                            "manifest_payload_sha256"
                        ],
                        "scout_prompt_sha256": sha256_file(
                            ROOT / "prompts" / "library_scout.md"
                        ),
                        "source_thread_id": "synthetic-scout-thread",
                        "source_last_turn_id": "synthetic-scout-turn",
                        "source_cumulative_usage": usage,
                        "scout_usage": usage,
                        "checkpoint_manifest": tree_manifest(checkpoint),
                    }
                ),
                encoding="utf-8",
            )
        packet_path = ROOT / "packets" / "P01-T2.json"
        packet = json.loads(packet_path.read_text(encoding="utf-8"))

        def fixture_inputs(_self: PairController, task_id: str):
            self.assertEqual(task_id, "P01-T2")
            return self.paper, packet_path, packet

        controller._paper_and_packet = types.MethodType(fixture_inputs, controller)

        def fake_provider_qualification(_self: PairController):
            record = self.root / "synthetic-provider-qualification.json"
            if not record.exists():
                record.write_text('{"status":"PASSED","charged_to_contestant":false}\n')
            return {
                "status": "PASSED",
                "record_path": str(record),
                "record_sha256": sha256_file(record),
            }

        controller._qualify_provider = types.MethodType(
            fake_provider_qualification, controller
        )
        return controller

    def test_warm_root_scout_runs_once_and_reuses_exact_checkpoint(self) -> None:
        controller = self.controller()
        warm_root, _record_path, _checkpoint = controller._warm_root_paths()
        shutil.rmtree(warm_root)
        controller.strict_hardware = True
        controller.config = {
            **controller.config,
            "warm_start": {
                **controller.config["warm_start"],
                "scout_runs_per_release": 1,
            },
        }
        controller.doctor = types.MethodType(
            lambda _self, _task_id: {"status": "PASSED"}, controller
        )
        calls: list[dict] = []

        class ScoutDriver:
            def __init__(_self, **kwargs):
                calls.append(kwargs)
                _self.state_root = Path(kwargs["state_root"])
                _self.state_root.mkdir(parents=True)
                (_self.state_root / "scout-state.json").write_text(
                    '{"thread":"scout-thread"}\n', encoding="utf-8"
                )

            def run_turn(_self, *, prompt, workspace, artifact_dir, timeout_seconds):
                self.assertIn("NumStability", prompt)
                self.assertFalse(calls[-1]["workspace_writable"])
                self.assertEqual(timeout_seconds, 18000.0)
                self.assertFalse(any(workspace.joinpath("source").glob("*")))
                artifact_dir.mkdir(parents=True)
                (artifact_dir / "turn.json").write_text(
                    json.dumps(
                        {
                            "terminal_status": "completed",
                            "turn_id": "scout-turn",
                            "active_seconds_through_quiescence": 12.5,
                        }
                    ),
                    encoding="utf-8",
                )
                (artifact_dir / "last_message.txt").write_text(
                    "scouting complete\n", encoding="utf-8"
                )
                usage = {
                    "input_tokens": 100,
                    "cached_input_tokens": 10,
                    "cache_write_input_tokens": 20,
                    "output_tokens": 30,
                    "reasoning_output_tokens": 15,
                    "total_tokens": 130,
                }
                return TurnResult(
                    thread_id="scout-thread",
                    exit_code=0,
                    timed_out=False,
                    wall_seconds=13.0,
                    usage=usage,
                    thread_cumulative_usage=usage,
                    usage_complete=True,
                    final_message="scouting complete",
                    event_count=1,
                    command=["codex", "app-server"],
                    active_started_perf_ns=1,
                    active_ended_perf_ns=2,
                    failure_kind=None,
                )

            def close(_self, *, artifact_dir):
                artifact_dir.mkdir(parents=True)

        with mock.patch("pair_controller.CodexDriver", ScoutDriver):
            first = controller.prepare_warm_root_when_idle()
            second = controller.prepare_warm_root_when_idle()

        self.assertEqual(len(calls), 1)
        self.assertEqual(first, second)
        self.assertEqual(first["status"], "READY")
        self.assertEqual(first["source_thread_id"], "scout-thread")
        self.assertFalse(first["benchmark_charged"])
        self.assertEqual(
            first["checkpoint_manifest"], tree_manifest(warm_root / "checkpoint")
        )

    def test_pilot12_refuses_a_replacement_scout_when_inherited_root_is_missing(self) -> None:
        controller = self.controller()
        warm_root, _record_path, _checkpoint = controller._warm_root_paths()
        shutil.rmtree(warm_root)
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, _task_id: {"status": "PASSED"}, controller
        )
        with self.assertRaisesRegex(BenchmarkError, "forbids a replacement scouting turn"):
            controller.prepare_warm_root_when_idle()

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

    @staticmethod
    def successful_driver(
        model_active_seconds: float | list[float], timeouts: list[float]
    ):
        active_durations = (
            [float(value) for value in model_active_seconds]
            if isinstance(model_active_seconds, list)
            else [float(model_active_seconds)]
        )
        turn_index = 0

        class FakeDriver:
            def run_turn(fake_self, **kwargs):
                nonlocal turn_index
                if turn_index >= len(active_durations):
                    raise AssertionError("unexpected extra formalizer turn")
                active_duration = active_durations[turn_index]
                turn_index += 1
                timeouts.append(float(kwargs["timeout_seconds"]))
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
                        b'{}\n' if name == "turn.json" else b""
                    )
                active_started = 1_000_000_000
                return types.SimpleNamespace(
                    exit_code=0,
                    timed_out=False,
                    active_started_perf_ns=active_started,
                    active_ended_perf_ns=(
                        active_started + int(active_duration * 1_000_000_000)
                    ),
                    wall_seconds=active_duration,
                    usage={
                        "input_tokens": 10,
                        "cached_input_tokens": 1,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 3,
                        "reasoning_output_tokens": 1,
                        "total_tokens": 13,
                    },
                    usage_complete=True,
                    thread_id="active-limit-thread",
                    failure_kind=None,
                )

            def assert_safe_control_surfaces(fake_self, workspace, **kwargs):
                return None

        return FakeDriver()

    def test_release_manifest_and_provider_free_pair_staging(self) -> None:
        manifest, config = verify_manifest()
        self.assertEqual(manifest["task_ids"], config["task_ids"])
        controller = self.controller()
        first = controller.run("P01-T2", dry_run=True)
        self.assertEqual(first["status"], "DRY_RUN_COMPLETE")
        self.assertTrue(first["contestant_active_time_complete"])
        self.assertEqual(first["contestant_active_time_interpretation"], "exact")
        self.assertEqual(first["condition_order"], ["N", "L"])
        pair_root = Path(first["pair_root"])
        n_prompt = (pair_root / "conditions" / "N" / "prompt.txt").read_bytes()
        l_prompt = (pair_root / "conditions" / "L" / "prompt.txt").read_bytes()
        common = (ROOT / "prompts" / "formalizer.md").read_bytes()
        self.assertEqual(n_prompt, common)
        self.assertEqual(l_prompt, common)
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

    def test_global_campaign_lock_serializes_releases_and_eleven_predecessors(self) -> None:
        registry = self.root / "account-registry"
        predecessor = self.root / "pilot-7-runs"
        legacy_predecessor = self.root / "pilot-5-runs"
        ancestral_predecessor = self.root / "pilot-4-runs"
        great_ancestral_predecessor = self.root / "pilot-3-runs"
        fifth_ancestral_predecessor = self.root / "pilot-2-runs"
        sixth_ancestral_predecessor = self.root / "pilot-1-runs"
        seventh_ancestral_predecessor = self.root / "pilot-0-runs"
        eighth_ancestral_predecessor = self.root / "pilot-minus-1-runs"
        ninth_ancestral_predecessor = self.root / "pilot-minus-2-runs"
        tenth_ancestral_predecessor = self.root / "pilot-minus-3-runs"
        eleventh_ancestral_predecessor = self.root / "pilot-minus-4-runs"
        with _campaign_lock(
            self.deployment.run_root, registry, predecessor, legacy_predecessor,
            ancestral_predecessor, great_ancestral_predecessor, fifth_ancestral_predecessor,
            sixth_ancestral_predecessor, seventh_ancestral_predecessor,
            eighth_ancestral_predecessor,
            ninth_ancestral_predecessor,
            tenth_ancestral_predecessor,
            eleventh_ancestral_predecessor,
        ):
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", registry):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, legacy_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, great_ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, fifth_ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, sixth_ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, seventh_ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, eighth_ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(self.root / "another-release", None, ninth_ancestral_predecessor):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(
                    self.root / "another-release", None, None, None, None, None,
                    None, None, None, None, None, tenth_ancestral_predecessor,
                ):
                    pass
            with self.assertRaisesRegex(BenchmarkError, "already active"):
                with _campaign_lock(
                    self.root / "another-release", None, None, None, None, None,
                    None, None, None, None, None, None,
                    eleventh_ancestral_predecessor,
                ):
                    pass

    def test_official_pair_rejects_downgraded_qualification_binding(self) -> None:
        from provider_capability_canary import ROLES, SCHEMA, WARM_FORK_ROLE

        controller = object.__new__(PairController)
        controller.deployment = replace(
            self.deployment, global_registry_root=self.root / "registry"
        )
        controller.manifest = {}
        controller.config = {}
        roles = {role[0] for role in ROLES}
        identity = {
            "roles": {
                role: {
                    "model": "fixture-model",
                    "reasoning_effort": "high",
                    "output_schema_sha256": "a" * 64,
                }
                for role in roles
            },
            "warm_fork": {
                "role": WARM_FORK_ROLE,
                "model": "fixture-model",
                "reasoning_effort": "high",
                "output_schema_sha256": "a" * 64,
            },
        }
        qualification_root = (
            self.deployment.run_root / "qualifications"
            / sha256_file(ROOT / "manifest.json")
        )
        roles_root = qualification_root / "roles"
        roles_root.mkdir(parents=True)
        (roles_root / "fixture.txt").write_text("role artifacts\n", encoding="utf-8")
        record_path = qualification_root / "qualification.json"
        record = {
            "schema_version": SCHEMA,
            "status": "PASSED",
            "identity": identity,
            "provider_turns": len(ROLES) + 1,
            "role_outcomes": {
                **{role: dict(identity["roles"][role]) for role in roles},
                WARM_FORK_ROLE: dict(identity["warm_fork"]),
            },
            "charged_to_contestant": False,
            "roles_manifest": tree_manifest(roles_root),
        }

        def verify(candidate: dict[str, object]) -> None:
            record_path.write_text(json.dumps(candidate), encoding="utf-8")
            binding = {
                "provider_qualification": {
                    "record_path": str(record_path),
                    "record_sha256": sha256_file(record_path),
                    "charged_to_contestant": False,
                }
            }
            with mock.patch(
                "provider_capability_canary.qualification_identity",
                return_value=identity,
            ):
                controller._verify_qualification_binding(binding)

        verify(record)
        with self.assertRaisesRegex(BenchmarkError, "evidence changed"):
            verify({**record, "schema_version": "formalization-provider-qualification-1"})
        with self.assertRaisesRegex(BenchmarkError, "evidence changed"):
            verify({**record, "role_outcomes": {}})
        bad_outcomes = {name: dict(value) for name, value in record["role_outcomes"].items()}
        bad_outcomes["audit-schema-blind-translation"]["output_schema_sha256"] = "b" * 64
        with self.assertRaisesRegex(BenchmarkError, "role evidence changed"):
            verify({**record, "role_outcomes": bad_outcomes})

    def test_account_global_reservation_prevents_a_second_local_pair(self) -> None:
        controller = self.controller()
        registry = self.root / "account-registry"
        controller.deployment = replace(
            controller.deployment, global_registry_root=registry
        )
        index = controller._registry_index_path("P01-T2")
        self.assertIsNotNone(index)
        index.parent.mkdir(parents=True)
        index.write_text('{"pilot_id":"reserved"}\n', encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkError, "already reserved"):
            controller.status("P01-T2")

    def test_failed_provider_qualification_consumes_no_official_pair_slot(self) -> None:
        controller = self.controller()
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {"task_id": task_id, "condition_order": ["N", "L"]},
            controller,
        )

        def incompatible_provider(_self):
            raise BenchmarkError("provider capability incompatibility")

        controller._qualify_provider = types.MethodType(
            incompatible_provider, controller
        )
        with self.assertRaisesRegex(BenchmarkError, "provider capability"):
            controller.run("P01-T2")
        self.assertFalse((self.deployment.run_root / "pairs").exists())
        self.assertFalse((self.deployment.run_root / "index").exists())

    def test_torn_global_reservation_recovers_the_same_pair(self) -> None:
        controller = self.controller()
        controller.deployment = replace(
            controller.deployment, global_registry_root=self.root / "account-registry"
        )
        controller.strict_hardware = True
        controller.doctor = types.MethodType(
            lambda _self, task_id: {"task_id": task_id, "condition_order": ["N", "L"]},
            controller,
        )
        controller._verify_qualification_binding = types.MethodType(
            lambda _self, admission: None, controller
        )

        def interrupted_after_index(_self, **kwargs):
            raise KeyboardInterrupt("synthetic crash after global reservation")

        controller._continue_pair = types.MethodType(
            interrupted_after_index, controller
        )
        with self.assertRaises(KeyboardInterrupt):
            controller.run("P01-T2")
        index_path = controller._index_path("P01-T2")
        registry_path = controller._registry_index_path("P01-T2")
        self.assertIsNotNone(registry_path)
        expected = json.loads(registry_path.read_text(encoding="utf-8"))
        index_path.unlink()  # Simulate a crash between the two index writes.
        with self.assertRaisesRegex(BenchmarkError, "already reserved"):
            controller.status("P01-T2")

        def recovered_pair(_self, **kwargs):
            return kwargs["pair_state"]

        controller._continue_pair = types.MethodType(recovered_pair, controller)
        resumed = controller.run("P01-T2")
        self.assertEqual(resumed["run_id"], expected["run_id"])
        self.assertEqual(json.loads(index_path.read_text(encoding="utf-8")), expected)
        self.assertEqual(json.loads(registry_path.read_text(encoding="utf-8")), expected)
        self.assertEqual(len(list((self.deployment.run_root / "pairs").iterdir())), 1)

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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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
        self.assertTrue(completed["contestant_active_time_complete"])
        self.assertEqual(completed["contestant_active_time_interpretation"], "exact")
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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
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

    def test_final_candidate_freeze_overshoot_is_measured_and_unscored(self) -> None:
        controller = self.controller()
        controller.config["contestant_active_time_limit_seconds"] = 2
        pair_root = self.root / "freeze-overshoot-pair"
        (pair_root / "conditions" / "N").mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        timeouts: list[float] = []
        driver = self.successful_driver(1.9, timeouts)
        import pair_controller as pair_module

        real_freeze = pair_module.freeze_candidate
        clock_ns = [10_000_000_000]

        def freeze_with_elapsed_time(*args, **kwargs):
            frozen = real_freeze(*args, **kwargs)
            clock_ns[0] += 200_000_000
            return frozen

        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.time.perf_counter_ns", side_effect=lambda: clock_ns[0]
        ), mock.patch(
            "pair_controller.freeze_candidate", side_effect=freeze_with_elapsed_time
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=AssertionError("over-limit submission must not be validated"),
        ):
            state = controller._run_condition_impl(
                pair_root=pair_root,
                task_id="P01-T2",
                condition="N",
                paper_path=self.paper,
                packet=packet,
                driver=driver,
            )

        self.assertEqual(timeouts, [2.0])
        self.assertEqual(state["status"], "ACTIVE_TIME_LIMIT")
        self.assertAlmostEqual(state["active_seconds"], 2.1)
        self.assertEqual(state["active_time_limit_threshold_seconds"], 2.0)
        self.assertAlmostEqual(state["active_time_limit_overshoot_seconds"], 0.1)
        self.assertEqual(len(state["attempts"]), 1)
        attempt = state["attempts"][0]
        self.assertEqual(attempt["status"], "ACTIVE_TIME_LIMIT")
        self.assertAlmostEqual(attempt["model_active_seconds"], 1.9)
        self.assertAlmostEqual(attempt["candidate_freeze_seconds"], 0.2)
        self.assertAlmostEqual(attempt["active_seconds_cumulative"], 2.1)
        self.assertAlmostEqual(attempt["active_time_limit_overshoot_seconds"], 0.1)
        candidate = Path(attempt["candidate"]["path"])
        self.assertTrue(candidate.is_file())
        self.assertEqual(sha256_file(candidate), attempt["candidate"]["sha256"])
        controller._verify_condition_active_time_contract(state)
        condition_root = pair_root / "conditions" / "N"
        self.write_fake_shutdown(condition_root)
        summary = controller._summarize_condition(pair_root, "N", state)
        controller._verify_condition_summary(pair_root, "N", summary)

    def test_rule_violation_takes_precedence_over_freeze_overshoot(self) -> None:
        controller = self.controller()
        controller.config["contestant_active_time_limit_seconds"] = 2
        pair_root = self.root / "violation-and-freeze-overshoot-pair"
        (pair_root / "conditions" / "N").mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        timeouts: list[float] = []
        driver = self.successful_driver(1.9, timeouts)
        import pair_controller as pair_module

        def unsafe_control_surface(fake_self, workspace, **kwargs):
            raise BenchmarkError("synthetic protected-path mutation")

        driver.assert_safe_control_surfaces = types.MethodType(
            unsafe_control_surface, driver
        )
        real_freeze = pair_module.freeze_candidate
        clock_ns = [15_000_000_000]

        def freeze_with_elapsed_time(*args, **kwargs):
            frozen = real_freeze(*args, **kwargs)
            clock_ns[0] += 200_000_000
            return frozen

        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.time.perf_counter_ns", side_effect=lambda: clock_ns[0]
        ), mock.patch(
            "pair_controller.freeze_candidate", side_effect=freeze_with_elapsed_time
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=AssertionError("rule-violating submission must not be validated"),
        ):
            state = controller._run_condition_impl(
                pair_root=pair_root,
                task_id="P01-T2",
                condition="N",
                paper_path=self.paper,
                packet=packet,
                driver=driver,
            )

        self.assertEqual(timeouts, [2.0])
        self.assertEqual(state["status"], "RULE_VIOLATION")
        self.assertAlmostEqual(state["active_seconds"], 2.1)
        self.assertEqual(len(state["attempts"]), 1)
        attempt = state["attempts"][0]
        self.assertEqual(attempt["status"], "RULE_VIOLATION")
        self.assertAlmostEqual(attempt["active_seconds"], 2.1)
        self.assertEqual(
            attempt["control_surface_violation"],
            "synthetic protected-path mutation",
        )
        self.assertNotIn("active_time_limit_overshoot_seconds", state)
        controller._verify_condition_active_time_contract(state)
        summary = controller._summarize_condition(pair_root, "N", state)
        controller._verify_condition_summary(pair_root, "N", summary)

    def test_provider_capability_failure_precedes_secondary_rule_markers(self) -> None:
        controller = self.controller()
        pair_root = self.root / "provider-capability-incident-pair"
        (pair_root / "conditions" / "N").mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        driver = self.successful_driver(0.25, [])
        original_run = driver.run_turn

        def incompatible_turn(**kwargs):
            result = original_run(**kwargs)
            (kwargs["artifact_dir"] / "network_violations.bin").write_bytes(
                b"secondary blocked network attempt"
            )
            result.failure_kind = "provider_capability_violation"
            result.exit_code = 1
            result.usage_complete = False
            return result

        def unsafe_control_surface(fake_self, workspace, **kwargs):
            raise BenchmarkError("secondary protected-path mutation")

        driver.run_turn = incompatible_turn
        driver.assert_safe_control_surfaces = types.MethodType(
            unsafe_control_surface, driver
        )
        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.freeze_candidate",
            side_effect=AssertionError("capability incident must not freeze"),
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=AssertionError("capability incident must not validate"),
        ):
            state = controller._run_condition_impl(
                pair_root=pair_root,
                task_id="P01-T2",
                condition="N",
                paper_path=self.paper,
                packet=packet,
                driver=driver,
            )
        self.assertEqual(state["status"], "INFRASTRUCTURE_FAILURE")
        self.assertEqual(len(state["attempts"]), 1)
        attempt = state["attempts"][0]
        self.assertEqual(attempt["status"], "INFRASTRUCTURE_FAILURE")
        self.assertEqual(
            attempt["incident_classification"],
            "provider_capability_incompatibility",
        )
        self.assertEqual(
            attempt["control_surface_violation"],
            "secondary protected-path mutation",
        )
        self.assertIsNone(attempt["candidate"])
        self.assertFalse(attempt["usage_complete"])

    def test_active_timeout_takes_precedence_over_invalid_final_telemetry(self) -> None:
        controller = self.controller()
        controller.config["contestant_active_time_limit_seconds"] = 2
        pair_root = self.root / "timeout-with-invalid-telemetry-pair"
        (pair_root / "conditions" / "N").mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        timeouts: list[float] = []
        driver = self.successful_driver(1.9, timeouts)
        successful_turn = driver.run_turn

        def timed_out_turn(**kwargs):
            result = successful_turn(**kwargs)
            result.timed_out = True
            result.failure_kind = "telemetry_invalid"
            result.usage_complete = False
            return result

        driver.run_turn = timed_out_turn
        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=AssertionError("timed-out turn must not be validated"),
        ):
            state = controller._run_condition_impl(
                pair_root=pair_root,
                task_id="P01-T2",
                condition="N",
                paper_path=self.paper,
                packet=packet,
                driver=driver,
            )

        self.assertEqual(timeouts, [2.0])
        self.assertEqual(state["status"], "ACTIVE_TIME_LIMIT")
        self.assertAlmostEqual(state["active_seconds"], 1.9)
        self.assertEqual(state["active_time_limit_threshold_seconds"], 2.0)
        self.assertEqual(state["active_time_limit_overshoot_seconds"], 0.0)
        self.assertFalse(state["contestant_usage_complete"])
        self.assertEqual(state["contestant_usage_interpretation"], "observed lower bound")
        self.assertEqual(len(state["attempts"]), 1)
        attempt = state["attempts"][0]
        self.assertEqual(attempt["status"], "ACTIVE_TIME_LIMIT")
        self.assertEqual(attempt["formalizer_failure_kind"], "telemetry_invalid")
        self.assertEqual(attempt["usage_interpretation"], "incomplete lower bound")

    def test_exact_active_time_limit_submission_reaches_off_clock_validation(self) -> None:
        controller = self.controller()
        controller.config["contestant_active_time_limit_seconds"] = 2
        pair_root = self.root / "exact-limit-pair"
        condition_root = pair_root / "conditions" / "N"
        condition_root.mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        timeouts: list[float] = []
        driver = self.successful_driver(1.8, timeouts)
        import pair_controller as pair_module

        real_freeze = pair_module.freeze_candidate
        clock_ns = [20_000_000_000]

        def freeze_at_boundary(*args, **kwargs):
            frozen = real_freeze(*args, **kwargs)
            clock_ns[0] += 200_000_000
            return frozen

        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.time.perf_counter_ns", side_effect=lambda: clock_ns[0]
        ), mock.patch(
            "pair_controller.freeze_candidate", side_effect=freeze_at_boundary
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=KeyboardInterrupt("synthetic off-clock validation stop"),
        ):
            with self.assertRaises(KeyboardInterrupt):
                controller._run_condition_impl(
                    pair_root=pair_root,
                    task_id="P01-T2",
                    condition="N",
                    paper_path=self.paper,
                    packet=packet,
                    driver=driver,
                )

        state = json.loads(
            (condition_root / "condition_state.json").read_text(encoding="utf-8")
        )
        self.assertEqual(timeouts, [2.0])
        self.assertEqual(state["status"], "VALIDATING")
        self.assertEqual(state["active_seconds"], 2.0)
        self.assertEqual(state["attempts"][0]["status"], "SUBMISSION_FROZEN")
        self.assertEqual(state["attempts"][0]["active_seconds_cumulative"], 2.0)

    def test_freeze_overshoot_uses_time_accumulated_across_repairs(self) -> None:
        controller = self.controller()
        controller.config["contestant_active_time_limit_seconds"] = 2
        pair_root = self.root / "cumulative-freeze-overshoot-pair"
        (pair_root / "conditions" / "N").mkdir(parents=True)
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        timeouts: list[float] = []
        driver = self.successful_driver([1.0, 0.8], timeouts)
        import pair_controller as pair_module

        real_freeze = pair_module.freeze_candidate
        clock_ns = [30_000_000_000]
        freeze_count = 0

        def two_freezes(*args, **kwargs):
            nonlocal freeze_count
            freeze_count += 1
            if freeze_count == 1:
                clock_ns[0] += 100_000_000
                raise BenchmarkError("synthetic missing first candidate")
            frozen = real_freeze(*args, **kwargs)
            clock_ns[0] += 200_000_000
            return frozen

        with mock.patch(
            "pair_controller.snapshot_hardware", return_value={"synthetic": True}
        ), mock.patch(
            "pair_controller.time.perf_counter_ns", side_effect=lambda: clock_ns[0]
        ), mock.patch(
            "pair_controller.freeze_candidate", side_effect=two_freezes
        ), mock.patch(
            "pair_controller.validate_candidate",
            side_effect=AssertionError("over-limit submission must not be validated"),
        ):
            state = controller._run_condition_impl(
                pair_root=pair_root,
                task_id="P01-T2",
                condition="N",
                paper_path=self.paper,
                packet=packet,
                driver=driver,
            )

        self.assertEqual(len(timeouts), 2)
        self.assertAlmostEqual(timeouts[0], 2.0)
        self.assertAlmostEqual(timeouts[1], 0.9)
        self.assertEqual(state["status"], "ACTIVE_TIME_LIMIT")
        self.assertAlmostEqual(state["active_seconds"], 2.1)
        self.assertAlmostEqual(state["active_time_limit_overshoot_seconds"], 0.1)
        self.assertEqual(
            [attempt["status"] for attempt in state["attempts"]],
            ["CANDIDATE_MISSING", "ACTIVE_TIME_LIMIT"],
        )
        self.assertAlmostEqual(state["attempts"][0]["active_seconds"], 1.1)
        self.assertAlmostEqual(state["attempts"][1]["active_seconds"], 1.0)
        self.assertAlmostEqual(
            state["attempts"][1]["active_seconds_cumulative"], 2.1
        )

    def test_condition_summary_rejects_accepted_result_over_active_limit(self) -> None:
        controller = self.controller()
        controller.config["contestant_active_time_limit_seconds"] = 2
        pair_root = self.root / "over-limit-summary-pair"
        condition_root = pair_root / "conditions" / "N"
        condition_root.mkdir(parents=True)
        state = {
            "schema_version": "formalization-condition-state-1",
            "task_id": "P01-T2",
            "condition": "N",
            "status": "ACCEPTED_FAITHFUL",
            "active_seconds": 2.1,
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
            "contestant_active_time_complete": True,
            "contestant_active_time_interpretation": "exact",
            "attempts": [],
        }
        state_path = condition_root / "condition_state.json"
        state_path.write_text(json.dumps(state), encoding="utf-8")
        self.write_fake_shutdown(condition_root)
        summary = controller._summarize_condition(pair_root, "N", state)
        with self.assertRaisesRegex(
            BenchmarkError, "exceeded the cumulative active-time limit"
        ):
            controller._verify_condition_summary(pair_root, "N", summary)

    def test_interrupted_active_turn_without_safe_record_marks_measurements_incomplete(
        self,
    ) -> None:
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        for record_kind in ("missing", "symlink", "malformed"):
            with self.subTest(record_kind=record_kind):
                controller = self.controller()
                pair_root = self.root / f"active-turn-{record_kind}-pair"
                condition_root = pair_root / "conditions" / "N"
                condition_root.mkdir(parents=True)
                controller._stage_condition(
                    task_id="P01-T2",
                    condition="N",
                    condition_root=condition_root,
                    paper_path=self.paper,
                    packet=packet,
                )
                formalizer_root = condition_root / "attempts" / "01" / "formalizer"
                formalizer_root.mkdir(parents=True)
                turn_path = formalizer_root / "turn.json"
                if record_kind == "symlink":
                    symlink_target = formalizer_root / "turn-target.json"
                    symlink_target.write_text("{}\n", encoding="utf-8")
                    turn_path.symlink_to(symlink_target.name)
                elif record_kind == "malformed":
                    turn_path.write_text("{not-json", encoding="utf-8")
                state_path = condition_root / "condition_state.json"
                state_path.write_text(
                    json.dumps(
                        {
                            "schema_version": "formalization-condition-state-1",
                            "task_id": "P01-T2",
                            "condition": "N",
                            "status": "CONTESTANT_ACTIVE",
                            "thread_id": None,
                            "active_seconds": 1.25,
                            "attempt_wall_seconds": 0.0,
                            "excluded_wall_seconds": 0.0,
                            "contestant_usage": {
                                "input_tokens": 4,
                                "cached_input_tokens": 1,
                                "cache_write_input_tokens": 0,
                                "output_tokens": 2,
                                "reasoning_output_tokens": 0,
                                "total_tokens": 6,
                            },
                            "contestant_usage_complete": True,
                            "contestant_usage_interpretation": "exact",
                            "contestant_active_time_complete": True,
                            "contestant_active_time_interpretation": "exact",
                            "attempts": [],
                        }
                    ),
                    encoding="utf-8",
                )

                with self.assertRaisesRegex(
                    BenchmarkError, "interrupted formalizer turn"
                ):
                    controller._run_condition_impl(
                        pair_root=pair_root,
                        task_id="P01-T2",
                        condition="N",
                        paper_path=self.paper,
                        packet=packet,
                        driver=object(),
                    )

                state = json.loads(state_path.read_text(encoding="utf-8"))
                self.assertEqual(state["active_seconds"], 1.25)
                self.assertEqual(state["contestant_usage"]["total_tokens"], 6)
                self.assertFalse(state["contestant_usage_complete"])
                self.assertEqual(
                    state["contestant_usage_interpretation"],
                    "observed lower bound",
                )
                self.assertFalse(state["contestant_active_time_complete"])
                self.assertEqual(
                    state["contestant_active_time_interpretation"],
                    "observed lower bound",
                )
                partial = controller._summarize_partial_condition(
                    pair_root, "N", state
                )
                controller._verify_partial_condition(pair_root, partial)
                self.assertFalse(partial["contestant_active_time_complete"])

    def test_freeze_journal_gap_preserves_usage_and_seals_active_lower_bound(
        self,
    ) -> None:
        controller = self.controller()
        packet = json.loads((ROOT / "packets" / "P01-T2.json").read_text())
        pair_root = self.root / "freeze-journal-gap-pair"
        condition_root = pair_root / "conditions" / "N"
        condition_root.mkdir(parents=True)
        controller._stage_condition(
            task_id="P01-T2",
            condition="N",
            condition_root=condition_root,
            paper_path=self.paper,
            packet=packet,
        )
        turn_return_path = condition_root / "attempts" / "01" / "turn-return.json"
        turn_return_path.parent.mkdir(parents=True)
        turn_return_path.write_text('{"returned":true}\n', encoding="utf-8")
        state_path = condition_root / "condition_state.json"
        state_path.write_text(
            json.dumps(
                {
                    "schema_version": "formalization-condition-state-1",
                    "task_id": "P01-T2",
                    "condition": "N",
                    "status": "TURN_RETURNED",
                    "thread_id": "freeze-gap-thread",
                    "active_seconds": 1.5,
                    "attempt_wall_seconds": 0.0,
                    "excluded_wall_seconds": 0.0,
                    "contestant_usage": {
                        "input_tokens": 8,
                        "cached_input_tokens": 2,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 3,
                        "reasoning_output_tokens": 1,
                        "total_tokens": 12,
                    },
                    "contestant_usage_complete": True,
                    "contestant_usage_interpretation": "exact",
                    "contestant_active_time_complete": True,
                    "contestant_active_time_interpretation": "exact",
                    "attempts": [],
                    "inflight_turn": {
                        "attempt": 1,
                        "turn_return_path": str(turn_return_path),
                        "turn_return_sha256": sha256_file(turn_return_path),
                        "model_active_seconds": 1.5,
                        "usage_complete": True,
                    },
                }
            ),
            encoding="utf-8",
        )

        with self.assertRaisesRegex(BenchmarkError, "outside a resumable boundary"):
            controller._run_condition_impl(
                pair_root=pair_root,
                task_id="P01-T2",
                condition="N",
                paper_path=self.paper,
                packet=packet,
                driver=object(),
            )

        state = json.loads(state_path.read_text(encoding="utf-8"))
        self.assertTrue(state["contestant_usage_complete"])
        self.assertEqual(state["contestant_usage_interpretation"], "exact")
        self.assertFalse(state["contestant_active_time_complete"])
        self.assertEqual(
            state["contestant_active_time_interpretation"],
            "observed lower bound",
        )
        partial = controller._summarize_partial_condition(pair_root, "N", state)
        controller._verify_partial_condition(pair_root, partial)

        admission_path = pair_root / "admission.json"
        admission_path.write_text("{}\n", encoding="utf-8")
        pair_state_path = pair_root / "pair_state.json"
        pair_state = {
            "schema_version": "formalization-pair-state-1",
            "pilot_id": controller.config["pilot_id"],
            "run_id": "freeze-gap-run",
            "task_id": "P01-T2",
            "created_at_utc": "2026-01-01T00:00:00Z",
            "created_unix_ns": 1,
            "pair_root": str(pair_root),
            "pair_state_path": str(pair_state_path),
            "status": "PAIR_INCIDENT",
            "condition_order": ["N", "L"],
            "conditions": {},
            "partial_condition_evidence": partial,
            "manifest_sha256": sha256_file(ROOT / "manifest.json"),
            "admission_sha256": sha256_file(admission_path),
            "dry_run": False,
            "strict_hardware_enforced": True,
            "measurement_admissible": True,
            "incident": {
                "condition": "N",
                "classification": "synthetic_freeze_journal_gap",
                "message": "Synthetic hard kill before freeze duration journaling.",
                "recorded_at_utc": "2026-01-01T00:00:01Z",
            },
        }
        pair_state_path.write_text(json.dumps(pair_state), encoding="utf-8")
        sealed = controller._seal_pair_terminal(
            pair_root=pair_root,
            pair_state_path=pair_state_path,
            pair_state=pair_state,
        )
        self.assertEqual(sealed["contestant_active_seconds_total"], 1.5)
        self.assertFalse(sealed["contestant_active_time_complete"])
        self.assertEqual(
            sealed["contestant_active_time_interpretation"],
            "observed lower bound",
        )
        controller._verify_pair_report(
            pair_root / "pair_report.json",
            sealed,
            expected_sha256=sealed["pair_report_sha256"],
        )

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

    def test_turn_return_and_freeze_time_are_journaled_when_freeze_is_interrupted(self) -> None:
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
            "pair_controller.time.perf_counter_ns",
            side_effect=[5_000_000_000, 6_000_000_000, 6_250_000_000],
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
        self.assertEqual(state["active_seconds"], 1.75)
        self.assertTrue(state["contestant_active_time_complete"])
        self.assertEqual(state["contestant_active_time_interpretation"], "exact")
        self.assertEqual(state["contestant_usage"]["total_tokens"], 15)
        inflight = state["inflight_turn"]
        self.assertEqual(inflight["candidate_freeze_seconds"], 0.25)
        self.assertIsNone(inflight["candidate"])
        record = Path(inflight["turn_return_path"])
        self.assertTrue(record.is_file())
        self.assertEqual(sha256_file(record), inflight["turn_return_sha256"])
        partial = controller._summarize_partial_condition(pair_root, "N", state)
        controller._verify_partial_condition(pair_root, partial)
        self.assertEqual(partial["submission_count"], 0)


if __name__ == "__main__":
    unittest.main()
