from __future__ import annotations

import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file, tree_manifest  # noqa: E402
from setup_titan import (  # noqa: E402
    INSTALL_TRANSACTION,
    LEGACY_INCIDENT_RUN_ID,
    LEGACY_MANIFEST_PAYLOAD_SHA256,
    LEGACY_RELEASE_COMMIT,
    PREDECESSOR_INCIDENT_RUN_ID,
    PREDECESSOR_MANIFEST_PAYLOAD_SHA256,
    PREDECESSOR_RELEASE_COMMIT,
    PILOT3_INCIDENT_RUN_ID,
    PILOT3_MANIFEST_PAYLOAD_SHA256,
    PILOT3_RELEASE_COMMIT,
    _load_transaction,
    _remove_skill_transaction_tree,
    _transaction_record,
    directory_identity,
    install,
    install_skill_atomically,
    isolated_runner_command,
    measured_build_command,
    measured_build_service_environment,
    private_provisioning_environment,
    make_parser,
    pilot2_lineage,
    predecessor_lineage,
    verify_predecessor_lineage,
    remove_owned_deployment_root,
    run_command_sandbox_canary,
    write_launcher,
)


class SkillInstallTests(unittest.TestCase):
    def test_pilot4_launcher_defaults_are_distinct_and_predecessor_is_required(self) -> None:
        parser = make_parser()
        with self.assertRaises(SystemExit):
            parser.parse_args(["--pdf-source-dir", "/tmp"])
        parsed = parser.parse_args(
            ["--pdf-source-dir", "/tmp", "--predecessor-deployment-root", "/tmp/old"]
        )
        self.assertTrue(parsed.deployment_root.endswith("highambench-formalization-pilot-4-r1"))
        self.assertTrue(parsed.launcher.endswith("run-highambench-formalization-pilot-4-r1"))

    def test_pilot2_incident_and_legacy_lock_are_read_only_and_hash_bound(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = (Path(temporary) / "deployment").resolve()
            legacy_root = (Path(temporary) / "pilot-1-deployment").resolve()
            legacy_run_root = legacy_root / "runs"
            legacy_manifest = (
                legacy_root / "release" / "paper_bencmark"
                / "formalization_benchmark" / "manifest.json"
            )
            legacy_manifest.parent.mkdir(parents=True)
            legacy_manifest.write_text(
                json.dumps({
                    "pilot_id": "formalization-benchmark-t2-pilot-1",
                    "manifest_payload_sha256": LEGACY_MANIFEST_PAYLOAD_SHA256,
                }),
                encoding="utf-8",
            )
            legacy_pair_root = legacy_run_root / "pairs" / LEGACY_INCIDENT_RUN_ID
            legacy_pair_root.mkdir(parents=True)
            legacy_report = legacy_pair_root / "pair_report.json"
            legacy_state = legacy_pair_root / "pair_state.json"
            legacy_report.write_text(
                json.dumps({
                    "pilot_id": "formalization-benchmark-t2-pilot-1",
                    "task_id": "P01-T2",
                    "status": "PAIR_INCIDENT",
                    "run_id": LEGACY_INCIDENT_RUN_ID,
                    "manifest_sha256": sha256_file(legacy_manifest),
                    "pair_root": str(legacy_pair_root),
                    "pair_state_path": str(legacy_state),
                }),
                encoding="utf-8",
            )
            legacy_state.write_text(
                json.dumps({
                    "status": "PAIR_INCIDENT",
                    "run_id": LEGACY_INCIDENT_RUN_ID,
                    "pair_root": str(legacy_pair_root),
                    "pair_state_path": str(legacy_state),
                    "pair_report_sha256": sha256_file(legacy_report),
                }),
                encoding="utf-8",
            )
            legacy_index = legacy_run_root / "index" / "P01-T2.json"
            legacy_index.parent.mkdir()
            legacy_index.write_text(
                json.dumps({
                    "task_id": "P01-T2",
                    "run_id": LEGACY_INCIDENT_RUN_ID,
                    "pair_root": str(legacy_pair_root),
                    "pair_state_path": str(legacy_state),
                }),
                encoding="utf-8",
            )
            legacy_deployment = legacy_root / "deployment.json"
            legacy_deployment.write_text(
                json.dumps({
                    "schema_version": "formalization-deployment-1",
                    "release_commit": LEGACY_RELEASE_COMMIT,
                    "release_manifest_sha256": sha256_file(legacy_manifest),
                    "run_root": str(legacy_run_root),
                }),
                encoding="utf-8",
            )
            manifest = (
                root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
            )
            manifest.parent.mkdir(parents=True)
            manifest.write_text(
                json.dumps(
                    {
                        "pilot_id": "formalization-benchmark-t2-pilot-2",
                        "manifest_payload_sha256": PREDECESSOR_MANIFEST_PAYLOAD_SHA256,
                    }
                ),
                encoding="utf-8",
            )
            run_root = root / "runs"
            pair_root = run_root / "pairs" / PREDECESSOR_INCIDENT_RUN_ID
            pair_root.mkdir(parents=True)
            report = pair_root / "pair_report.json"
            state_path = pair_root / "pair_state.json"
            report.write_text(
                json.dumps(
                    {
                        "pilot_id": "formalization-benchmark-t2-pilot-2",
                        "task_id": "P01-T2",
                        "status": "PAIR_INCIDENT",
                        "run_id": PREDECESSOR_INCIDENT_RUN_ID,
                        "manifest_sha256": sha256_file(manifest),
                        "pair_root": str(pair_root),
                        "pair_state_path": str(state_path),
                    }
                ),
                encoding="utf-8",
            )
            state_path.write_text(
                json.dumps(
                    {
                        "status": "PAIR_INCIDENT",
                        "run_id": PREDECESSOR_INCIDENT_RUN_ID,
                        "pair_root": str(pair_root),
                        "pair_state_path": str(state_path),
                        "pair_report_sha256": sha256_file(report),
                    }
                ),
                encoding="utf-8",
            )
            index = run_root / "index" / "P01-T2.json"
            index.parent.mkdir()
            index.write_text(
                json.dumps(
                    {
                        "task_id": "P01-T2",
                        "run_id": PREDECESSOR_INCIDENT_RUN_ID,
                        "pair_root": str(pair_root),
                        "pair_state_path": str(state_path),
                    }
                ),
                encoding="utf-8",
            )
            deployment = root / "deployment.json"
            deployment.write_text(
                json.dumps(
                    {
                        "schema_version": "formalization-deployment-1",
                        "pilot_id": "formalization-benchmark-t2-pilot-2",
                        "release_commit": PREDECESSOR_RELEASE_COMMIT,
                        "release_manifest_sha256": sha256_file(manifest),
                        "run_root": str(run_root),
                        "predecessor_pilot_id": "formalization-benchmark-t2-pilot-1",
                        "predecessor_run_root": str(legacy_run_root),
                        "predecessor_deployment_record": str(legacy_deployment),
                        "predecessor_deployment_record_sha256": sha256_file(legacy_deployment),
                        "predecessor_pair_report": str(legacy_report),
                        "predecessor_pair_report_sha256": sha256_file(legacy_report),
                    }
                ),
                encoding="utf-8",
            )
            before = {
                path: sha256_file(path)
                for path in (
                    deployment, manifest, index, report, state_path,
                    legacy_deployment, legacy_manifest, legacy_index,
                    legacy_report, legacy_state,
                )
            }
            with mock.patch.multiple(
                "setup_titan",
                PREDECESSOR_INCIDENT_REPORT_SHA256=before[report],
                PREDECESSOR_DEPLOYMENT_SHA256=before[deployment],
                PREDECESSOR_MANIFEST_FILE_SHA256=before[manifest],
                PREDECESSOR_INDEX_SHA256=before[index],
                PREDECESSOR_STATE_SHA256=before[state_path],
                LEGACY_DEPLOYMENT_SHA256=before[legacy_deployment],
                LEGACY_MANIFEST_FILE_SHA256=before[legacy_manifest],
                LEGACY_INDEX_SHA256=before[legacy_index],
                LEGACY_INCIDENT_REPORT_SHA256=before[legacy_report],
                LEGACY_STATE_SHA256=before[legacy_state],
            ):
                lineage = pilot2_lineage(str(root))
                self.assertEqual(lineage["predecessor_run_root"], str(run_root.resolve()))
                self.assertEqual(lineage["legacy_predecessor_run_root"], str(legacy_run_root))
                self.assertEqual(lineage["predecessor_pair_report_sha256"], before[report])
                self.assertEqual(lineage["predecessor_pair_state_sha256"], before[state_path])
                self.assertEqual(lineage["predecessor_task_index_sha256"], before[index])
                self.assertEqual(lineage["legacy_predecessor_pair_report_sha256"], before[legacy_report])
                self.assertEqual(before, {path: sha256_file(path) for path in before})
                original_legacy_report = legacy_report.read_bytes()
                legacy_altered = json.loads(legacy_report.read_text(encoding="utf-8"))
                legacy_altered["status"] = "COMPLETE"
                legacy_report.write_text(json.dumps(legacy_altered), encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkError, "pilot-1 incident evidence changed"):
                    pilot2_lineage(str(root))
                legacy_report.write_bytes(original_legacy_report)

                altered = json.loads(report.read_text(encoding="utf-8"))
                altered["status"] = "COMPLETE"
                report.write_text(json.dumps(altered), encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkError, "hash chain changed"):
                    pilot2_lineage(str(root))
                altered["status"] = "PAIR_INCIDENT"
                altered["incident"] = {"tampered": True}
                report.write_text(json.dumps(altered), encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkError, "hash chain changed"):
                    pilot2_lineage(str(root))

    def test_pilot3_incident_qualification_and_transitive_lineage_are_hash_bound(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = (Path(temporary) / "pilot-3-deployment").resolve()
            run_root = root / "runs"
            pilot2_run_root = (Path(temporary) / "pilot-2-deployment" / "runs").resolve()
            pilot1_run_root = (Path(temporary) / "pilot-1-deployment" / "runs").resolve()
            pilot2_run_root.mkdir(parents=True)
            pilot1_run_root.mkdir(parents=True)
            old_lineage = {
                "predecessor_pilot_id": "formalization-benchmark-t2-pilot-2",
                "predecessor_run_root": str(pilot2_run_root),
                "legacy_predecessor_pilot_id": "formalization-benchmark-t2-pilot-1",
                "legacy_predecessor_run_root": str(pilot1_run_root),
            }
            manifest = (
                root / "release" / "paper_bencmark" / "formalization_benchmark"
                / "manifest.json"
            )
            manifest.parent.mkdir(parents=True)
            manifest.write_text(
                json.dumps({
                    "pilot_id": "formalization-benchmark-t2-pilot-3",
                    "manifest_payload_sha256": PILOT3_MANIFEST_PAYLOAD_SHA256,
                }),
                encoding="utf-8",
            )
            pair_root = run_root / "pairs" / PILOT3_INCIDENT_RUN_ID
            pair_root.mkdir(parents=True)
            report = pair_root / "pair_report.json"
            state = pair_root / "pair_state.json"
            report.write_text(
                json.dumps({
                    "pilot_id": "formalization-benchmark-t2-pilot-3",
                    "task_id": "P01-T2",
                    "status": "PAIR_INCIDENT",
                    "run_id": PILOT3_INCIDENT_RUN_ID,
                    "manifest_sha256": sha256_file(manifest),
                    "pair_root": str(pair_root),
                    "pair_state_path": str(state),
                }),
                encoding="utf-8",
            )
            state.write_text(
                json.dumps({
                    "status": "PAIR_INCIDENT",
                    "run_id": PILOT3_INCIDENT_RUN_ID,
                    "pair_root": str(pair_root),
                    "pair_state_path": str(state),
                    "pair_report_sha256": sha256_file(report),
                }),
                encoding="utf-8",
            )
            index = run_root / "index" / "P01-T2.json"
            index.parent.mkdir()
            index.write_text(
                json.dumps({
                    "task_id": "P01-T2",
                    "run_id": PILOT3_INCIDENT_RUN_ID,
                    "pair_root": str(pair_root),
                    "pair_state_path": str(state),
                }),
                encoding="utf-8",
            )
            deployment = root / "deployment.json"
            deployment.write_text(
                json.dumps({
                    "schema_version": "formalization-deployment-1",
                    "pilot_id": "formalization-benchmark-t2-pilot-3",
                    "release_commit": PILOT3_RELEASE_COMMIT,
                    "release_manifest_sha256": sha256_file(manifest),
                    "manifest_payload_sha256": PILOT3_MANIFEST_PAYLOAD_SHA256,
                    "run_root": str(run_root),
                    **old_lineage,
                }),
                encoding="utf-8",
            )
            qualification = (
                run_root / "qualifications" / sha256_file(manifest) / "qualification.json"
            )
            qualification.parent.mkdir(parents=True)
            qualification_roles = qualification.parent / "roles"
            qualification_roles.mkdir()
            qualification_artifact = qualification_roles / "turn.json"
            qualification_artifact.write_text('{"probe":true}', encoding="utf-8")
            qualification.write_text(
                json.dumps({
                    "schema_version": "formalization-provider-qualification-2",
                    "status": "PASSED",
                    "roles_manifest": tree_manifest(qualification_roles),
                    "identity": {
                        "pilot_id": "formalization-benchmark-t2-pilot-3",
                        "manifest_sha256": sha256_file(manifest),
                        "manifest_payload_sha256": PILOT3_MANIFEST_PAYLOAD_SHA256,
                        "deployment_path": str(deployment),
                        "deployment_sha256": sha256_file(deployment),
                    },
                }),
                encoding="utf-8",
            )
            before = {path: sha256_file(path) for path in (
                deployment, manifest, index, report, state, qualification,
            )}
            with mock.patch.multiple(
                "setup_titan",
                PILOT3_DEPLOYMENT_SHA256=before[deployment],
                PILOT3_MANIFEST_FILE_SHA256=before[manifest],
                PILOT3_INDEX_SHA256=before[index],
                PILOT3_INCIDENT_REPORT_SHA256=before[report],
                PILOT3_STATE_SHA256=before[state],
                PILOT3_QUALIFICATION_SHA256=before[qualification],
            ), mock.patch("setup_titan.pilot2_lineage", return_value=old_lineage) as older:
                lineage = predecessor_lineage(str(root))
                self.assertEqual(lineage["predecessor_run_root"], str(run_root))
                self.assertEqual(lineage["legacy_predecessor_run_root"], str(pilot2_run_root))
                self.assertEqual(lineage["ancestral_predecessor_run_root"], str(pilot1_run_root))
                self.assertEqual(lineage["predecessor_qualification_sha256"], before[qualification])
                older.assert_called_with(str(pilot2_run_root.parent))
                self.assertEqual(before, {path: sha256_file(path) for path in before})
                verify_predecessor_lineage(str(root), lineage)

                with mock.patch("setup_titan.pilot2_lineage", return_value={
                    **old_lineage, "predecessor_pilot_id": "tampered"
                }), self.assertRaisesRegex(BenchmarkError, "does not bind"):
                    predecessor_lineage(str(root))

                original_artifact = qualification_artifact.read_bytes()
                qualification_artifact.write_text('{"probe":false}', encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkError, "pilot-3 qualification is not passed"):
                    predecessor_lineage(str(root))
                qualification_artifact.write_bytes(original_artifact)

                original_report = report.read_bytes()
                report.write_text('{"status":"COMPLETE"}', encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkError, "pilot-3 incident evidence"):
                    predecessor_lineage(str(root))
                report.write_bytes(original_report)

                qualification.write_text('{"status":"FAILED"}', encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkError, "pilot-3 qualification evidence"):
                    predecessor_lineage(str(root))

    @staticmethod
    def _write_read_only_skill(root: Path, contents: str) -> None:
        references = root / "references"
        references.mkdir(parents=True)
        (root / "SKILL.md").write_text(contents, encoding="utf-8")
        (references / "operations.md").write_text(contents, encoding="utf-8")
        (root / "SKILL.md").chmod(0o400)
        (references / "operations.md").chmod(0o400)
        references.chmod(0o500)
        root.chmod(0o500)

    @staticmethod
    def _linux_read_only_rename_guard(moves: list[tuple[str, str]]):
        real_replace = os.replace

        def guarded_replace(source_path, target_path):
            source = Path(source_path)
            target = Path(target_path)
            if source.parent != target.parent:
                if not stat.S_IMODE(source.stat().st_mode) & stat.S_IWUSR:
                    raise PermissionError(
                        f"read-only cross-parent directory rename: {source}"
                    )
                moves.append((source.name, target.name))
            real_replace(source_path, target_path)

        return guarded_replace

    def test_command_canary_embedded_python_probe_parses(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            staging = root / ".deployment.install-fixture"
            packages = root / "packages"
            staging.mkdir()
            packages.mkdir()
            deployment = SimpleNamespace(
                path=staging / "deployment.json",
                bwrap_binary=root / "bwrap",
                offline_shell=root / "offline-shell",
                toolchain_root=root / "toolchain",
                packages_root=packages,
                library_source=root / "library" / "source" / "NumStability",
                library_olean=root / "library" / "olean",
            )
            completed = SimpleNamespace(returncode=125, stdout="early failure")

            with mock.patch(
                "setup_titan.subprocess.run", return_value=completed
            ) as sandbox_run, self.assertRaises(BenchmarkError):
                run_command_sandbox_canary(deployment, "N")

            command = sandbox_run.call_args.args[0]
            script = command[-1]
            heredoc_start = "python3 - <<'PY'\n"
            self.assertIn(heredoc_start, script)
            probe = script.split(heredoc_start, 1)[1].split("\nPY\n", 1)[0]
            compile(probe, "<command-sandbox-canary>", "exec")
            for expected_literal in (
                "'socket-denied\\n'",
                "'x32-denied\\n'",
                "'signals-resources-scheduling-and-metadata-denied\\n'",
            ):
                self.assertIn(expected_literal, probe)

    def test_command_canary_preserves_early_failure_with_missing_markers(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            staging = root / ".deployment.install-fixture"
            packages = root / "packages"
            staging.mkdir()
            packages.mkdir()
            deployment = SimpleNamespace(
                path=staging / "deployment.json",
                bwrap_binary=root / "bwrap",
                offline_shell=root / "offline-shell",
                toolchain_root=root / "toolchain",
                packages_root=packages,
                library_source=root / "library" / "source" / "NumStability",
                library_olean=root / "library" / "olean",
            )
            output = "discarded-prefix-" + "x" * 2500 + "-sandbox-root-cause"
            completed = SimpleNamespace(returncode=125, stdout=output)

            with mock.patch(
                "setup_titan.subprocess.run", return_value=completed
            ), self.assertRaisesRegex(
                BenchmarkError, "command sandbox canary failed"
            ) as raised:
                run_command_sandbox_canary(deployment, "N")

            message = str(raised.exception)
            self.assertIn("returncode=125", message)
            self.assertIn("sandbox-root-cause", message)
            self.assertNotIn("discarded-prefix", message)
            for check in (
                "command_succeeded",
                "workspace_write_succeeded",
                "lean_compile_succeeded",
                "x32_syscalls_denied",
                "native_socket_syscall_denied",
                "signal_and_metadata_syscalls_denied",
                "control_auth_unchanged",
                "control_config_absent",
                "special_workspace_nodes_denied",
                "network_attempt_marked",
            ):
                self.assertIn(repr(check), message)

    def test_measured_build_command_uses_bounded_service_and_only_explicit_paths(self) -> None:
        with mock.patch("hardware.host_cpu_allowlist", return_value="0-7"):
            command = measured_build_command(
                systemd_run=Path("/usr/bin/systemd-run"),
                build_runner=Path("/release/measure_library_build.py"),
                checkout=Path("/private/checkout"),
                artifact_root=Path("/deployment/build"),
                toolchain_root=Path("/toolchain"),
                expected_commit="a" * 40,
                mathlib_commit="b" * 40,
                lean_toolchain="leanprover/lean4:test",
                service_environment={"TMPDIR": "/hdd/tooling/tmp"},
            )
        self.assertIn("CPUAffinity=0-7", command)
        self.assertIn("SystemCallFilter=~sched_setaffinity", command)
        self.assertIn("MemoryMax=34359738368", command)
        self.assertIn("TMPDIR=/hdd/tooling/tmp", command)
        self.assertIn("--expected-commit", command)
        self.assertIn("--mathlib-commit", command)

    def test_measured_build_service_environment_is_private_and_rejects_weak_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            deployment = parent / ".deployment.install-fixture"
            environment = measured_build_service_environment(deployment)
            self.assertEqual(
                set(environment), {"ELAN_HOME", "TMPDIR", "XDG_CACHE_HOME"}
            )
            tooling = parent / "tooling"
            self.assertEqual(tooling.stat().st_mode & 0o777, 0o700)
            (tooling / "tmp").chmod(0o755)
            with self.assertRaisesRegex(Exception, "tooling path is unsafe"):
                measured_build_service_environment(deployment)

    def test_dependency_preparation_uses_private_cache_and_tmp(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            deployment = root / "deployment-pilot-4-r1"
            private_bin = root / "tooling" / "elan" / "bin"
            private_bin.mkdir(parents=True, mode=0o700)
            private_bin.parent.parent.chmod(0o700)
            private_bin.parent.chmod(0o700)
            with mock.patch.dict(
                os.environ,
                {"XDG_CACHE_HOME": "/home/old-cache", "TMPDIR": "/tmp"},
            ):
                environment = private_provisioning_environment(deployment)
            self.assertEqual(
                environment["XDG_CACHE_HOME"], str(root / "tooling" / "cache")
            )
            self.assertEqual(
                environment["TMPDIR"], str(root / "tooling" / "tmp")
            )
            self.assertEqual(environment["ELAN_HOME"], str(private_bin.parent))
            self.assertEqual(environment["PATH"].split(":", 1)[0], str(private_bin))

    def test_failed_install_cleanup_refuses_substituted_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root = parent / "deployment"
            root.mkdir()
            expected = directory_identity(root)
            original = parent / "renamed-owned-root"
            root.rename(original)
            root.mkdir()
            replacement_marker = root / "do-not-delete"
            replacement_marker.write_text("replacement\n", encoding="utf-8")

            with self.assertRaisesRegex(Exception, "identity changed"):
                remove_owned_deployment_root(root, expected)

            self.assertTrue(replacement_marker.is_file())
            self.assertTrue(original.is_dir())

    def test_cleanup_preserves_substitution_racing_the_quarantine_rename(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root = parent / "deployment"
            root.mkdir()
            (root / "owned").write_text("owned\n", encoding="utf-8")
            expected = directory_identity(root)
            saved_owned = parent / "saved-owned"
            real_rename = os.rename
            injected = False

            def swap_before_rename(source, destination):
                nonlocal injected
                if not injected and Path(source) == root:
                    injected = True
                    real_rename(root, saved_owned)
                    root.mkdir()
                    (root / "replacement").write_text("preserve\n", encoding="utf-8")
                real_rename(source, destination)

            with mock.patch("setup_titan.os.rename", side_effect=swap_before_rename):
                with self.assertRaisesRegex(Exception, "identity changed"):
                    remove_owned_deployment_root(root, expected)

            quarantines = list(parent.glob(".deployment.failed-*"))
            self.assertEqual(len(quarantines), 1)
            self.assertEqual(
                (quarantines[0] / "replacement").read_text(encoding="utf-8"),
                "preserve\n",
            )
            self.assertTrue((saved_owned / "owned").is_file())

    def test_launcher_binds_deployment_path_and_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            launcher = root / "run-benchmark"
            write_launcher(
                launcher,
                root / "deployment.json",
                "a" * 64,
                root / "runner.py",
            )
            source = launcher.read_text(encoding="utf-8")
            self.assertIn("HIGHAMBENCH_FORMALIZATION_DEPLOYMENT=", source)
            self.assertIn("HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256=" + "a" * 64, source)

    def test_isolated_launcher_can_import_frozen_sibling_modules(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            runner = root / "runner.py"
            sibling = root / "sibling.py"
            sibling.write_text("VALUE = 'sibling-import-ok'\n", encoding="utf-8")
            runner.write_text(
                "import json, os, sys\n"
                "from sibling import VALUE\n"
                "print(json.dumps({\n"
                "    'value': VALUE,\n"
                "    'argv': sys.argv[1:],\n"
                "    'deployment': os.environ.get('HIGHAMBENCH_FORMALIZATION_DEPLOYMENT'),\n"
                "}))\n",
                encoding="utf-8",
            )
            deployment = root / "deployment.json"
            launcher = root / "run-benchmark"
            write_launcher(launcher, deployment, "b" * 64, runner)

            completed = subprocess.run(
                [str(launcher), "doctor", "--task-id", "P01-T2"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )

            self.assertEqual(completed.returncode, 0, completed.stdout)
            record = __import__("json").loads(completed.stdout)
            self.assertEqual(record["value"], "sibling-import-ok")
            self.assertEqual(record["argv"], ["doctor", "--task-id", "P01-T2"])
            self.assertEqual(record["deployment"], str(deployment))

    def test_isolated_runner_command_imports_siblings_directly(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "helper.py").write_text("VALUE = 17\n", encoding="utf-8")
            runner = root / "runner.py"
            runner.write_text(
                "from helper import VALUE\nprint(VALUE)\n", encoding="utf-8"
            )
            completed = subprocess.run(
                isolated_runner_command(runner),
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertEqual(completed.stdout.strip(), "17")

    def test_replaces_existing_skill_without_leaving_shared_staging(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            source.mkdir()
            destination.mkdir(parents=True)
            (source / "SKILL.md").write_text("new\n", encoding="utf-8")
            (destination / "SKILL.md").write_text("old\n", encoding="utf-8")

            install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "new\n"
            )
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )

    def test_installs_0500_skill_under_linux_read_only_rename_guard(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            self._write_read_only_skill(source, "new\n")
            moves: list[tuple[str, str]] = []

            with mock.patch(
                "setup_titan.os.replace",
                side_effect=self._linux_read_only_rename_guard(moves),
            ):
                install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "new\n"
            )
            self.assertEqual(stat.S_IMODE(destination.stat().st_mode), 0o500)
            self.assertEqual(
                stat.S_IMODE((destination / "references").stat().st_mode), 0o500
            )
            self.assertEqual(moves, [("staged", destination.name)])
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )

    def test_updates_0500_skill_and_removes_read_only_backup(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            self._write_read_only_skill(source, "new\n")
            self._write_read_only_skill(destination, "old\n")
            moves: list[tuple[str, str]] = []

            with mock.patch(
                "setup_titan.os.replace",
                side_effect=self._linux_read_only_rename_guard(moves),
            ):
                install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "new\n"
            )
            self.assertEqual(stat.S_IMODE(destination.stat().st_mode), 0o500)
            self.assertEqual(
                moves,
                [(destination.name, "previous"), ("staged", destination.name)],
            )
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )

    def test_rolls_back_0500_skill_after_committed_final_rename_error(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            self._write_read_only_skill(source, "new\n")
            self._write_read_only_skill(destination, "old\n")
            moves: list[tuple[str, str]] = []
            guarded_replace = self._linux_read_only_rename_guard(moves)
            injected = False

            def fail_after_final_rename(source_path, target_path):
                nonlocal injected
                guarded_replace(source_path, target_path)
                if (
                    not injected
                    and Path(source_path).name == "staged"
                    and Path(target_path) == destination
                ):
                    injected = True
                    raise OSError("injected post-rename failure")

            with mock.patch(
                "setup_titan.os.replace", side_effect=fail_after_final_rename
            ):
                with self.assertRaisesRegex(OSError, "injected post-rename failure"):
                    install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "old\n"
            )
            self.assertEqual(stat.S_IMODE(destination.stat().st_mode), 0o500)
            self.assertEqual(
                moves,
                [
                    (destination.name, "previous"),
                    ("staged", destination.name),
                    (destination.name, "staged"),
                    ("previous", destination.name),
                ],
            )
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )

    def test_rejects_substituted_rename_destination_and_restores_previous(self) -> None:
        for substitution in ("symlink", "directory"):
            with self.subTest(substitution=substitution):
                with tempfile.TemporaryDirectory() as temporary:
                    root = Path(temporary)
                    source = root / "source"
                    outside = root / "outside"
                    destination = root / "skills" / "run-highambench-experiments"
                    self._write_read_only_skill(source, "new\n")
                    self._write_read_only_skill(destination, "old\n")
                    outside.mkdir()
                    (outside / "marker").write_text("outside\n", encoding="utf-8")
                    real_replace = os.replace
                    injected = False

                    def substitute_staged(source_path, target_path):
                        nonlocal injected
                        source_value = Path(source_path)
                        target_value = Path(target_path)
                        if (
                            not injected
                            and source_value.name == "staged"
                            and target_value == destination
                        ):
                            injected = True
                            real_replace(
                                source_value,
                                source_value.parent / "legitimate-staged",
                            )
                            if substitution == "symlink":
                                source_value.symlink_to(
                                    outside, target_is_directory=True
                                )
                            else:
                                source_value.mkdir()
                                (source_value / "attacker-marker").write_text(
                                    "attacker\n", encoding="utf-8"
                                )
                        real_replace(source_path, target_path)

                    with mock.patch(
                        "setup_titan.os.replace", side_effect=substitute_staged
                    ):
                        with self.assertRaisesRegex(
                            BenchmarkError, "does not identify the moved directory"
                        ):
                            install_skill_atomically(source, destination)

                    self.assertFalse(destination.is_symlink())
                    self.assertEqual(
                        (destination / "SKILL.md").read_text(encoding="utf-8"),
                        "old\n",
                    )
                    self.assertEqual(
                        stat.S_IMODE(destination.stat().st_mode), 0o500
                    )
                    self.assertEqual(
                        (outside / "marker").read_text(encoding="utf-8"),
                        "outside\n",
                    )
                    quarantines = list(
                        destination.parent.glob(
                            ".run-highambench-experiments.untrusted-*"
                        )
                    )
                    self.assertEqual(len(quarantines), 1)
                    if substitution == "symlink":
                        self.assertTrue(quarantines[0].is_symlink())
                    else:
                        self.assertEqual(
                            (quarantines[0] / "attacker-marker").read_text(
                                encoding="utf-8"
                            ),
                            "attacker\n",
                        )

    def test_mode_restore_failure_forces_exact_0500_rollback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            self._write_read_only_skill(source, "new\n")
            self._write_read_only_skill(destination, "old\n")
            real_fchmod = os.fchmod
            saw_relaxed_directory = False
            injected = False

            def fail_first_restore(descriptor, mode):
                nonlocal saw_relaxed_directory, injected
                if mode == 0o700:
                    saw_relaxed_directory = True
                elif mode == 0o500 and saw_relaxed_directory and not injected:
                    injected = True
                    raise OSError("injected mode-restore failure")
                real_fchmod(descriptor, mode)

            with mock.patch(
                "setup_titan.os.fchmod", side_effect=fail_first_restore
            ):
                with self.assertRaisesRegex(
                    BenchmarkError, "mode restoration initially failed"
                ):
                    install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "old\n"
            )
            self.assertEqual(stat.S_IMODE(destination.stat().st_mode), 0o500)
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )

    def test_persistent_mode_restore_failure_retains_recovery_journal(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            self._write_read_only_skill(source, "new\n")
            self._write_read_only_skill(destination, "old\n")
            real_fchmod = os.fchmod

            def reject_0500_restore(descriptor, mode):
                if mode == 0o500:
                    raise OSError("persistent mode-restore failure")
                real_fchmod(descriptor, mode)

            with mock.patch(
                "setup_titan.os.fchmod", side_effect=reject_0500_restore
            ):
                with self.assertRaisesRegex(
                    BenchmarkError, "previous installation could not be restored"
                ):
                    install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "old\n"
            )
            transactions = list(
                destination.parent.glob(
                    ".run-highambench-experiments.install-*"
                )
            )
            self.assertEqual(len(transactions), 1)
            state = json.loads(
                (transactions[0] / "skill-install-state.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(state["previous_mode"], 0o500)
            self.assertTrue((transactions[0] / "staged").is_dir())

            with self.assertRaisesRegex(
                BenchmarkError, "requires exact recovery"
            ):
                install_skill_atomically(source, destination)

    def test_cleanup_quarantine_rejects_substituted_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            transaction = root / ".skill.install-fixture"
            transaction.mkdir()
            (transaction / "owned").write_text("owned\n", encoding="utf-8")
            saved_owned = root / "saved-owned"
            real_rename = os.rename
            injected = False

            def substitute_root(source_path, target_path, *args, **kwargs):
                nonlocal injected
                if not injected and Path(source_path) == transaction:
                    injected = True
                    real_rename(transaction, saved_owned)
                    transaction.mkdir()
                    (transaction / "replacement").write_text(
                        "preserve\n", encoding="utf-8"
                    )
                real_rename(source_path, target_path, *args, **kwargs)

            with mock.patch(
                "setup_titan.os.rename", side_effect=substitute_root
            ):
                with self.assertRaisesRegex(
                    BenchmarkError, "changed during quarantine"
                ):
                    _remove_skill_transaction_tree(transaction)

            self.assertEqual(
                (saved_owned / "owned").read_text(encoding="utf-8"), "owned\n"
            )
            quarantines = [path for path in root.iterdir() if ".cleanup-" in path.name]
            self.assertEqual(len(quarantines), 1)
            self.assertEqual(
                (quarantines[0] / "replacement").read_text(encoding="utf-8"),
                "preserve\n",
            )

    def test_cleanup_child_symlink_race_does_not_chmod_outside(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            transaction = root / ".skill.install-fixture"
            child = transaction / "child"
            outside = root / "outside"
            child.mkdir(parents=True)
            outside.mkdir()
            (child / "owned").write_text("owned\n", encoding="utf-8")
            outside.chmod(0o500)
            child.chmod(0o500)
            real_open = os.open
            injected = False

            def substitute_child(path, flags, mode=0o777, *, dir_fd=None):
                nonlocal injected
                if not injected and path == "child" and dir_fd is not None:
                    injected = True
                    os.rename(
                        "child",
                        "saved-child",
                        src_dir_fd=dir_fd,
                        dst_dir_fd=dir_fd,
                    )
                    os.symlink(
                        str(outside),
                        "child",
                        target_is_directory=True,
                        dir_fd=dir_fd,
                    )
                return real_open(path, flags, mode, dir_fd=dir_fd)

            with mock.patch("setup_titan.os.open", side_effect=substitute_child):
                with self.assertRaises(OSError):
                    _remove_skill_transaction_tree(transaction)

            self.assertEqual(stat.S_IMODE(outside.stat().st_mode), 0o500)
            self.assertTrue((outside).is_dir())
            quarantines = [path for path in root.iterdir() if ".cleanup-" in path.name]
            self.assertEqual(len(quarantines), 1)
            self.assertTrue((quarantines[0] / "child").is_symlink())

    def test_malformed_transaction_fails_as_benchmark_error(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            deployment = root / "deployment"
            launcher = root / "launcher"
            deployment.mkdir()
            (deployment / INSTALL_TRANSACTION).write_text("{broken", encoding="utf-8")
            with self.assertRaisesRegex(Exception, "transaction is malformed"):
                _load_transaction(
                    deployment, deployment_root=deployment, launcher=launcher
                )

    def test_ready_staging_is_published_and_resumed_without_rebuild(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            deployment = root / "deployment"
            launcher = root / "launcher"
            staging = root / ".deployment.install-existing"
            staging.mkdir()
            record = staging / "deployment.json"
            record.write_text('{"ready":true}\n', encoding="utf-8")
            from common import sha256_file

            transaction = _transaction_record(
                status="READY_TO_PUBLISH",
                deployment_root=deployment,
                launcher=launcher,
                deployment_record_sha256=sha256_file(record),
            )
            (staging / INSTALL_TRANSACTION).write_text(
                json.dumps(transaction) + "\n", encoding="utf-8"
            )
            args = SimpleNamespace(
                deployment_root=str(deployment), launcher=str(launcher)
            )
            with mock.patch(
                "setup_titan._finalize_install", return_value=deployment / "deployment.json"
            ) as finalize:
                result = install(args)

            self.assertEqual(result, deployment / "deployment.json")
            self.assertTrue(deployment.is_dir())
            self.assertFalse(staging.exists())
            finalize.assert_called_once_with(args, deployment.resolve(), launcher.resolve())

    def test_post_publication_failure_retains_resumable_deployment(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            deployment = root / "deployment"
            launcher = root / "launcher"
            args = SimpleNamespace(
                deployment_root=str(deployment), launcher=str(launcher)
            )

            def build_staged(_args, staging, _identity, _published):
                record = staging / "deployment.json"
                record.write_text('{"ready":true}\n', encoding="utf-8")
                return record

            with mock.patch("setup_titan._install_once", side_effect=build_staged):
                with mock.patch(
                    "setup_titan._finalize_install",
                    side_effect=RuntimeError("injected finalization failure"),
                ):
                    with self.assertRaisesRegex(RuntimeError, "finalization failure"):
                        install(args)

            self.assertTrue(deployment.is_dir())
            self.assertEqual(
                json.loads((deployment / INSTALL_TRANSACTION).read_text(encoding="utf-8"))[
                    "status"
                ],
                "READY_TO_PUBLISH",
            )
            self.assertEqual(list(root.glob(".deployment.install-*")), [])

    def test_restores_previous_skill_when_final_rename_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            source.mkdir()
            destination.mkdir(parents=True)
            (source / "SKILL.md").write_text("new\n", encoding="utf-8")
            (destination / "SKILL.md").write_text("old\n", encoding="utf-8")
            real_replace = os.replace

            def fail_new_install(source_path: os.PathLike[str], target_path: os.PathLike[str]) -> None:
                source_value = Path(source_path)
                target_value = Path(target_path)
                if source_value.name == "staged" and target_value == destination:
                    raise OSError("injected final-rename failure")
                real_replace(source_path, target_path)

            with mock.patch("setup_titan.os.replace", side_effect=fail_new_install):
                with self.assertRaisesRegex(OSError, "injected final-rename failure"):
                    install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "old\n"
            )
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )

    def test_restores_previous_skill_when_interrupted_after_backup_rename(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            destination = root / "skills" / "run-highambench-experiments"
            source.mkdir()
            destination.mkdir(parents=True)
            (source / "SKILL.md").write_text("new\n", encoding="utf-8")
            (destination / "SKILL.md").write_text("old\n", encoding="utf-8")
            real_replace = os.replace

            def interrupt_after_backup(source_path, target_path):
                real_replace(source_path, target_path)
                if Path(target_path).name == "previous":
                    raise KeyboardInterrupt("injected interrupt after backup rename")

            with mock.patch("setup_titan.os.replace", side_effect=interrupt_after_backup):
                with self.assertRaisesRegex(KeyboardInterrupt, "injected interrupt"):
                    install_skill_atomically(source, destination)

            self.assertEqual(
                (destination / "SKILL.md").read_text(encoding="utf-8"), "old\n"
            )
            self.assertEqual(
                list(destination.parent.glob(".run-highambench-experiments.install-*")),
                [],
            )


if __name__ == "__main__":
    unittest.main()
