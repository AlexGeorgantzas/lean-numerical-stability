from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))

from setup_titan import (  # noqa: E402
    INSTALL_TRANSACTION,
    _load_transaction,
    _transaction_record,
    directory_identity,
    install,
    install_skill_atomically,
    isolated_runner_command,
    measured_build_command,
    measured_build_service_environment,
    remove_owned_deployment_root,
    write_launcher,
)


class SkillInstallTests(unittest.TestCase):
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
