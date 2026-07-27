from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from check_construction import (  # noqa: E402
    check_one,
    construction_specs,
    make_parser,
    resolve_environment,
    run_checks,
)
from hashes import create_manifest  # noqa: E402
from common import BenchmarkToolError  # noqa: E402


class ConstructionCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.project = self.root / "project"
        self.project.mkdir()
        self.benchmark = self.root / "benchmark"
        (self.benchmark / "tools").mkdir(parents=True)
        (self.benchmark / "tools" / "lean_isolated.py").write_text(
            "# test adapter\n", encoding="utf-8"
        )
        (self.benchmark / "tools" / "dependency_audit.lean").write_text(
            "-- test audit\n", encoding="utf-8"
        )
        for filename in (
            "check_construction.py",
            "common.py",
            "hashes.py",
            "preflight.py",
            "validator.py",
        ):
            (self.benchmark / "tools" / filename).write_text(
                f"# test {filename}\n", encoding="utf-8"
            )
        (self.benchmark / "agent_prompt.md").write_text("prompt\n", encoding="utf-8")
        shared = self.benchmark / "shared" / "HighamBench" / "Definitions.lean"
        shared.parent.mkdir(parents=True)
        shared.write_text("namespace HighamBench\nend HighamBench\n", encoding="utf-8")

        self.private_gold = self.root / "private_gold"
        private_paper = self.private_gold / "P01"
        private_paper.mkdir(parents=True)
        (private_paper / "CommonN.lean").write_text(
            "theorem commonN : True := by trivial\n", encoding="utf-8"
        )
        (private_paper / "CommonL.lean").write_text(
            "theorem commonL : True := by trivial\n", encoding="utf-8"
        )

        controlled = self.benchmark / "metadata" / "controlled"
        controlled.mkdir(parents=True)
        for spec in construction_specs():
            if spec.condition != "N":
                continue
            task = self.benchmark / "tasks" / "P01" / spec.tier
            task.mkdir(parents=True)
            simple = spec.target_theorem.rsplit(".", 1)[-1]
            target = (
                "namespace HighamBench\n"
                f"theorem {simple} : True := by\n"
                "  sorry\n"
                "end HighamBench\n"
            )
            (task / "Target.lean").write_text(target, encoding="utf-8")
            (task / "context.md").write_text(f"context {spec.tier}\n", encoding="utf-8")
            manifest = create_manifest(
                self.benchmark,
                requested=[
                    "agent_prompt.md",
                    "shared/HighamBench/Definitions.lean",
                    f"tasks/P01/{spec.tier}/Target.lean",
                    f"tasks/P01/{spec.tier}/context.md",
                ],
                label=f"{spec.task_id}-controlled",
            )
            (controlled / f"{spec.task_id}.json").write_text(
                json.dumps(manifest), encoding="utf-8"
            )
            for condition in ("N", "L"):
                (private_paper / f"{spec.tier}_{condition}.lean").write_text(
                    target.replace("sorry", "trivial"), encoding="utf-8"
                )

        self.toolchain = self.root / "toolchain"
        self.packages = self.root / "packages"
        self.shared_olean = self.root / "shared-olean"
        self.library_source = self.project / "NumStability"
        self.library_olean = self.root / "library-olean"
        self.hidden = self.root / "hidden"
        for directory in (
            self.toolchain,
            self.packages,
            self.shared_olean,
            self.library_source,
            self.library_olean,
        ):
            directory.mkdir()
        (self.library_source / "Example.lean").write_text(
            "namespace NumStability\nend NumStability\n", encoding="utf-8"
        )
        self.library_root = self.project / "NumStability.lean"
        self.library_root.write_text("-- library root\n", encoding="utf-8")
        compiled = self.library_olean / "NumStability" / "Example.olean"
        compiled.parent.mkdir(parents=True)
        compiled.write_bytes(b"test compiled library")
        shared_compiled = self.shared_olean / "HighamBench" / "Definitions.olean"
        shared_compiled.parent.mkdir(parents=True)
        shared_compiled.write_bytes(b"test shared olean")
        mathlib_source = self.packages / "mathlib" / "Mathlib.lean"
        mathlib_source.parent.mkdir(parents=True)
        mathlib_source.write_text("-- test Mathlib source\n", encoding="utf-8")
        package_olean = (
            self.packages
            / "mathlib"
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Mathlib.olean"
        )
        package_olean.parent.mkdir(parents=True)
        package_olean.write_bytes(b"test Mathlib olean")
        package_olean.with_name("Mathlib.olean.server").write_bytes(
            b"test Mathlib server data"
        )
        package_olean.with_name("Mathlib.olean.private").write_bytes(
            b"test Mathlib private data"
        )
        package_olean.with_name("Mathlib.ir").write_bytes(b"test Mathlib IR")
        metadata = self.benchmark / "metadata"
        (metadata / "library_source.json").write_text(
            json.dumps(
                create_manifest(
                    self.project,
                    requested=["NumStability", "NumStability.lean"],
                    label="test-source",
                )
            ),
            encoding="utf-8",
        )
        (metadata / "library_olean.json").write_text(
            json.dumps(
                create_manifest(self.library_olean, label="test-compiled")
            ),
            encoding="utf-8",
        )
        (metadata / "packages_runtime.json").write_text(
            json.dumps(create_manifest(self.packages, label="test-packages-runtime")),
            encoding="utf-8",
        )
        self.bwrap = self.root / "bwrap"
        self.bwrap.write_text("test executable\n", encoding="utf-8")
        self.environment = resolve_environment(
            make_parser().parse_args(
                [
                    "--project-root",
                    str(self.project),
                    "--benchmark-root",
                    str(self.benchmark),
                    "--private-gold",
                    str(self.private_gold),
                    "--toolchain-root",
                    str(self.toolchain),
                    "--packages-root",
                    str(self.packages),
                    "--shared-olean-root",
                    str(self.shared_olean),
                    "--library-source",
                    str(self.library_source),
                    "--library-root-file",
                    str(self.library_root),
                    "--library-olean",
                    str(self.library_olean),
                    "--hidden-parent",
                    str(self.hidden),
                    "--bwrap",
                    str(self.bwrap),
                ]
            )
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def successful_validation(config, *, library_use: bool | None = None):
        uses_library = config.condition == "L" if library_use is None else library_use
        declarations = (
            [
                {
                    "name": "NumStability.example",
                    "module": "NumStability.Example",
                    "distance": 1,
                }
            ]
            if uses_library
            else []
        )
        helper_modules = [
            Path(relative).stem for relative in config.local_source_relatives
        ]
        return {
            "pass": True,
            "failure_code": None,
            "note": "accepted",
            "statement_check": {"ok": True},
            "controlled_before": {"ok": True},
            "controlled_hidden": {"ok": True},
            "controlled_after_compile": {"ok": True},
            "controlled_after_expected_compile": {"ok": True},
            "controlled_after_audit": {"ok": True},
            "semantic_statement_check": {
                "candidate": config.target_theorem,
                "expected": "HighamBench.generatedExpected",
                "equal": True,
            },
            "static_findings": [],
            "compile": {
                "exit_code": 0,
                "timed_out": False,
                "system_error": None,
            },
            "dependency_audit": {
                "exit_code": 0,
                "timed_out": False,
                "system_error": None,
                "parsed": {
                    "ok": True,
                    "format_version": 2,
                    "type_check": {
                        "candidate": config.target_theorem,
                        "expected": "HighamBench.generatedExpected",
                        "equal": True,
                    },
                    "forbidden_dependencies": [],
                    "local_modules": helper_modules + ["Submission"],
                    "missing_helper_modules": [],
                },
            },
            "library_audit_complete": True,
            "library_use": uses_library,
            "library_declarations": declarations,
        }

    @staticmethod
    def successful_preflight(root, **kwargs):
        root = Path(root)
        assert (root / "task").is_dir()
        assert not (root / "Submission.lean").exists()
        assert kwargs.get("probe_command") is not None
        return {
            "ok": True,
            "complete": True,
            "filesystem_scan": {
                "root": ".",
                "markers": ["NumStability", "numStability", "lean-fp-analysis"],
                "regular_file_count": 4,
                "directory_count": 4,
                "symlink_count": 0,
                "content_limit_bytes": 4 * 1024 * 1024,
            },
            "filesystem_leaks": [],
            "import_probe": {
                "attempted": True,
                "reliable": True,
                "importable": False,
            },
        }

    def test_matrix_has_exactly_six_proofs_and_only_t1_t2_use_helpers(self) -> None:
        specs = construction_specs()
        self.assertEqual(
            [(item.task_id, item.condition) for item in specs],
            [
                ("P01-T1", "N"),
                ("P01-T1", "L"),
                ("P01-T2", "N"),
                ("P01-T2", "L"),
                ("P01-T3", "N"),
                ("P01-T3", "L"),
            ],
        )
        self.assertEqual(sum(item.helper_filename is not None for item in specs), 4)
        self.assertTrue(
            all(item.helper_filename is None for item in specs if item.tier == "T3")
        )

    def test_fresh_staging_helper_build_and_n_l_commands(self) -> None:
        helper_commands: list[list[str]] = []
        validation_configs = []
        workspace_snapshots: list[tuple[Path, list[str]]] = []

        def fake_runner(command, *, cwd, timeout_seconds):
            self.assertEqual(cwd, self.project)
            self.assertGreater(timeout_seconds, 0)
            helper_commands.append(command)
            source = Path(command[command.index("--source") + 1])
            source.with_suffix(".olean").write_bytes(b"fresh test olean")
            return {
                "exit_code": 0,
                "timed_out": False,
                "system_error": None,
                "seconds": 0.01,
                "output": "format\t2\n",
            }

        def fake_validator(config):
            validation_configs.append(config)
            workspace_snapshots.append(
                (config.workspace, sorted(path.name for path in config.workspace.iterdir()))
            )
            self.assertTrue((config.workspace / "task" / "agent_prompt.md").is_file())
            self.assertTrue((config.workspace / "Submission.lean").is_file())
            for relative in config.local_source_relatives:
                source = config.workspace / relative
                self.assertTrue(source.is_file())
                self.assertTrue(source.with_suffix(".olean").is_file())
            return self.successful_validation(config)

        evidence = run_checks(
            self.environment,
            command_runner=fake_runner,
            validator_fn=fake_validator,
            preflight_fn=self.successful_preflight,
        )
        self.assertTrue(evidence["pass"], evidence)
        self.assertEqual(evidence["summary"]["passed"], 6)
        self.assertEqual(len(helper_commands), 4)
        self.assertEqual(len(validation_configs), 6)
        basis = evidence["verification_basis"]
        self.assertEqual(
            set(basis["tools"]),
            {
                "tools/check_construction.py",
                "tools/common.py",
                "tools/hashes.py",
                "tools/lean_isolated.py",
                "tools/preflight.py",
                "tools/validator.py",
                "tools/dependency_audit.lean",
            },
        )
        self.assertTrue(basis["numstability_source"]["exact_tree"])
        self.assertEqual(basis["numstability_source"]["file_count"], 2)
        self.assertTrue(basis["numstability_compiled"]["exact_tree"])
        self.assertEqual(basis["numstability_compiled"]["file_count"], 1)
        self.assertTrue(basis["packages_runtime"]["exact_tree"])
        self.assertEqual(basis["packages_runtime"]["file_count"], 5)
        self.assertTrue(
            basis["packages_runtime"][
                "only_mathlib_source_and_lean_compiled_artifacts"
            ]
        )
        self.assertEqual(basis["packages_runtime"]["mathlib_source_file_count"], 1)
        self.assertEqual(basis["packages_runtime"]["base_olean_file_count"], 1)
        self.assertEqual(
            basis["packages_runtime"]["compiled_support_file_count"], 3
        )
        self.assertEqual(
            basis["packages_runtime"]["file_count"],
            basis["packages_runtime"]["mathlib_source_file_count"]
            + basis["packages_runtime"]["base_olean_file_count"]
            + basis["packages_runtime"]["compiled_support_file_count"],
        )
        self.assertTrue(
            basis["packages_runtime"]["condition_n_absence_scan"]["ok"]
        )
        self.assertTrue(basis["shared_olean"]["condition_n_absence_scan"]["ok"])
        self.assertRegex(basis["executables"]["python"]["version"], r"^\d+\.\d+\.\d+$")
        self.assertEqual(basis["shared_olean"]["exact_file_count"], 1)
        n_checks = [
            item["n_preflight"] for item in evidence["results"] if item["condition"] == "N"
        ]
        self.assertEqual(len(n_checks), 3)
        self.assertTrue(all(item["ok"] for item in n_checks))
        self.assertTrue(
            all(item["controlled_files_verified_after_staging"]["ok"] for item in n_checks)
        )

        for command in helper_commands:
            condition = command[command.index("--condition") + 1]
            if condition == "N":
                self.assertNotIn("--library-source", command)
                self.assertNotIn("--library-root-file", command)
                self.assertNotIn("--library-olean", command)
            else:
                self.assertIn("--library-source", command)
                self.assertIn("--library-root-file", command)
                self.assertIn("--library-olean", command)

        for config in validation_configs:
            for command in (config.compile_command, config.audit_command):
                assert command is not None
                if config.condition == "N":
                    self.assertNotIn("--library-source", command)
                    self.assertNotIn("--library-root-file", command)
                    self.assertNotIn("--library-olean", command)
                else:
                    self.assertIn("--library-source", command)
                    self.assertIn("--library-root-file", command)
                    self.assertIn("--library-olean", command)

        helper_workspaces = [
            names for _path, names in workspace_snapshots if "CommonN.lean" in names or "CommonL.lean" in names
        ]
        no_helper_workspaces = [
            names for _path, names in workspace_snapshots if "CommonN.lean" not in names and "CommonL.lean" not in names
        ]
        self.assertEqual(len(helper_workspaces), 4)
        self.assertEqual(len(no_helper_workspaces), 2)
        for names in no_helper_workspaces:
            self.assertEqual(names, ["Submission.lean", "task"])
        self.assertTrue(all(not path.exists() for path, _names in workspace_snapshots))

    def test_helper_failure_is_recorded_and_remaining_proofs_are_checked(self) -> None:
        validation_count = 0

        def fake_runner(command, *, cwd, timeout_seconds):
            source = Path(command[command.index("--source") + 1])
            if source.name == "CommonL.lean":
                return {
                    "exit_code": 1,
                    "timed_out": False,
                    "system_error": None,
                    "seconds": 0.01,
                    "output": "test failure",
                }
            source.with_suffix(".olean").write_bytes(b"fresh test olean")
            return {
                "exit_code": 0,
                "timed_out": False,
                "system_error": None,
                "seconds": 0.01,
                "output": "",
            }

        def fake_validator(config):
            nonlocal validation_count
            validation_count += 1
            return self.successful_validation(config)

        evidence = run_checks(
            self.environment,
            command_runner=fake_runner,
            validator_fn=fake_validator,
            preflight_fn=self.successful_preflight,
        )
        self.assertFalse(evidence["pass"])
        self.assertEqual(evidence["summary"]["passed"], 4)
        self.assertEqual(validation_count, 4)
        failures = [item for item in evidence["results"] if not item["pass"]]
        self.assertEqual(
            [(item["task_id"], item["condition"]) for item in failures],
            [("P01-T1", "L"), ("P01-T2", "L")],
        )
        self.assertTrue(all(item["validation"] is None for item in failures))

    def test_l_construction_must_record_real_library_use(self) -> None:
        def fake_runner(command, *, cwd, timeout_seconds):
            source = Path(command[command.index("--source") + 1])
            source.with_suffix(".olean").write_bytes(b"fresh test olean")
            return {
                "exit_code": 0,
                "timed_out": False,
                "system_error": None,
                "seconds": 0.01,
                "output": "",
            }

        def fake_validator(config):
            return self.successful_validation(config, library_use=False)

        evidence = run_checks(
            self.environment,
            command_runner=fake_runner,
            validator_fn=fake_validator,
            preflight_fn=self.successful_preflight,
        )
        self.assertFalse(evidence["pass"])
        self.assertEqual(evidence["summary"]["condition_n_passed"], 3)
        self.assertEqual(evidence["summary"]["condition_l_passed"], 0)
        l_results = [item for item in evidence["results"] if item["condition"] == "L"]
        self.assertTrue(
            all(
                "did not use a NumStability declaration" in item["reasons"][-1]
                for item in l_results
            )
        )

    def test_unmanifested_compiled_library_file_blocks_all_checks(self) -> None:
        extra = self.library_olean / "NumStability" / "Hidden.olean"
        extra.write_bytes(b"unfrozen compiled declaration")
        with self.assertRaisesRegex(
            BenchmarkToolError, "compiled NumStability manifest is not an exact tree snapshot"
        ):
            run_checks(self.environment, preflight_fn=self.successful_preflight)

    def test_manifested_package_runtime_marker_blocks_condition_n_release(self) -> None:
        package = (
            self.packages
            / "mathlib"
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Mathlib.olean"
        )
        package.write_bytes(b"embedded lean-fp-analysis cache path")
        (self.benchmark / "metadata" / "packages_runtime.json").write_text(
            json.dumps(create_manifest(self.packages, label="test-packages-runtime")),
            encoding="utf-8",
        )
        with self.assertRaisesRegex(
            BenchmarkToolError, "pruned package runtime leaks a condition-N marker"
        ):
            run_checks(self.environment, preflight_fn=self.successful_preflight)

    def test_failed_complete_n_preflight_blocks_private_proof_validation(self) -> None:
        spec = next(
            item
            for item in construction_specs()
            if item.task_id == "P01-T3" and item.condition == "N"
        )
        validator_called = False

        def bad_preflight(root, **kwargs):
            self.assertTrue((Path(root) / "task").is_dir())
            self.assertFalse((Path(root) / "Submission.lean").exists())
            return {
                "ok": False,
                "complete": True,
                "filesystem_leaks": [
                    {"kind": "content", "path": "task/context.md", "markers": ["NumStability"]}
                ],
                "import_probe": {"attempted": True, "reliable": True, "importable": False},
            }

        def should_not_validate(config):
            nonlocal validator_called
            validator_called = True
            return self.successful_validation(config)

        result = check_one(
            self.environment,
            spec,
            validator_fn=should_not_validate,
            preflight_fn=bad_preflight,
        )
        self.assertFalse(result["pass"])
        self.assertFalse(validator_called)
        self.assertIn("complete staged condition-N package", result["reasons"][0])
        self.assertTrue(result["n_preflight"]["controlled_files_verified_after_staging"]["ok"])

    def test_real_validator_rejects_private_placeholder_sources_before_bubblewrap(self) -> None:
        spec = next(
            item
            for item in construction_specs()
            if item.task_id == "P01-T3" and item.condition == "N"
        )
        source = self.private_gold / "P01" / spec.gold_filename
        simple = spec.target_theorem.rsplit(".", 1)[-1]
        cases = {
            "sorry": (
                "namespace HighamBench\n"
                f"theorem {simple} : True := by sorry\n"
                "end HighamBench\n"
            ),
            "admit": (
                "namespace HighamBench\n"
                f"theorem {simple} : True := by admit\n"
                "end HighamBench\n"
            ),
            "axiom": (
                "namespace HighamBench\n"
                "axiom hiddenConstructionFact : True\n"
                f"theorem {simple} : True := by exact hiddenConstructionFact\n"
                "end HighamBench\n"
            ),
            "unsafe": (
                "namespace HighamBench\n"
                "unsafe def hiddenConstructionValue : Nat := 0\n"
                f"theorem {simple} : True := by trivial\n"
                "end HighamBench\n"
            ),
        }
        for label, text in cases.items():
            with self.subTest(label=label):
                source.write_text(text, encoding="utf-8")
                result = check_one(
                    self.environment,
                    spec,
                    preflight_fn=self.successful_preflight,
                )
                self.assertFalse(result["pass"])
                self.assertEqual(
                    result["validation"]["failure_code"], "RULE_VIOLATION"
                )
                self.assertGreaterEqual(
                    result["validation"]["static_finding_count"], 1
                )


if __name__ == "__main__":
    unittest.main()
