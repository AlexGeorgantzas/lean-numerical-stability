from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import read_json, sha256_file, write_json  # noqa: E402
from hashes import create_manifest, stage_manifest_files  # noqa: E402
import run_matrix  # noqa: E402


LEAN_COMMIT = "1" * 40
MATHLIB_COMMIT = "2" * 40
NUMSTABILITY_COMMIT = "3" * 40
P01_PAPER_SHA256 = "4" * 64
P02_PAPER_SHA256 = "5" * 64


def _executable(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


def _write_two_paper_task_records(root: Path) -> list[str]:
    papers = []
    task_ids: list[str] = []
    for paper_id, paper_sha256 in (
        ("P01", P01_PAPER_SHA256),
        ("P02", P02_PAPER_SHA256),
    ):
        targets = []
        included_tasks = []
        for tier in ("T1", "T2", "T3"):
            task_id = f"{paper_id}-{tier}"
            theorem_name = f"{paper_id.lower()}_{tier.lower()}_fixture"
            target_dir = root / "tasks" / paper_id / tier
            target_dir.mkdir(parents=True, exist_ok=True)
            (target_dir / "Target.lean").write_text(
                f"theorem {theorem_name} : True := by trivial\n", encoding="utf-8"
            )
            (target_dir / "context.md").write_text("fixture context\n", encoding="utf-8")
            declared_target = (
                f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/Target.lean"
            )
            write_json(
                target_dir / "task.json",
                {
                    "task_id": task_id,
                    "paper_id": paper_id,
                    "tier": tier,
                    "paper_source": {"sha256": paper_sha256},
                    "context_file": (
                        f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/context.md"
                    ),
                    "formal_statement": {
                        "namespace": "HighamBench",
                        "theorem_name": theorem_name,
                        "target_file": declared_target,
                    },
                    "validation": {
                        "required_declaration": f"HighamBench.{theorem_name}",
                        "controlled_target_file": declared_target,
                    },
                },
            )
            controlled = root / "metadata" / "controlled" / f"{task_id}.json"
            controlled.parent.mkdir(parents=True, exist_ok=True)
            write_json(controlled, {"task_id": task_id})
            targets.append(
                {
                    "task_id": task_id,
                    "tier": tier,
                    "availability": "available",
                    "lean_target": {
                        "declaration": theorem_name,
                        "file": declared_target,
                    },
                }
            )
            included_tasks.append(task_id)
            task_ids.append(task_id)
        write_json(
            root / "tasks" / paper_id / "paper.json",
            {
                "paper_id": paper_id,
                "source": {"sha256": paper_sha256},
                "included_tasks": included_tasks,
            },
        )
        papers.append(
            {
                "paper_id": paper_id,
                "source": {"sha256": paper_sha256},
                "targets": targets,
            }
        )
    write_json(
        root / "metadata" / "manifest.json",
        {
            "benchmark_id": "two-paper-fixture",
            "corpus": {"paper_count": 2, "paper_ids": ["P01", "P02"]},
            "papers": papers,
        },
    )
    return task_ids


class FrozenEnvironmentFixture:
    def __init__(self, parent: Path) -> None:
        self.project = parent / "project"
        self.root = self.project / "paper_bencmark" / "highambench"
        self.metadata = self.root / "metadata"
        self.toolchain = parent / "toolchain"
        self.packages = self.project / ".lake" / "packages"
        self.packages_runtime = parent / "packages-runtime"
        self.library_olean = parent / "library-olean"
        self.shared_olean = parent / "shared-olean"
        self.offline_shell = parent / "offline-shell"
        self.codex = parent / "codex"
        self.auth = parent / "auth.json"
        self.results = parent / "results"
        self._make_files()

    def _make_files(self) -> None:
        benchmark_manifest = {
            "schema_version": "0.1.0",
            "benchmark_id": "test-benchmark",
            "corpus": {"paper_count": 1, "paper_ids": ["P01"]},
            "papers": [
                {
                    "paper_id": "P01",
                    "source": {"sha256": P01_PAPER_SHA256},
                    "targets": [
                        {
                            "task_id": "P01-T1",
                            "tier": "T1",
                            "availability": "available",
                            "lean_target": {
                                "declaration": "p01_t1_fixture",
                                "file": "paper_bencmark/highambench/tasks/P01/T1/Target.lean",
                            },
                        }
                    ],
                }
            ],
        }
        _executable(
            self.codex,
            "#!/bin/sh\n"
            "if [ \"$1\" = features ]; then\n"
            "  echo 'rollout_budget under development false'\n"
            "else\n"
            "  echo 'codex-cli 1.2.3'\n"
            "fi\n",
        )
        _executable(
            self.toolchain / "bin" / "lean",
            "#!/bin/sh\necho 'Lean (version 4.29.0, x86_64-unknown-linux-gnu, "
            f"commit {LEAN_COMMIT}, Release)'\n",
        )
        (self.toolchain / "lib" / "lean").mkdir(parents=True)
        (self.toolchain / "lib" / "lean" / "Init.olean").write_bytes(b"lean")
        mathlib_olean = self.packages / "mathlib" / ".lake" / "build" / "lib" / "lean"
        mathlib_olean.mkdir(parents=True)
        (mathlib_olean / "Mathlib.olean").write_bytes(b"mathlib")
        (mathlib_olean / "Mathlib.olean.server").write_bytes(b"server")
        (mathlib_olean / "Mathlib.olean.private").write_bytes(b"private")
        (mathlib_olean / "Mathlib.ir").write_bytes(b"ir")
        (mathlib_olean / "Mathlib.trace").write_bytes(b"not exposed")
        (self.packages / "mathlib" / "Mathlib").mkdir()
        (self.packages / "mathlib" / "Mathlib.lean").write_text(
            "import Mathlib.Basic\n", encoding="utf-8"
        )
        (self.packages / "mathlib" / "Mathlib" / "Basic.lean").write_text(
            "def fixture := 1\n", encoding="utf-8"
        )

        (self.project / "NumStability").mkdir(parents=True)
        (self.project / "NumStability" / "Basic.lean").write_text("def x := 1\n", encoding="utf-8")
        (self.project / "NumStability.lean").write_text(
            "import NumStability.Basic\n", encoding="utf-8"
        )
        (self.library_olean / "NumStability").mkdir(parents=True)
        (self.library_olean / "NumStability" / "Basic.olean").write_bytes(b"ns")
        (self.shared_olean / "HighamBench").mkdir(parents=True)
        (self.shared_olean / "HighamBench" / "Definitions.olean").write_bytes(b"shared-olean")
        self.offline_shell.write_bytes(b"offline")
        self.auth.write_text("{}\n", encoding="utf-8")

        for relative in run_matrix.required_release_files(benchmark_manifest):
            path = self.root / relative
            if path.exists():
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            if relative == "agent_prompt.md":
                path.write_text("prove the target\n", encoding="utf-8")
            elif relative == "shared/HighamBench/Definitions.lean":
                path.write_text("namespace HighamBench\nend HighamBench\n", encoding="utf-8")
            else:
                path.write_text(f"fixture {relative}\n", encoding="utf-8")

        write_json(self.metadata / "manifest.json", benchmark_manifest)
        write_json(
            self.root / "tasks" / "P01" / "paper.json",
            {
                "paper_id": "P01",
                "source": {"sha256": P01_PAPER_SHA256},
                "included_tasks": ["P01-T1"],
            },
        )
        write_json(
            self.root / "tasks" / "P01" / "T1" / "task.json",
            {
                "task_id": "P01-T1",
                "paper_id": "P01",
                "tier": "T1",
                "paper_source": {"sha256": P01_PAPER_SHA256},
                "context_file": "paper_bencmark/highambench/tasks/P01/T1/context.md",
                "formal_statement": {
                    "namespace": "HighamBench",
                    "theorem_name": "p01_t1_fixture",
                    "target_file": "paper_bencmark/highambench/tasks/P01/T1/Target.lean",
                },
                "validation": {
                    "required_declaration": "HighamBench.p01_t1_fixture",
                    "controlled_target_file": "paper_bencmark/highambench/tasks/P01/T1/Target.lean",
                },
            },
        )
        write_json(
            self.metadata / "run_order.json",
            {"schema_version": 1, "benchmark_id": "test-benchmark", "pairs": []},
        )
        write_json(
            self.metadata / "library_source.json",
            create_manifest(
                self.project,
                requested=["NumStability", "NumStability.lean"],
                label="source",
            ),
        )
        write_json(
            self.metadata / "library_olean.json",
            create_manifest(self.library_olean, label="compiled-library"),
        )
        packages_runtime_manifest = create_manifest(
            self.packages,
            requested=sorted(run_matrix.expected_packages_runtime_files(self.packages)),
            label="packages-runtime",
        )
        write_json(
            self.metadata / "packages_runtime.json", packages_runtime_manifest
        )
        stage_manifest_files(
            self.packages, self.packages_runtime, packages_runtime_manifest
        )
        with mock.patch.object(run_matrix, "_git_head", return_value=MATHLIB_COMMIT), mock.patch.object(
            run_matrix, "_require_git_sources_clean"
        ):
            compiled = run_matrix.compiled_environment_summary(self.toolchain, self.packages)
        write_json(self.metadata / "packages_olean.json", compiled)

        release_paths = sorted(run_matrix._release_tree_files(self.root))
        write_json(
            self.metadata / "release_files.json",
            create_manifest(
                self.root,
                requested=release_paths,
                label="evaluation-package-snapshot",
            ),
        )

        prompt_sha = sha256_file(self.root / "agent_prompt.md")
        source_sha = sha256_file(self.metadata / "library_source.json")
        library_sha = sha256_file(self.metadata / "library_olean.json")
        packages_sha = sha256_file(self.metadata / "packages_olean.json")
        packages_runtime_sha = sha256_file(self.metadata / "packages_runtime.json")
        release_sha = sha256_file(self.metadata / "release_files.json")
        bundle_placeholder = "0" * 64
        frozen = {
            "lean_toolchain": "leanprover/lean4:v4.29.0",
            "lean_commit": LEAN_COMMIT,
            "lean_binary_sha256": sha256_file(self.toolchain / "bin" / "lean"),
            "mathlib_commit": MATHLIB_COMMIT,
            "numstability_commit": NUMSTABILITY_COMMIT,
            "agent_id": "codex-cli",
            "agent_version": "1.2.3",
            "agent_binary_sha256": sha256_file(self.codex),
            "model_version": "test-model",
            "model_reasoning_effort": "medium",
            "prompt_sha256": prompt_sha,
            "allowed_tools": ["shell", "Lean"],
            "hardware_class": "fixture host",
            "operating_system": "fixture",
            "bubblewrap_binary_sha256": sha256_file(Path("/bin/bwrap")),
            "bubblewrap_version": "bubblewrap 0.6.1",
            "numstability_source_manifest": "paper_bencmark/highambench/metadata/library_source.json",
            "numstability_source_manifest_sha256": source_sha,
            "numstability_compiled_manifest": "paper_bencmark/highambench/metadata/library_olean.json",
            "numstability_compiled_manifest_sha256": library_sha,
            "compiled_environment_summary": "paper_bencmark/highambench/metadata/packages_olean.json",
            "compiled_environment_summary_sha256": packages_sha,
            "packages_runtime_manifest": run_matrix.FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH,
            "packages_runtime_manifest_sha256": packages_runtime_sha,
            "python_version": platform.python_version(),
            "python_binary_sha256": sha256_file(Path(sys.executable)),
            "release_manifest": run_matrix.FROZEN_RELEASE_MANIFEST_PATH,
            "release_manifest_sha256": release_sha,
            "environment_id": "placeholder",
            "environment_bundle_sha256": bundle_placeholder,
            "container_image_digest": "sha256:" + "f" * 64,
        }
        config = {
            "schema_version": "0.1.0",
            "benchmark_id": "test-benchmark",
            "frozen_environment": frozen,
            "limits": {
                "wall_clock_seconds": 10,
                "total_model_tokens": 100,
                "failure_scored_time_seconds": 10,
            },
        }
        environment = {
            "schema_version": "0.1.0",
            "kind": "highambench-environment-record",
            "environment_id": "placeholder",
            "environment_bundle_sha256": bundle_placeholder,
            "environment_bundle_definition": run_matrix.ENVIRONMENT_BUNDLE_DEFINITION,
            "release_manifest": run_matrix.FROZEN_RELEASE_MANIFEST_PATH,
            "release_manifest_sha256": release_sha,
            "lean": {
                "version": "4.29.0",
                "commit": LEAN_COMMIT,
                "binary_sha256": frozen["lean_binary_sha256"],
                "mathlib_commit": MATHLIB_COMMIT,
                "numstability_commit": NUMSTABILITY_COMMIT,
                "numstability_source_manifest": frozen["numstability_source_manifest"],
                "numstability_source_manifest_sha256": source_sha,
                "numstability_compiled_manifest": frozen["numstability_compiled_manifest"],
                "numstability_compiled_manifest_sha256": library_sha,
                "compiled_environment_summary": frozen["compiled_environment_summary"],
                "compiled_environment_summary_sha256": packages_sha,
                "shared_definitions_sha256": sha256_file(
                    self.root / "shared" / "HighamBench" / "Definitions.lean"
                ),
                "shared_definitions_olean_sha256": sha256_file(
                    self.shared_olean / "HighamBench" / "Definitions.olean"
                ),
            },
            "agent": {
                "id": "codex-cli",
                "version": "1.2.3",
                "binary_sha256": sha256_file(self.codex),
                "model": "test-model",
                "reasoning_effort": "medium",
                "prompt_sha256": prompt_sha,
            },
            "isolation": {
                "filesystem_adapter_sha256": sha256_file(self.root / "tools" / "codex_isolated.py"),
                "lean_adapter_sha256": sha256_file(self.root / "tools" / "lean_isolated.py"),
                "offline_shell_source_sha256": sha256_file(self.root / "tools" / "offline_shell.c"),
                "offline_shell_binary_sha256": sha256_file(self.offline_shell),
                "runner_sha256": sha256_file(self.root / "tools" / "runner.py"),
                "validator_sha256": sha256_file(self.root / "tools" / "validator.py"),
                "dependency_audit_sha256": sha256_file(
                    self.root / "tools" / "dependency_audit.lean"
                ),
                "bubblewrap_binary_sha256": frozen["bubblewrap_binary_sha256"],
                "bubblewrap_version": frozen["bubblewrap_version"],
            },
            "runtime": {
                "python": {
                    "version": frozen["python_version"],
                    "binary_sha256": frozen["python_binary_sha256"],
                },
                "packages_runtime_manifest": frozen["packages_runtime_manifest"],
                "packages_runtime_manifest_sha256": packages_runtime_sha,
            },
            "host_class": {
                "kernel": "fixture",
                "virtualization": "LXC",
                "processor": "fixture",
                "online_logical_cpus": 1,
                "visible_memory_bytes": 1,
            },
        }
        bundle = run_matrix.environment_bundle_digest(config, environment)
        environment_id = f"highambench-p01-{bundle[:16]}"
        frozen["environment_id"] = environment_id
        frozen["environment_bundle_sha256"] = bundle
        environment["environment_id"] = environment_id
        environment["environment_bundle_sha256"] = bundle
        write_json(self.metadata / "config.json", config)
        write_json(self.metadata / "environment.json", environment)

    def args(self) -> argparse.Namespace:
        return argparse.Namespace(
            benchmark_root=self.root,
            project_root=self.project,
            results_root=self.results,
            codex=self.codex,
            auth_file=self.auth,
            offline_shell=self.offline_shell,
            toolchain_root=self.toolchain,
            packages_root=self.packages,
            packages_runtime_root=self.packages_runtime,
            shared_olean_root=self.shared_olean,
            library_source=self.project / "NumStability",
            library_root_file=self.project / "NumStability.lean",
            library_olean=self.library_olean,
            release_manifest=None,
            agent_id=None,
            agent_version=None,
            model=None,
            reasoning_effort=None,
            time_limit_seconds=None,
            token_limit=None,
            agent_network_verified=True,
            token_control_verified=False,
            force=False,
        )


class RunMatrixTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @mock.patch.object(run_matrix, "_verify_host_class", return_value={"verified": True})
    @mock.patch.object(run_matrix, "_require_git_sources_clean")
    def test_frozen_environment_is_derived_and_rejects_extra_library_olean(
        self, _clean: mock.Mock, _host: mock.Mock
    ) -> None:
        fixture = FrozenEnvironmentFixture(self.base)

        def git_head(path: Path, _label: str) -> str:
            return NUMSTABILITY_COMMIT if path.resolve() == fixture.project.resolve() else MATHLIB_COMMIT

        with mock.patch.object(run_matrix, "_git_head", side_effect=git_head):
            args = fixture.args()
            check = run_matrix.verify_frozen_run_environment(args, fixture.root)
            self.assertTrue(check["ok"])
            self.assertEqual(args.environment_id, check["environment_id"])
            self.assertEqual(args.reasoning_effort, "medium")
            self.assertEqual(args.time_limit_seconds, 10)
            self.assertEqual(
                check["packages_runtime"]["file_count"],
                check["packages_runtime"]["source_file_count"]
                + check["packages_runtime"]["olean_file_count"]
                + check["packages_runtime"]["compiled_support_file_count"],
            )
            self.assertEqual(check["packages_runtime"]["source_file_count"], 2)
            self.assertEqual(check["packages_runtime"]["olean_file_count"], 1)
            self.assertEqual(
                check["packages_runtime"]["compiled_support_file_count"], 3
            )

            (fixture.library_olean / "LeanFpAnalysis.olean").write_bytes(b"leak")
            with self.assertRaisesRegex(Exception, "exact pruned manifest tree"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            (fixture.library_olean / "LeanFpAnalysis.olean").unlink()

            package_leak = (
                fixture.packages
                / "mathlib"
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "Hidden.olean"
            )
            package_leak.write_bytes(b"hidden")
            with self.assertRaisesRegex(Exception, "compiled Lean/package trees"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            package_leak.unlink()

            (fixture.shared_olean / "Hidden.olean").write_bytes(b"hidden")
            with self.assertRaisesRegex(Exception, "shared olean root is not exact"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            (fixture.shared_olean / "Hidden.olean").unlink()

            (fixture.packages_runtime / "Hidden.olean").write_bytes(b"hidden")
            with self.assertRaisesRegex(Exception, "exact frozen manifest tree"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            (fixture.packages_runtime / "Hidden.olean").unlink()

            with mock.patch.object(
                run_matrix.platform, "python_version", return_value="0.0.0"
            ):
                with self.assertRaisesRegex(Exception, "actual Python version"):
                    run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)

            command_args = fixture.args()
            run_matrix.verify_frozen_run_environment(command_args, fixture.root)
            command_args.freeze_check_json = "{}"
            assignment = {
                "pair_id": "P02-T1-rep-01",
                "task_id": "P02-T1",
                "paper_id": "P02",
                "paper_sha256": P02_PAPER_SHA256,
                "tier": "T1",
                "theorem_name": "p02_t1_fixture",
                "required_declaration": "HighamBench.p02_t1_fixture",
                "target_dir": "tasks/P02/T1",
                "target_file": "tasks/P02/T1/Target.lean",
                "context_file": "tasks/P02/T1/context.md",
                "repetition_id": "rep-01",
                "condition": "L",
                "condition_order": ["N", "L"],
                "order_index": 2,
                "run_id": "P02-T1-rep-01-L",
            }
            command = run_matrix.runner_command(
                command_args,
                assignment,
                self.base / "attempt.jsonl",
                self.base / "attempt.json",
                self.base / "base",
            )
            runtime_value = str(fixture.packages_runtime.resolve())
            original_value = str(fixture.packages.resolve())
            nested_commands = [
                json.loads(command[command.index(option) + 1])
                for option in (
                    "--agent-command-json",
                    "--compile-command-json",
                    "--audit-command-json",
                    "--n-probe-command-json",
                )
            ]
            self.assertTrue(
                all(runtime_value in nested for nested in nested_commands)
            )
            self.assertTrue(
                all(original_value not in nested for nested in nested_commands)
            )
            self.assertTrue(command_args.token_control_verified)
            self.assertIn("--token-enforced", command)
            self.assertEqual(command[command.index("--paper-id") + 1], "P02")
            self.assertEqual(
                command[command.index("--paper-sha256") + 1], P02_PAPER_SHA256
            )
            self.assertEqual(
                command[command.index("--canonical-relative") + 1],
                "task/tasks/P02/T1/Target.lean",
            )
            self.assertEqual(
                command[command.index("--target-theorem") + 1],
                "HighamBench.p02_t1_fixture",
            )

            config_path = fixture.metadata / "config.json"
            changed_config = json.loads(config_path.read_text(encoding="utf-8"))
            changed_config["changed_after_freeze"] = True
            write_json(config_path, changed_config)
            with self.assertRaisesRegex(Exception, "canonical config/environment payload"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)

    def test_package_runtime_projection_includes_only_required_split_artifacts(
        self,
    ) -> None:
        fixture = FrozenEnvironmentFixture(self.base)
        files = run_matrix.expected_packages_runtime_files(fixture.packages)
        compiled_prefix = "mathlib/.lake/build/lib/lean/"
        self.assertIn(compiled_prefix + "Mathlib.olean", files)
        self.assertIn(compiled_prefix + "Mathlib.olean.server", files)
        self.assertIn(compiled_prefix + "Mathlib.olean.private", files)
        self.assertIn(compiled_prefix + "Mathlib.ir", files)
        self.assertNotIn(compiled_prefix + "Mathlib.trace", files)
        self.assertEqual(
            len(files),
            sum(path.endswith(".lean") for path in files)
            + sum(path.endswith(".olean") for path in files)
            + sum(
                path.endswith(run_matrix.PACKAGE_COMPILED_SUPPORT_SUFFIXES)
                for path in files
            ),
        )

    def test_exact_tree_digest_changes_for_path_and_content(self) -> None:
        tree = self.base / "tree"
        tree.mkdir()
        (tree / "a").write_bytes(b"one")
        first = run_matrix.exact_tree_digest(tree)
        (tree / "a").write_bytes(b"two")
        second = run_matrix.exact_tree_digest(tree)
        self.assertNotEqual(first["tree_sha256"], second["tree_sha256"])
        (tree / "a").rename(tree / "b")
        third = run_matrix.exact_tree_digest(tree)
        self.assertNotEqual(second["tree_sha256"], third["tree_sha256"])

        (tree / "alias").symlink_to("b")
        fourth = run_matrix.exact_tree_digest(tree)
        self.assertEqual(fourth["regular_file_count"], 1)
        self.assertEqual(fourth["symlink_count"], 1)
        self.assertNotEqual(third["tree_sha256"], fourth["tree_sha256"])
        (tree / "alias").unlink()
        (tree / "alias").symlink_to("missing")
        with self.assertRaisesRegex(Exception, "broken or external symlink"):
            run_matrix.exact_tree_digest(tree)

    def test_run_matrix_keeps_unique_startup_incident_in_rebuilt_jsonl(self) -> None:
        root = self.base / "benchmark"
        project = self.base / "project"
        results = self.base / "results"
        for directory in (
            root / "metadata",
            project,
            self.base / "toolchain",
            self.base / "packages",
            self.base / "packages-runtime",
            self.base / "shared",
            self.base / "library-source",
            self.base / "library-olean",
        ):
            directory.mkdir(parents=True, exist_ok=True)
        for path in (self.base / "codex", self.base / "auth", self.base / "offline", self.base / "root.lean"):
            path.write_text("fixture\n", encoding="utf-8")

        task_ids = _write_two_paper_task_records(root)
        repetitions = ("rep-01", "rep-02", "rep-03")
        write_json(
            root / "metadata" / "config.json",
            {
                "repetitions": [{"id": repetition} for repetition in repetitions],
                "planned_counts_per_agent": {
                    "papers": 2,
                    "tasks": 6,
                    "repetitions_per_task": 3,
                    "conditions": 2,
                    "paired_assignments": 18,
                    "runs": 36,
                },
            },
        )
        pairs = []
        for task in task_ids:
            for repetition in repetitions:
                pair_id = f"{task}-{repetition}"
                pairs.append(
                    {
                        "pair_id": pair_id,
                        "task_id": task,
                        "repetition_id": repetition,
                        "condition_order": ["N", "L"],
                        "run_ids": [f"{pair_id}-N", f"{pair_id}-L"],
                    }
                )
        write_json(root / "metadata" / "run_order.json", {"pairs": pairs})
        manifest = read_json(root / "metadata" / "manifest.json")
        catalog = run_matrix.load_task_catalog(root, manifest)
        self.assertEqual(run_matrix.corpus_slug(manifest), "p01-p02")
        self.assertEqual(len(catalog), 6)
        expanded = run_matrix.assignments_from_order(
            {"pairs": pairs}, catalog, repetitions
        )
        self.assertEqual(len(expanded), 36)
        p02_assignment = next(
            assignment
            for assignment in expanded
            if assignment["task_id"] == "P02-T1"
        )
        self.assertEqual(p02_assignment["paper_sha256"], P02_PAPER_SHA256)
        self.assertEqual(p02_assignment["target_file"], "tasks/P02/T1/Target.lean")
        with self.assertRaisesRegex(Exception, "exact task/repetition matrix"):
            run_matrix.assignments_from_order(
                {"pairs": pairs[:-1]}, catalog, repetitions
            )
        post_use_system_run = pairs[0]["run_ids"][1]
        args = argparse.Namespace(
            benchmark_root=root,
            project_root=project,
            results_root=results,
            codex=self.base / "codex",
            auth_file=self.base / "auth",
            offline_shell=self.base / "offline",
            library_root_file=self.base / "root.lean",
            toolchain_root=self.base / "toolchain",
            packages_root=self.base / "packages",
            packages_runtime_root=self.base / "packages-runtime",
            shared_olean_root=self.base / "shared",
            library_source=self.base / "library-source",
            library_olean=self.base / "library-olean",
            force=False,
        )
        attempts: dict[str, int] = {}

        def fake_command(
            _args: argparse.Namespace,
            assignment: dict,
            _attempt_jsonl: Path,
            attempt_output: Path,
            _base: Path,
        ) -> list[str]:
            return ["fake", json.dumps(assignment), str(attempt_output)]

        def fake_run(command: list[str], **_kwargs: object) -> subprocess.CompletedProcess:
            assignment = json.loads(command[1])
            output = Path(command[2])
            run_id = assignment["run_id"]
            attempts[run_id] = attempts.get(run_id, 0) + 1
            startup_incident = len(attempts) == 1 and attempts[run_id] == 1
            post_use_system = run_id == post_use_system_run
            record = {
                "schema_version": 1,
                "kind": "highambench-run",
                "run_id": run_id,
                "pair_id": assignment["pair_id"],
                "task_id": assignment["task_id"],
                "condition": assignment["condition"],
                "repetition_id": assignment["repetition_id"],
                "pass": not startup_incident and not post_use_system,
                "scored": not startup_incident,
                "failure_code": (
                    "SYSTEM_ERROR" if startup_incident or post_use_system else None
                ),
                "failure_note": (
                    "startup fault"
                    if startup_incident
                    else "post-start fault"
                    if post_use_system
                    else ""
                ),
                "useful_work_started": not startup_incident,
            }
            write_json(output, record)
            return subprocess.CompletedProcess(command, 1 if startup_incident else 0)

        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value={"ok": True, "environment_id": "derived"},
        ), mock.patch.object(run_matrix, "runner_command", side_effect=fake_command), mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ):
            self.assertEqual(run_matrix.run(args), 0)

        rows = [json.loads(line) for line in (results / "runs.jsonl").read_text().splitlines()]
        self.assertEqual(len(rows), 37)
        self.assertEqual(len({row["run_id"] for row in rows}), 37)
        self.assertEqual(rows[0]["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(rows[0]["planned_run_id"], pairs[0]["run_ids"][0])
        self.assertEqual(rows[1]["run_id"], pairs[0]["run_ids"][0])
        self.assertIsNone(rows[1]["failure_code"])
        post_use_row = next(row for row in rows if row["run_id"] == post_use_system_run)
        self.assertEqual(post_use_row["failure_code"], "SYSTEM_ERROR")
        self.assertTrue(post_use_row["useful_work_started"])
        self.assertEqual(attempts[post_use_system_run], 1)


if __name__ == "__main__":
    unittest.main()
