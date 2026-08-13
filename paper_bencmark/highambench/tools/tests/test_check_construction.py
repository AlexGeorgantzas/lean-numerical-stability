from __future__ import annotations

import copy
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from check_construction import (  # noqa: E402
    check_one,
    construction_specs,
    local_helper_sources,
    make_parser,
    promote_current_evidence,
    resolve_environment,
    run_checks,
    verification_basis,
)
from hashes import create_manifest  # noqa: E402
from common import BenchmarkToolError, sha256_file  # noqa: E402


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
        shared_root = self.benchmark / "shared" / "HighamBench"
        shared_root.mkdir(parents=True)
        (shared_root / "Core.lean").write_text(
            "namespace HighamBench\nend HighamBench\n", encoding="utf-8"
        )
        for paper_id in ("P01", "P02"):
            (shared_root / f"{paper_id}Definitions.lean").write_text(
                "import HighamBench.Core\n", encoding="utf-8"
            )

        self.target_names = {
            "P01-T1": "p01_t1_pairwise_nonnegative",
            "P01-T2": "p01_t2_pairwise_vs_recursive_bounds",
            "P01-T3": "p01_t3_noGuard_recursive_running_error_bound",
            "P02-T1": "p02_t1_vecSum_preserves_sum",
            "P02-T2": "p02_t2_sum2_error_bound",
            "P02-T3": "p02_t3_dotK_error_bound",
        }
        metadata = self.benchmark / "metadata"
        metadata.mkdir()
        central_manifest = {
            "controlled_shared_files": [
                {
                    "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                    "paper_ids": ["P01", "P02"],
                    "sha256": sha256_file(shared_root / "Core.lean"),
                },
                *[
                    {
                        "path": (
                            "paper_bencmark/highambench/shared/HighamBench/"
                            f"{paper_id}Definitions.lean"
                        ),
                        "paper_ids": [paper_id],
                        "sha256": sha256_file(
                            shared_root / f"{paper_id}Definitions.lean"
                        ),
                    }
                    for paper_id in ("P01", "P02")
                ],
            ],
            "papers": [
                {
                    "paper_id": paper_id,
                    "targets": [
                        {
                            "task_id": f"{paper_id}-{tier}",
                            "tier": tier,
                            "availability": "available",
                            "lean_target": {
                                "declaration": self.target_names[f"{paper_id}-{tier}"],
                                "file": (
                                    "paper_bencmark/highambench/tasks/"
                                    f"{paper_id}/{tier}/Target.lean"
                                ),
                            },
                        }
                        for tier in ("T1", "T2", "T3")
                    ],
                }
                for paper_id in ("P01", "P02")
            ]
        }
        (metadata / "manifest.json").write_text(
            json.dumps(central_manifest), encoding="utf-8"
        )

        self.private_gold = self.root / "private_gold"
        private_paper = self.private_gold / "P01"
        private_paper.mkdir(parents=True)
        (private_paper / "CommonN.lean").write_text(
            "theorem commonN : True := by trivial\n", encoding="utf-8"
        )
        (private_paper / "CommonL.lean").write_text(
            "theorem commonL : True := by trivial\n", encoding="utf-8"
        )

        controlled = metadata / "controlled"
        controlled.mkdir(parents=True)
        for spec in construction_specs(self.benchmark):
            if spec.condition != "N":
                continue
            task = self.benchmark / "tasks" / spec.paper_id / spec.tier
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
                    "shared/HighamBench/Core.lean",
                    f"shared/HighamBench/{spec.paper_id}Definitions.lean",
                    f"tasks/{spec.paper_id}/{spec.tier}/Target.lean",
                    f"tasks/{spec.paper_id}/{spec.tier}/context.md",
                ],
                label=f"{spec.task_id}-controlled",
            )
            (controlled / f"{spec.task_id}.json").write_text(
                json.dumps(manifest), encoding="utf-8"
            )
            if spec.paper_id == "P01":
                for condition in ("N", "L"):
                    proof = target.replace("sorry", "trivial")
                    if spec.tier in ("T1", "T2"):
                        proof = f"import Common{condition}\n" + proof
                    (private_paper / f"{spec.tier}_{condition}.lean").write_text(
                        proof, encoding="utf-8"
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
        for paper_id in ("P01", "P02"):
            shared_compiled_root = self.shared_olean / paper_id / "HighamBench"
            shared_compiled_root.mkdir(parents=True)
            for name in ("Core", f"{paper_id}Definitions"):
                (shared_compiled_root / f"{name}.olean").write_bytes(
                    f"test shared olean {paper_id} {name}".encode("utf-8")
                )
        (metadata / "environment.json").write_text(
            json.dumps(
                {
                    "lean": {
                        "shared_olean_bundles": {
                            paper_id: {
                                f"HighamBench/{name}.olean": sha256_file(
                                    self.shared_olean
                                    / paper_id
                                    / "HighamBench"
                                    / f"{name}.olean"
                                )
                                for name in ("Core", f"{paper_id}Definitions")
                            }
                            for paper_id in ("P01", "P02")
                        }
                    }
                }
            ),
            encoding="utf-8",
        )
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
                    "--paper-id",
                    "P01",
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
                "regular_file_count": 5,
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

    def complete_promotion_evidence(self) -> dict:
        """Build a lightweight but exact synthetic 20-paper/120-result record."""

        shared_root = self.benchmark / "shared" / "HighamBench"
        papers = []
        controlled_shared_files = [
            {
                "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                "paper_ids": [f"P{index:02d}" for index in range(1, 21)],
                "sha256": sha256_file(shared_root / "Core.lean"),
            }
        ]
        for index in range(1, 21):
            paper_id = f"P{index:02d}"
            shared = shared_root / f"{paper_id}Definitions.lean"
            shared.write_text("import HighamBench.Core\n", encoding="utf-8")
            compiled_root = self.shared_olean / paper_id / "HighamBench"
            compiled_root.mkdir(parents=True, exist_ok=True)
            (compiled_root / "Core.olean").write_bytes(
                f"test shared olean {paper_id} Core".encode("utf-8")
            )
            (compiled_root / f"{paper_id}Definitions.olean").write_bytes(
                f"test shared olean {paper_id} definitions".encode("utf-8")
            )
            controlled_shared_files.append(
                {
                    "path": (
                        "paper_bencmark/highambench/shared/HighamBench/"
                        f"{paper_id}Definitions.lean"
                    ),
                    "paper_ids": [paper_id],
                    "sha256": sha256_file(shared),
                }
            )
            targets = []
            for tier_index in range(1, 4):
                tier = f"T{tier_index}"
                task_id = f"{paper_id}-{tier}"
                declaration = f"{paper_id.lower()}_{tier.lower()}_test"
                task = self.benchmark / "tasks" / paper_id / tier
                task.mkdir(parents=True, exist_ok=True)
                (task / "Target.lean").write_text(
                    "namespace HighamBench\n"
                    f"theorem {declaration} : True := by sorry\n"
                    "end HighamBench\n",
                    encoding="utf-8",
                )
                (task / "context.md").write_text(
                    f"context {task_id}\n", encoding="utf-8"
                )
                controlled = create_manifest(
                    self.benchmark,
                    requested=[
                        "agent_prompt.md",
                        "shared/HighamBench/Core.lean",
                        f"shared/HighamBench/{paper_id}Definitions.lean",
                        f"tasks/{paper_id}/{tier}/Target.lean",
                        f"tasks/{paper_id}/{tier}/context.md",
                    ],
                    label=f"{task_id}-controlled",
                )
                (self.benchmark / "metadata" / "controlled" / f"{task_id}.json").write_text(
                    json.dumps(controlled), encoding="utf-8"
                )
                targets.append(
                    {
                        "task_id": task_id,
                        "tier": tier,
                        "availability": "available",
                        "lean_target": {
                            "declaration": declaration,
                            "file": (
                                "paper_bencmark/highambench/tasks/"
                                f"{paper_id}/{tier}/Target.lean"
                            ),
                        },
                    }
                )
            papers.append({"paper_id": paper_id, "targets": targets})

        central_manifest = {
            "controlled_shared_files": controlled_shared_files,
            "papers": papers,
        }
        central_path = self.benchmark / "metadata" / "manifest.json"
        central_path.write_text(json.dumps(central_manifest), encoding="utf-8")
        specs = tuple(construction_specs(self.benchmark))
        task_ids = list(dict.fromkeys(spec.task_id for spec in specs))
        paper_ids = list(dict.fromkeys(spec.paper_id for spec in specs))
        (self.benchmark / "metadata" / "environment.json").write_text(
            json.dumps(
                {
                    "lean": {
                        "shared_olean_bundles": {
                            paper_id: {
                                relative: sha256_file(
                                    self.shared_olean / paper_id / relative
                                )
                                for relative in (
                                    "HighamBench/Core.olean",
                                    f"HighamBench/{paper_id}Definitions.olean",
                                )
                            }
                            for paper_id in paper_ids
                        }
                    }
                }
            ),
            encoding="utf-8",
        )
        self.promotion_environment = replace(
            self.environment,
            specs=specs,
            manifest_task_ids=tuple(task_ids),
            manifest_paper_ids=tuple(paper_ids),
            selected_paper_ids=tuple(paper_ids),
        )

        results = []
        for spec in specs:
            manifest_sha = sha256_file(
                self.benchmark
                / "metadata"
                / "controlled"
                / f"{spec.task_id}.json"
            )
            dependency = {
                "complete": True,
                "exit_code": 0,
                "forbidden_dependency_count": 0,
                "format_version": 2,
                "library_declarations": (
                    []
                    if spec.condition == "N"
                    else [
                        {
                            "distance": 1,
                            "module": "NumStability.Example",
                            "name": "NumStability.example",
                        }
                    ]
                ),
                "library_use": spec.condition == "L",
                "local_modules": ["Submission"],
                "missing_helper_modules": [],
                "semantic_type_check": {
                    "candidate": spec.target_theorem,
                    "equal": True,
                    "expected": "HighamBench.generatedExpected",
                },
            }
            preflight = None
            if spec.condition == "N":
                preflight = {
                    "complete": True,
                    "controlled_files_verified_after_staging": {
                        "changed": [],
                        "expected": 5,
                        "missing": [],
                        "ok": True,
                        "verified": 5,
                    },
                    "controlled_manifest_sha256": manifest_sha,
                    "filesystem_leaks": [],
                    "import_probe": {
                        "attempted": True,
                        "importable": False,
                        "reliable": True,
                        "system_error": None,
                        "timed_out": False,
                    },
                    "ok": True,
                }
            results.append(
                {
                    "task_id": spec.task_id,
                    "paper_id": spec.paper_id,
                    "tier": spec.tier,
                    "condition": spec.condition,
                    "target_theorem": spec.target_theorem,
                    "pass": True,
                    "reasons": [],
                    "manifest_sha256": manifest_sha,
                    "gold_source_sha256": "a" * 64,
                    "helpers": [],
                    "condition_n_library_arguments_omitted": spec.condition == "N",
                    "n_preflight": preflight,
                    "validation": {
                        "compile_exit_code": 0,
                        "compile_timed_out": False,
                        "controlled_after_audit_ok": True,
                        "controlled_after_compile_ok": True,
                        "controlled_after_expected_compile_ok": True,
                        "controlled_before_ok": True,
                        "controlled_hidden_ok": True,
                        "dependency_audit": dependency,
                        "failure_code": None,
                        "note": "accepted by hidden Lean validation",
                        "pass": True,
                        "semantic_statement_equal": True,
                        "statement_unchanged": True,
                        "static_finding_count": 0,
                    },
                }
            )

        return {
            "schema_version": 1,
            "kind": "highambench-private-construction-check",
            "generated_at_utc": "2026-08-11T00:00:00+00:00",
            "execution": {
                "jobs": 4,
                "result_order": "central manifest order, N then L per task",
            },
            "pass": True,
            "record_status": "current_final",
            "scope": {
                "central_manifest": "metadata/manifest.json",
                "central_manifest_sha256": sha256_file(central_path),
                "manifest_paper_ids": paper_ids,
                "manifest_available_task_ids": task_ids,
                "selected_paper_ids": paper_ids,
                "selected_task_ids": task_ids,
                "complete_manifest_scope": True,
            },
            "summary": {
                "expected": 120,
                "checked": 120,
                "passed": 120,
                "condition_n_passed": 60,
                "condition_l_passed": 60,
            },
            "isolation": {
                "fresh_workspace_per_result": True,
                "controlled_task_staged_under": "task/",
                "private_gold_staged_as": "Submission.lean",
                "private_helper_oleans_reused": False,
                "condition_n_numstability_mounts_configured": False,
                "condition_n_preflight_after_complete_controlled_staging": True,
                "condition_l_numstability_mounts_configured": True,
                "validator_hidden_rebuild": True,
            },
            "verification_basis": verification_basis(self.promotion_environment),
            "results": results,
        }

    def write_promotion_candidate(self, evidence: dict, name: str = "candidate.json") -> Path:
        path = self.root / name
        path.write_text(
            json.dumps(evidence, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return path

    def test_paper_selector_and_import_driven_helpers_use_generic_rules(self) -> None:
        specs = construction_specs(self.benchmark, paper_ids=["P01"])
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
        helpers = {
            (item.task_id, item.condition): local_helper_sources(
                self.private_gold / item.paper_id,
                self.private_gold / item.paper_id / item.gold_filename,
            )
            for item in specs
        }
        self.assertEqual(sum(bool(value) for value in helpers.values()), 4)
        self.assertTrue(
            all(not value for (task_id, _condition), value in helpers.items() if task_id.endswith("-T3"))
        )

    def test_manifest_discovery_includes_p02_task_specific_theorems(self) -> None:
        specs = construction_specs(self.benchmark)
        self.assertEqual(len(specs), 12)
        self.assertEqual(
            [(item.task_id, item.condition) for item in specs],
            [
                (f"{paper_id}-{tier}", condition)
                for paper_id in ("P01", "P02")
                for tier in ("T1", "T2", "T3")
                for condition in ("N", "L")
            ],
        )
        for spec in specs:
            self.assertEqual(
                spec.target_theorem,
                f"HighamBench.{self.target_names[spec.task_id]}",
            )
            self.assertEqual(
                spec.canonical_relative,
                f"tasks/{spec.paper_id}/{spec.tier}/Target.lean",
            )

    def test_p02_spec_drives_validator_paths_with_synthetic_unit_source(self) -> None:
        spec = next(
            item
            for item in construction_specs(self.benchmark, paper_ids=["P02"])
            if item.task_id == "P02-T2" and item.condition == "N"
        )
        private_p02 = self.private_gold / "P02"
        private_p02.mkdir()
        (private_p02 / spec.gold_filename).write_text(
            "namespace HighamBench\n"
            f"theorem {self.target_names[spec.task_id]} : True := by trivial\n"
            "end HighamBench\n",
            encoding="utf-8",
        )
        captured = []

        def fake_validator(config):
            captured.append(config)
            return self.successful_validation(config)

        result = check_one(
            self.environment,
            spec,
            validator_fn=fake_validator,
            preflight_fn=self.successful_preflight,
        )
        self.assertTrue(result["pass"], result)
        self.assertEqual(result["paper_id"], "P02")
        self.assertEqual(result["target_theorem"], "HighamBench.p02_t2_sum2_error_bound")
        self.assertEqual(len(captured), 1)
        self.assertEqual(
            captured[0].canonical_relative,
            "task/tasks/P02/T2/Target.lean",
        )
        self.assertEqual(
            captured[0].target_theorem,
            "HighamBench.p02_t2_sum2_error_bound",
        )

    def test_default_full_scope_rejects_missing_p02_gold(self) -> None:
        arguments = make_parser().parse_args(
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
                "--bwrap",
                str(self.bwrap),
            ]
        )
        with self.assertRaisesRegex(
            BenchmarkToolError,
            r"private construction material is missing.*P02-T1/N proof.*P02-T3/L proof",
        ):
            resolve_environment(arguments)

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
        self.assertEqual(evidence["summary"]["expected"], 6)
        self.assertEqual(
            evidence["scope"]["manifest_available_task_ids"],
            ["P01-T1", "P01-T2", "P01-T3", "P02-T1", "P02-T2", "P02-T3"],
        )
        self.assertEqual(evidence["scope"]["selected_paper_ids"], ["P01"])
        self.assertEqual(
            evidence["scope"]["selected_task_ids"],
            ["P01-T1", "P01-T2", "P01-T3"],
        )
        self.assertFalse(evidence["scope"]["complete_manifest_scope"])
        self.assertEqual(len(helper_commands), 4)
        self.assertEqual(len(validation_configs), 6)
        self.assertEqual(
            {config.canonical_relative for config in validation_configs},
            {
                "task/tasks/P01/T1/Target.lean",
                "task/tasks/P01/T2/Target.lean",
                "task/tasks/P01/T3/Target.lean",
            },
        )
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
        self.assertEqual(basis["shared_olean"]["exact_file_count"], 4)
        self.assertEqual(
            set(basis["shared_olean"]["bundles"]),
            {"P01", "P02"},
        )
        self.assertEqual(
            set(basis["shared_olean"]["bundles"]["P01"]),
            {
                "HighamBench/Core.olean",
                "HighamBench/P01Definitions.olean",
            },
        )
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
                self.assertEqual(
                    command[command.index("--shared-olean-root") + 1],
                    str(self.shared_olean / "P01"),
                )
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

    def test_complete_current_promotion_installs_certificate_and_both_pointers(self) -> None:
        evidence = self.complete_promotion_evidence()
        candidate = self.write_promotion_candidate(evidence)
        (self.benchmark / "metadata" / "evidence").mkdir()
        promoted = promote_current_evidence(self.promotion_environment, candidate)

        evidence_root = self.benchmark / "metadata" / "evidence"
        certificate = evidence_root / "construction_validation_full_current.json"
        n_pointer = json.loads(
            (evidence_root / "condition_n_preflight.json").read_text(encoding="utf-8")
        )
        l_pointer = json.loads(
            (evidence_root / "library_dependency_probe.json").read_text(encoding="utf-8")
        )
        certificate_sha = hashlib.sha256(certificate.read_bytes()).hexdigest()
        self.assertEqual(json.loads(certificate.read_text(encoding="utf-8")), evidence)
        self.assertEqual(promoted["certificate_sha256"], certificate_sha)
        self.assertEqual(promoted["paper_count"], 20)
        self.assertEqual(promoted["task_count"], 60)
        self.assertEqual(promoted["result_count"], 120)
        self.assertEqual(promoted["condition_n_preflight_count"], 60)
        self.assertEqual(promoted["condition_l_library_dependency_count"], 60)
        for pointer in (n_pointer, l_pointer):
            self.assertEqual(pointer["current_evidence_sha256"], certificate_sha)
            self.assertEqual(
                pointer["current_evidence"],
                "paper_bencmark/highambench/metadata/evidence/"
                "construction_validation_full_current.json",
            )
            self.assertEqual(
                pointer["status"], "current complete-corpus construction evidence"
            )
        self.assertEqual(n_pointer["current_result"]["condition_n_tasks_checked"], 60)
        self.assertEqual(
            l_pointer["current_result"]["condition_l_passed_proofs_using_numstability"],
            60,
        )
        self.assertEqual(
            list(evidence_root.glob(".*.promote-*")),
            [],
        )

    def test_current_promotion_rejects_tamper_without_touching_destinations(self) -> None:
        evidence = self.complete_promotion_evidence()
        evidence_root = self.benchmark / "metadata" / "evidence"
        evidence_root.mkdir()
        destinations = [
            evidence_root / "construction_validation_full_current.json",
            evidence_root / "condition_n_preflight.json",
            evidence_root / "library_dependency_probe.json",
        ]
        for index, destination in enumerate(destinations):
            destination.write_text(f"old-{index}\n", encoding="utf-8")
        before = {path: path.read_bytes() for path in destinations}

        n_index = next(
            index
            for index, result in enumerate(evidence["results"])
            if result["condition"] == "N"
        )
        l_index = next(
            index
            for index, result in enumerate(evidence["results"])
            if result["condition"] == "L"
        )
        cases = []
        bad_summary = copy.deepcopy(evidence)
        bad_summary["summary"]["passed"] = 119
        cases.append(("summary", bad_summary, "120/120"))
        bad_manifest = copy.deepcopy(evidence)
        bad_manifest["results"][0]["manifest_sha256"] = "f" * 64
        cases.append(("controlled", bad_manifest, "failed or stale"))
        bad_preflight = copy.deepcopy(evidence)
        bad_preflight["results"][n_index]["n_preflight"]["import_probe"][
            "reliable"
        ] = False
        cases.append(("preflight", bad_preflight, "isolation preflight"))
        bad_dependency = copy.deepcopy(evidence)
        bad_dependency["results"][l_index]["validation"]["dependency_audit"][
            "library_use"
        ] = False
        cases.append(("dependency", bad_dependency, "NumStability use"))
        bad_tool = copy.deepcopy(evidence)
        bad_tool["verification_basis"]["tools"]["tools/validator.py"] = "f" * 64
        cases.append(("tool", bad_tool, "changed after certification"))
        bad_runtime_basis = copy.deepcopy(evidence)
        bad_runtime_basis["verification_basis"]["packages_runtime"]["file_count"] += 1
        cases.append(
            (
                "runtime-basis",
                bad_runtime_basis,
                "verification basis does not exactly match",
            )
        )
        bad_top_level = copy.deepcopy(evidence)
        bad_top_level["unexpected"] = True
        cases.append(("top-level", bad_top_level, "noncanonical top-level"))

        for name, tampered, error in cases:
            with self.subTest(name=name):
                candidate = self.write_promotion_candidate(
                    tampered, f"candidate-{name}.json"
                )
                with self.assertRaisesRegex(BenchmarkToolError, error):
                    promote_current_evidence(self.promotion_environment, candidate)
                self.assertEqual(
                    {path: path.read_bytes() for path in destinations}, before
                )

    def test_current_promotion_fails_closed_on_symlink_paths(self) -> None:
        evidence = self.complete_promotion_evidence()
        candidate = self.write_promotion_candidate(evidence)
        evidence_root = self.benchmark / "metadata" / "evidence"
        evidence_root.mkdir()
        certificate = evidence_root / "construction_validation_full_current.json"
        certificate.write_text("old-certificate\n", encoding="utf-8")
        symlink_target = self.root / "outside-pointer.json"
        symlink_target.write_text("outside\n", encoding="utf-8")
        pointer = evidence_root / "condition_n_preflight.json"
        pointer.symlink_to(symlink_target)

        with self.assertRaisesRegex(BenchmarkToolError, "may not be a symlink"):
            promote_current_evidence(self.promotion_environment, candidate)
        self.assertEqual(certificate.read_text(encoding="utf-8"), "old-certificate\n")
        self.assertEqual(symlink_target.read_text(encoding="utf-8"), "outside\n")

        candidate_link = self.root / "candidate-link.json"
        candidate_link.symlink_to(candidate)
        pointer.unlink()
        with self.assertRaisesRegex(BenchmarkToolError, "regular non-symlink"):
            promote_current_evidence(self.promotion_environment, candidate_link)

    def test_current_promotion_rolls_back_if_one_replace_fails(self) -> None:
        evidence = self.complete_promotion_evidence()
        candidate = self.write_promotion_candidate(evidence)
        evidence_root = self.benchmark / "metadata" / "evidence"
        evidence_root.mkdir()
        destinations = [
            evidence_root / "construction_validation_full_current.json",
            evidence_root / "condition_n_preflight.json",
            evidence_root / "library_dependency_probe.json",
        ]
        for index, destination in enumerate(destinations):
            destination.write_text(f"old-{index}\n", encoding="utf-8")
        before = {path: path.read_bytes() for path in destinations}

        import check_construction as construction_module

        real_replace = construction_module.os.replace
        destination_set = {path.resolve() for path in destinations}
        promotion_replaces = 0
        failed_once = False

        def fail_second_promotion_replace(source, destination):
            nonlocal promotion_replaces, failed_once
            if Path(destination).resolve() in destination_set and not failed_once:
                promotion_replaces += 1
                if promotion_replaces == 2:
                    failed_once = True
                    raise OSError("injected second-document replacement failure")
            return real_replace(source, destination)

        with patch.object(
            construction_module.os,
            "replace",
            side_effect=fail_second_promotion_replace,
        ):
            with self.assertRaisesRegex(BenchmarkToolError, "promotion failed"):
                promote_current_evidence(self.promotion_environment, candidate)
        self.assertEqual({path: path.read_bytes() for path in destinations}, before)
        self.assertEqual(list(evidence_root.glob(".*.promote-*")), [])

    def test_promote_current_cli_flag_is_explicit(self) -> None:
        arguments = make_parser().parse_args(
            [
                "--project-root",
                str(self.project),
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
                "--output",
                str(self.root / "new-certificate.json"),
                "--promote-current",
            ]
        )
        self.assertTrue(arguments.promote_current)
        self.assertEqual(arguments.output, self.root / "new-certificate.json")

    def test_failed_complete_n_preflight_blocks_private_proof_validation(self) -> None:
        spec = next(
            item
            for item in construction_specs(self.benchmark, paper_ids=["P01"])
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
            for item in construction_specs(self.benchmark, paper_ids=["P01"])
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
