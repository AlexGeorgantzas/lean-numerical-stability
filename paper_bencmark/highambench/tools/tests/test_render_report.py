from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from render_report import (  # noqa: E402
    CONSTRUCTION_TOOL_PATHS,
    PACKAGES_RUNTIME_ROOT,
    PRUNED_LIBRARY_OLEAN_ROOT,
    ReportError,
    load_report_inputs,
    main,
    render_report,
)


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def document_digest(value: dict) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


class ReportFixture:
    def __init__(self, raw: str) -> None:
        self.repo = Path(raw) / "repo"
        self.root = self.repo / "paper_bencmark" / "highambench"
        self.analysis_path = self.repo / "results" / "analysis" / "summary.json"
        self.freeze_path = self.repo / "results" / "freeze_check.json"
        self.output_tex = self.repo / "report.tex"
        self.construction_path = (
            self.root / "metadata" / "evidence" / "construction_validation.json"
        )
        self.library_pointer_path = (
            self.root / "metadata" / "evidence" / "library_dependency_probe.json"
        )
        self._build()

    def _build(self) -> None:
        prompt = b"Use Lean to complete the fixed theorem.\n"
        prompt_path = self.root / "agent_prompt.md"
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_bytes(prompt)
        shared = b"""namespace HighamBench
structure StandardAddModel where
  u : Real
structure NoGuardAddModel where
  u : Real
def gamma := 0
def GammaValid := True
def pairwiseSum := 0
def recursiveSum := 0
def noGuardRecursiveRunningBudget := 0
end HighamBench
"""
        shared_path = self.root / "shared" / "HighamBench" / "Definitions.lean"
        shared_path.parent.mkdir(parents=True, exist_ok=True)
        shared_path.write_bytes(shared)

        targets: list[dict] = []
        task_ids = ["P01-T1", "P01-T2", "P01-T3"]
        for tier, task_id in zip(("T1", "T2", "T3"), task_ids):
            target_bytes = (
                "import HighamBench.Definitions\n"
                f"theorem p01_{tier.lower()}_test : True := by trivial\n"
            ).encode()
            target_path = self.root / "tasks" / "P01" / tier / "Target.lean"
            target_path.parent.mkdir(parents=True, exist_ok=True)
            target_path.write_bytes(target_bytes)
            targets.append(
                {
                    "task_id": task_id,
                    "tier": tier,
                    "tier_name": {"T1": "direct use", "T2": "combine", "T3": "extend"}[tier],
                    "availability": "available",
                    "title": f"Fixture result {tier}",
                    "tier_reason": f"Fixture reason for {tier}.",
                    "source_locations": [
                        {
                            "section": f"Section {tier}",
                            "anchor": f"equation ({tier[-1]}.1)",
                            "journal_page": 780 + int(tier[-1]),
                            "pdf_page": int(tier[-1]),
                            "role": "fixture source anchor",
                        }
                    ],
                    "lean_target": {
                        "declaration": f"p01_{tier.lower()}_test",
                        "file": f"paper_bencmark/highambench/tasks/P01/{tier}/Target.lean",
                        "controlled_file_sha256": digest_bytes(target_bytes),
                    },
                }
            )
            write_json(
                self.root / "tasks" / "P01" / tier / "task.json",
                {
                    "task_id": task_id,
                    "paper_id": "P01",
                    "tier": tier,
                    "classification_frozen_before_runs": True,
                    "tier_label": targets[-1]["tier_name"],
                    "tier_rationale": targets[-1]["tier_reason"],
                    "informal_statement": f"The chosen {tier} fixture claim.",
                    "source_locations": targets[-1]["source_locations"],
                    "formal_statement": {
                        "theorem_name": f"p01_{tier.lower()}_test",
                        "lean_header": f"theorem p01_{tier.lower()}_test : True",
                        "plain_language": f"The {tier} fixture statement is true.",
                    },
                },
            )

        paper_hash = "a" * 64
        spec_hash = "b" * 64
        paper = {
            "paper_id": "P01",
            "classification_frozen_before_runs": True,
            "title": "The Accuracy of Floating Point Summation",
            "authors": ["Nicholas J. Higham"],
            "source": {
                "local_path": "paper_bencmark/reference_papers/paper.pdf",
                "sha256": paper_hash,
            },
            "benchmark_specification": {
                "local_path": "paper_bencmark/scratch_pad/spec.pdf",
                "sha256": spec_hash,
            },
        }
        write_json(self.root / "tasks" / "P01" / "paper.json", paper)

        benchmark_id = "fixture-p01"
        manifest = {
            "benchmark_id": benchmark_id,
            "specification": {
                "local_path": "paper_bencmark/scratch_pad/spec.pdf",
                "sha256": spec_hash,
            },
            "controlled_shared_files": [
                {
                    "path": "paper_bencmark/highambench/shared/HighamBench/Definitions.lean",
                    "sha256": digest_bytes(shared),
                }
            ],
            "papers": [
                {
                    "paper_id": "P01",
                    "citation": {
                        "author": "Nicholas J. Higham",
                        "title": "The Accuracy of Floating Point Summation",
                    },
                    "source": {
                        "local_path": "paper_bencmark/reference_papers/paper.pdf",
                        "sha256": paper_hash,
                        "rights_note": "Fixture source; do not redistribute.",
                    },
                    "targets": targets,
                }
            ],
        }
        tool_hashes: dict[str, str] = {}
        for index, relative in enumerate(CONSTRUCTION_TOOL_PATHS, start=1):
            tool_path = self.root / relative
            tool_path.parent.mkdir(parents=True, exist_ok=True)
            tool_path.write_bytes(f"fixture checker {index}: {relative}\n".encode())
            tool_hashes[relative] = digest_bytes(tool_path.read_bytes())

        source_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "NumStability source",
            "files": [
                {"path": "NumStability.lean", "sha256": "1" * 64, "bytes": 101},
                {
                    "path": "NumStability/Fixture.lean",
                    "sha256": "2" * 64,
                    "bytes": 202,
                },
            ],
        }
        compiled_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "compiled NumStability",
            "files": [
                {
                    "path": "NumStability/Fixture.olean",
                    "sha256": "3" * 64,
                    "bytes": 303,
                }
            ],
        }
        packages_runtime_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "pruned package runtime",
            "files": [
                {"path": "mathlib/Mathlib.lean", "sha256": "a" * 64, "bytes": 10},
                {
                    "path": "mathlib/Mathlib/Fixture.lean",
                    "sha256": "b" * 64,
                    "bytes": 20,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean",
                    "sha256": "c" * 64,
                    "bytes": 30,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean.server",
                    "sha256": "d" * 64,
                    "bytes": 40,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean.private",
                    "sha256": "e" * 64,
                    "bytes": 50,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.ir",
                    "sha256": "f" * 64,
                    "bytes": 60,
                },
            ],
        }
        compiled_summary = {
            "schema_version": 1,
            "kind": "highambench-compiled-environment-summary",
            "toolchain": {
                "relative_root": ".",
                "file_count": 7,
                "total_bytes": 700,
                "tree_sha256": "4" * 64,
            },
            "packages": [
                {
                    "package": "mathlib",
                    "relative_root": "mathlib/.lake/build/lib/lean",
                    "git_commit": "5" * 40,
                    "file_count": 11,
                    "total_bytes": 1100,
                    "tree_sha256": "6" * 64,
                }
            ],
        }
        source_manifest_path = self.root / "metadata" / "library_source.json"
        compiled_manifest_path = self.root / "metadata" / "library_olean.json"
        compiled_summary_path = self.root / "metadata" / "packages_olean.json"
        packages_runtime_path = self.root / "metadata" / "packages_runtime.json"
        write_json(source_manifest_path, source_manifest)
        write_json(compiled_manifest_path, compiled_manifest)
        write_json(compiled_summary_path, compiled_summary)
        write_json(packages_runtime_path, packages_runtime_manifest)
        source_manifest_sha = digest_bytes(source_manifest_path.read_bytes())
        compiled_manifest_sha = digest_bytes(compiled_manifest_path.read_bytes())
        compiled_summary_sha = digest_bytes(compiled_summary_path.read_bytes())
        packages_runtime_sha = digest_bytes(packages_runtime_path.read_bytes())

        def release_entry(relative: str) -> dict:
            path = self.root / relative
            value = path.read_bytes()
            return {"path": relative, "sha256": digest_bytes(value), "bytes": len(value)}

        release_paths = list(CONSTRUCTION_TOOL_PATHS) + [
            "metadata/library_source.json",
            "metadata/library_olean.json",
            "metadata/packages_olean.json",
            "metadata/packages_runtime.json",
        ]
        release_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "evaluation release",
            "files": [release_entry(relative) for relative in release_paths],
        }
        release_path = self.root / "metadata" / "release_files.json"
        write_json(release_path, release_manifest)
        release_sha = digest_bytes(release_path.read_bytes())

        bundle_sha = "e" * 64
        environment_id = "highambench-p01-" + bundle_sha[:16]
        shared_olean_sha = "7" * 64
        lean_binary_sha = "8" * 64
        bubblewrap_sha = "9" * 64
        python_binary_sha = "f" * 64
        python_version = "3.fixture"
        config = {
            "benchmark_id": benchmark_id,
            "frozen_environment": {
                "environment_id": environment_id,
                "environment_bundle_sha256": bundle_sha,
                "prompt_sha256": digest_bytes(prompt),
                "agent_id": "fixture-agent",
                "agent_version": "1.2.3",
                "agent_binary_sha256": "a" * 64,
                "model_version": "fixture-model",
                "model_reasoning_effort": "medium",
                "python_version": python_version,
                "python_binary_sha256": python_binary_sha,
                "numstability_source_manifest": (
                    "paper_bencmark/highambench/metadata/library_source.json"
                ),
                "numstability_source_manifest_sha256": source_manifest_sha,
                "numstability_compiled_manifest": (
                    "paper_bencmark/highambench/metadata/library_olean.json"
                ),
                "numstability_compiled_manifest_sha256": compiled_manifest_sha,
                "compiled_environment_summary": (
                    "paper_bencmark/highambench/metadata/packages_olean.json"
                ),
                "compiled_environment_summary_sha256": compiled_summary_sha,
                "packages_runtime_manifest": (
                    "paper_bencmark/highambench/metadata/packages_runtime.json"
                ),
                "packages_runtime_manifest_sha256": packages_runtime_sha,
                "release_manifest": (
                    "paper_bencmark/highambench/metadata/release_files.json"
                ),
                "release_manifest_sha256": release_sha,
                "bubblewrap_binary_sha256": bubblewrap_sha,
            },
            "planned_counts_per_agent": {
                "papers": 1,
                "tasks": 3,
                "repetitions_per_task": 3,
                "conditions": 2,
                "paired_assignments": 9,
                "runs": 18,
            },
            "repetitions": [
                {"id": "rep-01", "backend_seed": None},
                {"id": "rep-02", "backend_seed": None},
                {"id": "rep-03", "backend_seed": None},
            ],
            "limits": {"wall_clock_seconds": 900, "total_model_tokens": 120000},
        }
        run_order = {"benchmark_id": benchmark_id, "pairs": []}
        environment = {
            "environment_id": environment_id,
            "environment_bundle_sha256": bundle_sha,
            "release_manifest": "paper_bencmark/highambench/metadata/release_files.json",
            "release_manifest_sha256": release_sha,
            "runtime": {
                "python": {
                    "version": python_version,
                    "binary_sha256": python_binary_sha,
                },
                "packages_runtime_manifest": (
                    "paper_bencmark/highambench/metadata/packages_runtime.json"
                ),
                "packages_runtime_manifest_sha256": packages_runtime_sha,
            },
            "host_class": {
                "kernel": "Fixture Linux",
                "virtualization": "FIXTURE",
                "processor": "Fixture CPU",
                "online_logical_cpus": 4,
                "visible_memory_bytes": 16000000000,
                "visible_memory": "16 GB",
            },
            "lean": {
                "version": "4.fixture",
                "commit": "b" * 40,
                "binary_sha256": lean_binary_sha,
                "mathlib_commit": "c" * 40,
                "numstability_commit": "d" * 40,
                "shared_definitions_olean_sha256": shared_olean_sha,
                "numstability_source_manifest": (
                    "paper_bencmark/highambench/metadata/library_source.json"
                ),
                "numstability_source_manifest_sha256": source_manifest_sha,
                "numstability_compiled_manifest": (
                    "paper_bencmark/highambench/metadata/library_olean.json"
                ),
                "numstability_compiled_manifest_sha256": compiled_manifest_sha,
                "compiled_environment_summary": (
                    "paper_bencmark/highambench/metadata/packages_olean.json"
                ),
                "compiled_environment_summary_sha256": compiled_summary_sha,
            },
            "isolation": {
                "kind": "bubblewrap namespace; not an OCI container",
                "network_boundary": "model shell offline; provider control connection retained",
                "lean_adapter_sha256": tool_hashes["tools/lean_isolated.py"],
                "validator_sha256": tool_hashes["tools/validator.py"],
                "dependency_audit_sha256": tool_hashes["tools/dependency_audit.lean"],
                "bubblewrap_binary_sha256": bubblewrap_sha,
                "bubblewrap_version": "bubblewrap 0.fixture",
            },
            "known_reference_protocol_deviations": [
                "No backend seed is available; repetition IDs are not seeds.",
                "There is no frozen OCI image.",
                "The provider connection remains available to the control process.",
                "Exact token totals arrive at turn completion, after first-valid timing.",
            ],
        }
        write_json(self.root / "metadata" / "manifest.json", manifest)
        write_json(self.root / "metadata" / "config.json", config)
        write_json(self.root / "metadata" / "run_order.json", run_order)
        write_json(self.root / "metadata" / "environment.json", environment)

        write_json(
            self.root / "metadata" / "evidence" / "exact_target_search.json",
            {
                "fixed_surface_hashes": {
                    "shared_definitions": {"sha256": digest_bytes(shared)},
                    **{
                        target["task_id"]: {
                            "sha256": target["lean_target"]["controlled_file_sha256"]
                        }
                        for target in targets
                    },
                },
                "overall_conclusion": {
                    "all_three_exact_targets_absent": True,
                    "all_three_semantic_duplicates_absent": True,
                    "tier_labels_supported_by_library_surface": True,
                },
                "task_findings": [
                    {
                        "task_id": task_id,
                        "exact_duplicate_found": False,
                        "semantic_duplicate_found": False,
                        "tier_assessment": f"{tier} is supported by the fixture search.",
                    }
                    for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
                ],
            },
        )
        construction = {
            "kind": "highambench-private-construction-check",
            "pass": True,
            "summary": {
                "expected": 6,
                "checked": 6,
                "passed": 6,
                "condition_n_passed": 3,
                "condition_l_passed": 3,
            },
            "isolation": {
                "condition_n_preflight_after_complete_controlled_staging": True,
                "condition_n_numstability_mounts_configured": False,
                "condition_l_numstability_mounts_configured": True,
            },
            "verification_basis": {
                "tools": tool_hashes,
                "executables": {
                    "python": {
                        "path": "/usr/bin/python3",
                        "sha256": python_binary_sha,
                        "version": python_version,
                    },
                    "bubblewrap": {"path": "/bin/bwrap", "sha256": bubblewrap_sha},
                },
                "shared_olean": {
                    "relative_file": "HighamBench/Definitions.olean",
                    "sha256": shared_olean_sha,
                    "exact_file_count": 1,
                },
                "numstability_source": {
                    "path": "metadata/library_source.json",
                    "sha256": source_manifest_sha,
                    "label": "NumStability source",
                    "file_count": len(source_manifest["files"]),
                    "total_bytes": sum(item["bytes"] for item in source_manifest["files"]),
                    "verified": len(source_manifest["files"]),
                    "exact_tree": True,
                },
                "numstability_compiled": {
                    "path": "metadata/library_olean.json",
                    "sha256": compiled_manifest_sha,
                    "label": "compiled NumStability",
                    "file_count": len(compiled_manifest["files"]),
                    "total_bytes": sum(item["bytes"] for item in compiled_manifest["files"]),
                    "verified": len(compiled_manifest["files"]),
                    "exact_tree": True,
                    "mount_root": str((self.repo / PRUNED_LIBRARY_OLEAN_ROOT).resolve()),
                    "only_numstability_namespace": True,
                },
                "packages_runtime": {
                    "path": "metadata/packages_runtime.json",
                    "sha256": packages_runtime_sha,
                    "label": "pruned package runtime",
                    "file_count": len(packages_runtime_manifest["files"]),
                    "total_bytes": sum(
                        item["bytes"] for item in packages_runtime_manifest["files"]
                    ),
                    "verified": len(packages_runtime_manifest["files"]),
                    "exact_tree": True,
                    "mount_root": str((self.repo / PACKAGES_RUNTIME_ROOT).resolve()),
                    "only_mathlib_source_and_lean_compiled_artifacts": True,
                    "mathlib_source_file_count": 2,
                    "base_olean_file_count": 1,
                    "compiled_support_file_count": 3,
                },
            },
            "results": [
                {
                    "task_id": task_id,
                    "tier": tier,
                    "condition": condition,
                    "manifest_sha256": ("0" if tier == "T1" else "1" if tier == "T2" else "2") * 64,
                    "condition_n_library_arguments_omitted": condition == "N",
                    "pass": True,
                    "n_preflight": (
                        {
                            "ok": True,
                            "complete": True,
                            "filesystem_leaks": [],
                            "controlled_manifest_sha256": (
                                ("0" if tier == "T1" else "1" if tier == "T2" else "2")
                                * 64
                            ),
                            "controlled_files_verified_after_staging": {
                                "ok": True,
                                "verified": 4,
                                "expected": 4,
                                "missing": [],
                                "changed": [],
                            },
                            "filesystem_scan": {
                                "root": ".",
                                "markers": ["NumStability", "numStability"],
                                "regular_file_count": 4,
                                "directory_count": 3,
                                "symlink_count": 0,
                            },
                            "import_probe": {
                                "attempted": True,
                                "reliable": True,
                                "importable": False,
                            },
                        }
                        if condition == "N"
                        else None
                    ),
                    "validation": {
                        "pass": True,
                        "compile_exit_code": 0,
                        "compile_timed_out": False,
                        "controlled_before_ok": True,
                        "controlled_hidden_ok": True,
                        "failure_code": None,
                        "statement_unchanged": True,
                        "static_finding_count": 0,
                        "dependency_audit": {
                            "complete": True,
                            "exit_code": 0,
                            "format_version": 2,
                            "forbidden_dependency_count": 0,
                            "library_declarations": (
                                [
                                    {
                                        "distance": 1,
                                        "module": "NumStability.Fixture",
                                        "name": f"NumStability.fixture{tier}",
                                    }
                                ]
                                if condition == "L"
                                else []
                            ),
                            "library_use": condition == "L",
                            "local_modules": ["Submission"],
                            "missing_helper_modules": [],
                        },
                    },
                }
                for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
                for condition in ("N", "L")
            ],
        }
        write_json(self.construction_path, construction)
        write_json(
            self.library_pointer_path,
            {
                "schema_version": "0.1.0",
                "kind": "highambench-library-dependency-evidence-pointer",
                "status": "superseded by the complete six-proof construction check",
                "current_evidence": (
                    "paper_bencmark/highambench/metadata/evidence/"
                    "construction_validation.json"
                ),
                "current_evidence_sha256": digest_bytes(
                    self.construction_path.read_bytes()
                ),
                "current_result": {
                    "proofs_checked": 6,
                    "proofs_passed": 6,
                    "condition_l_passed_proofs_using_numstability": 3,
                },
            },
        )
        for number, focus in ((1, "paper meaning and source"), (2, "formal interface and protocol")):
            write_json(
                self.root / "metadata" / "reviews" / f"reviewer_{number}.json",
                {
                    "review_id": f"fixture-review-{number}",
                    "reviewer": {"focus": focus, "kind": "Codex review, not human"},
                    "overall_status": "final pass",
                    "task_reviews": [
                        {"task_id": task_id, "review_outcome": "pass"} for task_id in task_ids
                    ],
                },
            )

        release_count = len(release_manifest["files"])
        freeze_check = {
            "schema_version": 1,
            "kind": "highambench-frozen-run-verification",
            "ok": True,
            "benchmark_id": benchmark_id,
            "environment_id": environment_id,
            "environment_bundle_sha256": bundle_sha,
            "agent": {
                "id": "fixture-agent",
                "version": "1.2.3",
                "binary_sha256": "a" * 64,
                "model": "fixture-model",
                "reasoning_effort": "medium",
            },
            "python": {
                "version": python_version,
                "binary_sha256": python_binary_sha,
            },
            "token_control": {
                "feature": "rollout_budget",
                "feature_row": "rollout_budget under development false",
                "strict_config": True,
                "limit_tokens": 120000,
                "prefill_token_weight": 1,
                "sampling_token_weight": 1,
            },
            "lean": {
                "version": "4.fixture",
                "commit": "b" * 40,
                "binary_sha256": lean_binary_sha,
                "mathlib_commit": "c" * 40,
                "numstability_commit": "d" * 40,
                "source_files_verified": len(source_manifest["files"]),
                "compiled_files_verified": len(compiled_manifest["files"]),
            },
            "host_class": {
                field: environment["host_class"][field]
                for field in (
                    "kernel",
                    "virtualization",
                    "processor",
                    "online_logical_cpus",
                    "visible_memory_bytes",
                )
            },
            "limits": {"wall_clock_seconds": 900, "total_model_tokens": 120000},
            "release_manifest": {
                "path": "metadata/release_files.json",
                "sha256": release_sha,
                "file_count": release_count,
                "verification": {
                    "ok": True,
                    "verified": release_count,
                    "expected": release_count,
                    "missing": [],
                    "changed": [],
                },
            },
            "packages_runtime": {
                "path": "paper_bencmark/highambench/metadata/packages_runtime.json",
                "sha256": packages_runtime_sha,
                "file_count": len(packages_runtime_manifest["files"]),
                "source_file_count": 2,
                "olean_file_count": 1,
                "compiled_support_file_count": 3,
                "verification": {
                    "ok": True,
                    "verified": len(packages_runtime_manifest["files"]),
                    "expected": len(packages_runtime_manifest["files"]),
                    "missing": [],
                    "changed": [],
                },
            },
            "compiled_environment_summary": {
                "path": "paper_bencmark/highambench/metadata/packages_olean.json",
                "sha256": compiled_summary_sha,
                "toolchain_file_count": 7,
                "package_count": 1,
                "package_file_count": 11,
            },
            "bubblewrap": {
                "version": "bubblewrap 0.fixture",
                "binary_sha256": bubblewrap_sha,
            },
            "metadata_document_sha256": {
                "config": document_digest(config),
                "environment": document_digest(environment),
                "manifest": document_digest(manifest),
                "run_order": document_digest(run_order),
            },
        }
        write_json(self.freeze_path, freeze_check)
        freeze_sha = document_digest(freeze_check)

        failure_counts = {code: 0 for code in (
            "TIME_LIMIT",
            "TOKEN_LIMIT",
            "NO_SUBMISSION",
            "RULE_VIOLATION",
            "SYNTAX_OR_ELAB",
            "PROOF_ERROR",
            "SYSTEM_ERROR",
        )}
        failure_counts["PROOF_ERROR"] = 3

        def condition_row(scope: str, condition: str, task_id: str | None = None, tier: str | None = None) -> dict:
            row = {
                "result_status": "observational_not_reference_score",
                "agent_id": "fixture-agent",
                "agent_version": "1.2.3",
                "model": "fixture-model",
                "scope": scope,
                "condition": condition,
                "official_scored_runs": 0,
                "observational_runs": 9 if scope == "overall" else 3,
                "observed_passes": (9 if scope == "overall" else 3) if condition == "L" else 0,
                "observed_pass_rate": 1.0 if condition == "L" else 0.0,
                "median_observed_seconds": 12.5 if condition == "L" else 900.0,
                "median_observed_model_tokens": 1000.0 if condition == "L" else 2000.0,
                "runs_with_token_measurement": 9 if scope == "overall" else 3,
                "observed_passed_library_use": 9 if scope == "overall" and condition == "L" else 3 if condition == "L" else 0,
                "failure_counts": {code: (failure_counts[code] if condition == "N" else 0) for code in failure_counts},
            }
            if task_id is not None:
                row.update({"paper_id": "P01", "task_id": task_id, "tier": tier})
            return row

        condition_rows = [
            condition_row(scope, condition)
            for scope in ("overall", "T1", "T2", "T3")
            for condition in ("N", "L")
        ]
        task_rows = [
            condition_row(task_id, condition, task_id, tier)
            for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
            for condition in ("N", "L")
        ]

        def pair_row(scope: str, task_id: str | None = None, tier: str | None = None) -> dict:
            row = {
                "result_status": "observational_not_reference_score",
                "agent_id": "fixture-agent",
                "agent_version": "1.2.3",
                "model": "fixture-model",
                "scope": scope,
                "condition": "L-N",
                "pairs": 9 if scope == "overall" else 3,
                "observed_pass_rate_change": 1.0,
                "median_observed_paired_time_change": -887.5,
                "median_observed_paired_token_change": -1000.0,
                "pairs_with_token_measurement": 9 if scope == "overall" else 3,
                "bootstrap": {
                    "method": "percentile bootstrap resampling whole papers",
                    "confidence": 0.95,
                    "paper_count": 1,
                    "informative": False,
                    "note": "one-paper resampling is degenerate and does not estimate corpus uncertainty",
                    "ranges": {
                        "pass_rate_change": {"low": 1.0, "high": 1.0},
                        "median_paired_time_change": {"low": -887.5, "high": -887.5},
                        "median_paired_token_change": {"low": -1000.0, "high": -1000.0},
                    },
                },
            }
            if task_id is not None:
                row.update({"paper_id": "P01", "task_id": task_id, "tier": tier})
            return row

        pair_rows = [pair_row(scope) for scope in ("overall", "T1", "T2", "T3")]
        task_pair_rows = [
            pair_row(task_id, task_id, tier)
            for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
        ]

        runs: list[dict] = []
        selected_ids: list[str] = []
        for task_id, tier in zip(task_ids, ("T1", "T2", "T3")):
            for repetition in ("rep-01", "rep-02", "rep-03"):
                for condition in ("N", "L"):
                    run_id = f"{task_id}-{repetition}-{condition}"
                    selected_ids.append(run_id)
                    passed = condition == "L"
                    runs.append(
                        {
                            "agent_id": "fixture-agent",
                            "agent_version": "1.2.3",
                            "model": "fixture-model",
                            "run_id": run_id,
                            "pair_id": f"{task_id}-{repetition}",
                            "paper_id": "P01",
                            "task_id": task_id,
                            "tier": tier,
                            "repetition_id": repetition,
                            "backend_seed": None,
                            "condition": condition,
                            "pair_order": "N-first",
                            "order_index": 1 if condition == "N" else 2,
                            "scored": False,
                            "pass": passed,
                            "actual_stop_seconds": 12.5 if passed else 100.0,
                            "scored_elapsed_seconds": 12.5 if passed else 900.0,
                            "model_tokens": 1000 if passed else 2000,
                            "library_use": passed,
                            "library_declarations": ["NumStability.fixture"] if passed else [],
                            "failure_code": None if passed else "PROOF_ERROR",
                            "failure_note": "" if passed else "fixture proof failure",
                            "protocol_complete": False,
                            "submission_sha256": "d" * 64 if passed else None,
                        }
                    )

        reasons = [
            "backend seeds are unavailable",
            "no frozen OCI image",
            "protocol claim not met: seed_enforced_by_agent",
        ]
        result_check = {
            "kind": "highambench-result-set-check",
            "ok": True,
            "benchmark_id": benchmark_id,
            "metadata_document_sha256": {
                "config": document_digest(config),
                "manifest": document_digest(manifest),
                "run_order": document_digest(run_order),
            },
            "freeze_check_sha256": freeze_sha,
            "network_violation_run_count": 0,
            "network_integrity_failure_count": 0,
            "expected_agents": 1,
            "expected_pairs_per_agent": 9,
            "expected_final_runs_per_agent": 18,
            "input_record_count": 18,
            "selected_final_record_count": 18,
            "official_final_record_count": 0,
            "selected_final_run_ids": selected_ids,
            "analysis_profile": "observational_pilot",
            "reference_compliant": False,
            "official_scores_valid": False,
            "observational_results_allowed": True,
            "nonreference_reasons": reasons,
            "system_error_incident_count": 0,
            "system_error_incidents": [],
            "system_error_issue_count": 0,
            "system_error_issues": [],
            "system_error_handling_complete": True,
            "errors": [],
            "warnings": [],
        }
        analysis = {
            "schema_version": 1,
            "kind": "highambench-analysis",
            "included_unscored": False,
            "input_run_count": 18,
            "analyzed_run_count": 0,
            "excluded_run_count": 18,
            "official_scores_valid": False,
            "result_set_check": result_check,
            "observational_pilot_results": {
                "label": "observational pilot; not a reference-compliant HighamBench score",
                "official_scores_valid": False,
                "nonreference_reasons": reasons,
                "run_count": 18,
                "condition_summaries": condition_rows,
                "per_task_summaries": task_rows,
                "paired_comparisons": pair_rows,
                "per_task_paired_comparisons": task_pair_rows,
            },
            "per_run_results": runs,
            "condition_summaries": [],
            "per_task_summaries": [],
            "paired_comparisons": [],
            "per_task_paired_comparisons": [],
            "pair_problems": [],
            "malformed_input_lines": [],
        }
        write_json(self.analysis_path, analysis)

    def refresh_construction_pointer_digest(self) -> None:
        pointer = json.loads(self.library_pointer_path.read_text(encoding="utf-8"))
        pointer["current_evidence_sha256"] = digest_bytes(
            self.construction_path.read_bytes()
        )
        write_json(self.library_pointer_path, pointer)


class RenderReportTests(unittest.TestCase):
    def test_resolves_authenticated_construction_pointer_and_uses_all_rows(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            inputs = load_report_inputs(fixture.root, fixture.analysis_path)
            self.assertEqual(
                inputs.construction_check.get("kind"),
                "highambench-private-construction-check",
            )
            self.assertEqual(len(inputs.construction_check.get("results", [])), 6)
            latex = render_report(inputs)
            self.assertIn("3 of 3 private library-side proofs compiled", latex)
            self.assertIn("3 of 3 proof dependency records were complete", latex)
            self.assertIn("3 of 3 proofs used NumStability", latex)

    def test_refuses_tampered_pointer_target_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            fixture.construction_path.write_text(
                fixture.construction_path.read_text(encoding="utf-8") + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                ReportError, "current library construction evidence changed after it was frozen"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_authenticated_but_incomplete_l_construction_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            t3_l = next(
                result
                for result in construction["results"]
                if result["task_id"] == "P01-T3" and result["condition"] == "L"
            )
            t3_l["validation"]["dependency_audit"]["library_use"] = False
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "P01-T3/L.*does not record real NumStability library use"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_failed_l_compile_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            t1_l = next(
                result
                for result in construction["results"]
                if result["task_id"] == "P01-T1" and result["condition"] == "L"
            )
            t1_l["validation"]["compile_exit_code"] = 1
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "P01-T1/L.*incomplete compile or dependency record"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_incomplete_l_dependency_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            t2_l = next(
                result
                for result in construction["results"]
                if result["task_id"] == "P01-T2" and result["condition"] == "L"
            )
            t2_l["validation"]["dependency_audit"]["complete"] = False
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "P01-T2/L.*incomplete compile or dependency record"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_unsafe_construction_pointer_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            pointer = json.loads(
                fixture.library_pointer_path.read_text(encoding="utf-8")
            )
            pointer["current_evidence"] = "../construction_validation.json"
            write_json(fixture.library_pointer_path, pointer)
            with self.assertRaisesRegex(ReportError, "unsafe file path"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_pointer_target_with_wrong_evidence_kind(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            construction["kind"] = "unrelated-evidence"
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "not a highambench-private-construction-check"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_renders_required_sections_and_observational_labels(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            inputs = load_report_inputs(fixture.root, fixture.analysis_path)
            latex = render_report(inputs)
            self.assertIn("OBSERVATIONAL ONLY---NOT AN OFFICIAL HIGHAMBENCH SCORE", latex)
            self.assertIn("\\section{Why T1, T2, and T3 are present}", latex)
            self.assertIn("\\section{The exact shared Lean setting}", latex)
            self.assertIn("\\section{The two conditions and their isolation}", latex)
            self.assertIn("Every run record (observational only, not an official score)", latex)
            self.assertIn("Per-condition results (observational only, not an official score)", latex)
            self.assertIn("Per-task results (observational only, not an official score)", latex)
            self.assertIn("Failure counts by condition", latex)
            self.assertIn("Paired changes by tier", latex)
            self.assertIn("Actual library use in condition L", latex)
            self.assertIn("All six private construction proofs", latex)
            self.assertIn("Duplicate search and final tier check", latex)
            self.assertIn("one paper", latex.lower())
            self.assertIn("bootstrap", latex.lower())
            self.assertIn("provider connection", latex.lower())
            self.assertIn("12.500", latex)
            self.assertIn("P01-T3", latex)
            self.assertIn("\\end{document}", latex)

    def test_refuses_incomplete_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            analysis = json.loads(fixture.analysis_path.read_text(encoding="utf-8"))
            analysis["result_set_check"]["ok"] = False
            analysis["result_set_check"]["errors"] = ["missing run"]
            write_json(fixture.analysis_path, analysis)
            with self.assertRaisesRegex(ReportError, "incomplete analysis"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_analysis_after_metadata_changes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            config_path = fixture.root / "metadata" / "config.json"
            config = json.loads(config_path.read_text(encoding="utf-8"))
            config["limits"]["wall_clock_seconds"] = 901
            write_json(config_path, config)
            with self.assertRaisesRegex(ReportError, "stale (analysis|metadata)"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_reproduction_uses_pruned_library_and_no_free_environment_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            latex = render_report(load_report_inputs(fixture.root, fixture.analysis_path))
            self.assertNotIn("--environment-id", latex)
            self.assertNotIn("--library-olean .lake/build/lib/lean", latex)
            self.assertIn("--library-olean " + PRUNED_LIBRARY_OLEAN_ROOT, latex)
            self.assertIn("--packages-runtime-root " + PACKAGES_RUNTIME_ROOT, latex)
            self.assertIn("--release-manifest paper_bencmark/highambench/metadata/release_files.json", latex)
            self.assertIn("--agent-network-verified --token-control-verified", latex)
            self.assertIn(r"rollout\_budget", latex)

    def test_report_explains_exact_axiom_policy_and_authenticated_setup(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            latex = render_report(load_report_inputs(fixture.root, fixture.analysis_path))
            self.assertIn("does not ban every axiom", latex)
            self.assertIn("task-local helper module", latex)
            self.assertNotIn("Only the normal trusted foundations", latex)
            self.assertIn("Authenticated release, compiled setup, and network evidence", latex)
            self.assertIn("Frozen-run check", latex)
            self.assertIn(r"freeze\_check.json", latex)
            self.assertIn("damaged marker evidence", latex)
            self.assertIn(".olean.server, .olean.private, and .ir support files", latex)
            self.assertIn("The host folders /usr, /bin, /lib*, and /etc", latex)
            self.assertIn("not one fully fingerprinted OCI filesystem", latex)

    def test_refuses_construction_tool_not_authenticated_by_release(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["tools"]["tools/preflight.py"] = "0" * 64
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "preflight.py.*not authenticated"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_wrong_pruned_library_mount(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["numstability_compiled"]["mount_root"] = (
                str((fixture.repo / ".lake" / "build" / "lib" / "lean").resolve())
            )
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "exact pruned library mount"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_stale_pruned_library_identity(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["numstability_compiled"]["sha256"] = (
                "0" * 64
            )
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "stale or incomplete.*compiled"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_stale_pruned_package_identity(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["packages_runtime"]["sha256"] = "0" * 64
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "stale or incomplete.*package"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_construction_python_that_differs_from_frozen_runtime(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["executables"]["python"]["version"] = (
                "different"
            )
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "executable identities"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_n_scan_that_did_not_cover_staged_task(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            n_result = next(
                result for result in construction["results"] if result["condition"] == "N"
            )
            n_result["n_preflight"]["filesystem_scan"]["regular_file_count"] = 0
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "complete staged task"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_tampered_adjacent_freeze_check(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            freeze = json.loads(fixture.freeze_path.read_text(encoding="utf-8"))
            freeze["release_manifest"]["file_count"] += 1
            write_json(fixture.freeze_path, freeze)
            with self.assertRaisesRegex(ReportError, "not linked"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_cli_writes_tex(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            status = main(
                [
                    "--benchmark-root",
                    str(fixture.root),
                    "--analysis",
                    str(fixture.analysis_path),
                    "--output-tex",
                    str(fixture.output_tex),
                ]
            )
            self.assertEqual(status, 0)
            self.assertTrue(fixture.output_tex.is_file())
            self.assertIn("not an official HighamBench score", fixture.output_tex.read_text())


if __name__ == "__main__":
    unittest.main()
