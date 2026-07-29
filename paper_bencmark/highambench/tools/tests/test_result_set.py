from __future__ import annotations

import copy
import datetime as dt
import hashlib
import json
from pathlib import Path
import platform
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from analyze import analyze, render_latex, write_csv_tables  # noqa: E402
from common import BenchmarkToolError  # noqa: E402
from result_set import (  # noqa: E402
    ENVIRONMENT_BUNDLE_DEFINITION,
    _environment_bundle_digest,
    check_result_set,
    require_complete_result_set,
)


SHA_A = "a" * 64
SHA_B = "b" * 64
SHA_C = "c" * 64
SALT = "test-highambench-order"
PYTHON_VERSION = platform.python_version()
PYTHON_SHA256 = hashlib.sha256(Path(sys.executable).resolve().read_bytes()).hexdigest()


def benchmark_documents(
    *,
    backend_seed: int | None = 7,
    bubblewrap: bool = False,
    paper_ids: tuple[str, ...] = ("P01",),
) -> tuple[dict, dict, dict]:
    corpus_id = "-".join(paper_id.lower() for paper_id in paper_ids)
    config = {
        "schema_version": "0.1.0",
        "benchmark_id": "test-highambench",
        "frozen_environment": {
            "lean_toolchain": "leanprover/lean4:v4.29.0",
            "lean_commit": "3" * 40,
            "lean_binary_sha256": SHA_A,
            "mathlib_commit": "1" * 40,
            "numstability_commit": "2" * 40,
            "agent_id": "codex",
            "agent_version": "agent-v1",
            "agent_binary_sha256": SHA_B,
            "model_version": "model-v1",
            "model_reasoning_effort": "medium",
            "prompt_sha256": SHA_A,
            "allowed_tools": ["shell", "Lean"],
            "hardware_class": "test-machine",
            "operating_system": "test-os",
            "environment_id": f"highambench-{corpus_id}-" + SHA_C[:16],
            "environment_bundle_sha256": SHA_C,
            "bubblewrap_binary_sha256": SHA_B,
            "bubblewrap_version": "bubblewrap 1.0",
            "numstability_source_manifest": "metadata/library_source.json",
            "numstability_source_manifest_sha256": SHA_A,
            "numstability_compiled_manifest": "metadata/library_olean.json",
            "numstability_compiled_manifest_sha256": SHA_C,
            "compiled_environment_summary": "metadata/packages_olean.json",
            "compiled_environment_summary_sha256": SHA_B,
            "packages_runtime_manifest": "metadata/packages_runtime.json",
            "packages_runtime_manifest_sha256": SHA_A,
            "python_version": PYTHON_VERSION,
            "python_binary_sha256": PYTHON_SHA256,
            "release_manifest": "metadata/release_files.json",
            "release_manifest_sha256": SHA_C,
            "container_image_digest": None if bubblewrap else "sha256:" + SHA_C,
        },
        "limits": {
            "wall_clock_seconds": 100,
            "total_model_tokens": 1000,
            "failure_scored_time_seconds": 100,
        },
        "repetitions": [{"id": "rep-01", "backend_seed": backend_seed}],
        "planned_counts_per_agent": {
            "papers": len(paper_ids),
            "tasks": 3 * len(paper_ids),
            "repetitions_per_task": 1,
            "conditions": 2,
            "paired_assignments": 3 * len(paper_ids),
            "runs": 6 * len(paper_ids),
        },
        "isolation": (
            {
                "implementation": "fresh bubblewrap mount and process namespaces per run",
                "model_shell_network": "blocked inside the namespace",
                "codex_control_process_network": "provider connection retained outside namespace",
            }
            if bubblewrap
            else {"implementation": "frozen OCI container"}
        ),
    }
    papers = []
    for paper_index, paper_id in enumerate(paper_ids):
        targets = []
        for tier in ("T1", "T2", "T3"):
            task_id = f"task-{tier}" if paper_index == 0 else f"task-{paper_id}-{tier}"
            target_file = (
                f"targets/{tier}.lean"
                if paper_index == 0
                else f"targets/{paper_id}/{tier}.lean"
            )
            targets.append(
                {
                    "task_id": task_id,
                    "tier": tier,
                    "lean_target": {
                        "file": target_file,
                        "controlled_file_sha256": SHA_B,
                    },
                }
            )
        papers.append(
            {
                "paper_id": paper_id,
                "source": {
                    "local_path": (
                        "paper.pdf" if paper_index == 0 else f"paper-{paper_id}.pdf"
                    ),
                    "sha256": SHA_C,
                },
                "targets": targets,
            }
        )
    manifest = {
        "schema_version": "0.1.0",
        "benchmark_id": "test-highambench",
        "specification": {"local_path": "spec.pdf", "sha256": SHA_A},
        "papers": papers,
        "controlled_shared_files": [
            {"path": "shared/Definitions.lean", "sha256": SHA_A}
        ],
    }
    pairs = []
    for paper in papers:
        for target in paper["targets"]:
            task_id = target["task_id"]
            repetition_id = "rep-01"
            digest = hashlib.sha256(
                f"{SALT}|{task_id}|{repetition_id}".encode("utf-8")
            ).hexdigest()
            order = ["N", "L"] if int(digest[:2], 16) % 2 == 0 else ["L", "N"]
            pair_id = f"{task_id}-{repetition_id}"
            pairs.append(
                {
                    "pair_id": pair_id,
                    "task_id": task_id,
                    "repetition_id": repetition_id,
                    "sha256": digest,
                    "condition_order": order,
                    "run_ids": [f"{pair_id}-{condition}" for condition in order],
                }
            )
    run_order = {
        "schema_version": "0.1.0",
        "benchmark_id": "test-highambench",
        "method": {"name": "sha256_first_byte_parity", "salt": SALT},
        "pairs": pairs,
    }
    return config, manifest, run_order


def result_records(
    config: dict,
    manifest: dict,
    run_order: dict,
    *,
    observational: bool = False,
) -> list[dict]:
    task_metadata = {
        target["task_id"]: {
            "tier": target["tier"],
            "paper_id": paper["paper_id"],
            "paper_sha256": paper["source"]["sha256"],
        }
        for paper in manifest["papers"]
        for target in paper["targets"]
    }
    seed = config["repetitions"][0]["backend_seed"]
    frozen = config["frozen_environment"]
    freeze_check = {
        "schema_version": 1,
        "kind": "highambench-frozen-run-verification",
        "ok": True,
        "benchmark_id": config["benchmark_id"],
        "environment_id": frozen["environment_id"],
        "environment_bundle_sha256": frozen["environment_bundle_sha256"],
        "agent": {
            "id": frozen["agent_id"],
            "version": frozen["agent_version"],
            "binary_sha256": frozen["agent_binary_sha256"],
            "model": frozen["model_version"],
            "reasoning_effort": frozen["model_reasoning_effort"],
        },
        "python": {
            "version": frozen["python_version"],
            "binary_sha256": frozen["python_binary_sha256"],
        },
        "token_control": {
            "feature": "rollout_budget",
            "feature_row": "rollout_budget under development false",
            "strict_config": True,
            "limit_tokens": config["limits"]["total_model_tokens"],
            "prefill_token_weight": 1,
            "sampling_token_weight": 1,
        },
        "lean": {
            "version": "4.29.0",
            "commit": frozen["lean_commit"],
            "binary_sha256": frozen["lean_binary_sha256"],
            "mathlib_commit": frozen["mathlib_commit"],
            "numstability_commit": frozen["numstability_commit"],
            "compiled_files_verified": 1,
            "source_files_verified": 1,
        },
        "limits": {
            "wall_clock_seconds": config["limits"]["wall_clock_seconds"],
            "total_model_tokens": config["limits"]["total_model_tokens"],
        },
        "bubblewrap": {
            "version": frozen["bubblewrap_version"],
            "binary_sha256": frozen["bubblewrap_binary_sha256"],
        },
        "compiled_environment_summary": {
            "sha256": frozen["compiled_environment_summary_sha256"],
            "toolchain_file_count": 1,
            "package_count": 1,
            "package_file_count": 1,
        },
        "packages_runtime": {
            "path": frozen["packages_runtime_manifest"],
            "sha256": frozen["packages_runtime_manifest_sha256"],
            "file_count": 3,
            "source_file_count": 1,
            "olean_file_count": 1,
            "compiled_support_file_count": 1,
            "verification": {
                "ok": True,
                "verified": 3,
                "expected": 3,
                "missing": [],
                "changed": [],
            },
        },
        "host_class": {
            "kernel": "test-os",
            "virtualization": "TEST",
            "processor": "test-cpu",
            "online_logical_cpus": 1,
            "visible_memory_bytes": 1,
        },
        "release_manifest": {
            "sha256": frozen["release_manifest_sha256"],
            "file_count": 1,
            "verification": {
                "ok": True,
                "verified": 1,
                "expected": 1,
                "missing": [],
                "changed": [],
            },
        },
        "metadata_document_sha256": {
            "config": hashlib.sha256(
                json.dumps(config, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "manifest": hashlib.sha256(
                json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "run_order": hashlib.sha256(
                json.dumps(run_order, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest(),
            "environment": SHA_A,
        },
    }
    freeze_digest = hashlib.sha256(
        json.dumps(freeze_check, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    records: list[dict] = []
    epoch = dt.datetime(2026, 7, 25, tzinfo=dt.timezone.utc)
    for pair_number, pair in enumerate(run_order["pairs"]):
        task = task_metadata[pair["task_id"]]
        pair_start = epoch + dt.timedelta(minutes=pair_number)
        pair_order = "N-first" if pair["condition_order"][0] == "N" else "L-first"
        for order_index, (condition, run_id) in enumerate(
            zip(pair["condition_order"], pair["run_ids"], strict=True), start=1
        ):
            started = pair_start + dt.timedelta(seconds=(order_index - 1) * 20)
            finished = started + dt.timedelta(seconds=10)
            model_tokens = 60 if condition == "N" else 40
            input_tokens = 40 if condition == "N" else 25
            output_tokens = model_tokens - input_tokens
            claims = {
                "fresh_conversation": True,
                "filesystem_isolated": True,
                "network_disabled": True,
                "backend_seed_supplied": seed is not None,
                "seed_enforced_by_agent": seed is not None and not observational,
                "token_limit_enforced_by_agent": not observational,
                "condition_l_library_available": True,
            }
            notes = []
            if observational:
                if seed is None:
                    notes.append("no backend seed was supplied")
                notes.append("provider controls do not enforce the token limit")
            records.append(
                {
                    "schema_version": 1,
                    "kind": "highambench-run",
                    "run_id": run_id,
                    "pair_id": pair["pair_id"],
                    "paper_id": task["paper_id"],
                    "paper_sha256": task["paper_sha256"],
                    "task_id": pair["task_id"],
                    "tier": task["tier"],
                    "condition": condition,
                    "repetition_id": pair["repetition_id"],
                    "backend_seed": seed,
                    "pair_order": pair_order,
                    "order_index": order_index,
                    "agent": {
                        "id": "codex",
                        "version": "agent-v1",
                        "model": "model-v1",
                        "reasoning_effort": "medium",
                    },
                    "environment_id": config["frozen_environment"]["environment_id"],
                    "frozen_run_verification": {
                        "freeze_check_sha256": freeze_digest,
                        "freeze_check": copy.deepcopy(freeze_check),
                    },
                    "limits": {"time_seconds": 100, "model_tokens": 1000},
                    "started_at_utc": started.isoformat(),
                    "finished_at_utc": finished.isoformat(),
                    "useful_work_started": True,
                    "pass": True,
                    "scored": not observational,
                    "failure_code": None,
                    "failure_note": "",
                    "actual_stop_seconds": 12 if condition == "N" else 7,
                    "scored_elapsed_seconds": 12 if condition == "N" else 7,
                    "token_usage": {
                        "input_tokens": input_tokens,
                        "cached_input_tokens": 5,
                        "output_tokens": output_tokens,
                        "model_tokens": model_tokens,
                    },
                    "library_use": condition == "L",
                    "library_declarations": (
                        ["NumStability.example"] if condition == "L" else []
                    ),
                    "submission_sha256": SHA_B,
                    "network_violation": {
                        "detected": False,
                        "event_count": 0,
                        "kernel_event_count": 0,
                        "saturated": False,
                        "integrity_ok": True,
                        "note": "no denied socket-related system call was recorded",
                        "saved_marker_log": None,
                        "marker_sha256": None,
                    },
                    "n_preflight": (
                        {
                            "ok": True,
                            "complete": True,
                            "controlled_task_staging": {
                                "manifest_sha256": SHA_A,
                                "verified_files": 4,
                                "expected_files": 4,
                                "complete": True,
                            },
                            "filesystem_scan": {
                                "root": ".",
                                "markers": ["NumStability", "numStability"],
                                "regular_file_count": 5,
                                "directory_count": 2,
                                "symlink_count": 0,
                                "content_limit_bytes": 4194304,
                            },
                            "filesystem_leaks": [],
                            "import_probe": {"reliable": True, "importable": False},
                        }
                        if condition == "N"
                        else None
                    ),
                    "protocol": {
                        "complete": not observational,
                        "claims": claims,
                        "verified": {
                            "fresh_workspace_copy": True,
                            "condition_n_preflight": True,
                            "condition_n_import_probe_complete": True,
                            "network_violation_marker_integrity": True,
                        },
                        "notes": notes,
                    },
                }
            )
    return records


def refresh_freeze_evidence(
    records: list[dict],
    config: dict,
    manifest: dict,
    run_order: dict,
    *,
    environment: dict | None = None,
) -> None:
    frozen = config["frozen_environment"]
    freeze_check = copy.deepcopy(
        records[0]["frozen_run_verification"]["freeze_check"]
    )
    freeze_check["benchmark_id"] = config["benchmark_id"]
    freeze_check["environment_id"] = frozen["environment_id"]
    freeze_check["environment_bundle_sha256"] = frozen["environment_bundle_sha256"]
    freeze_check["release_manifest"]["sha256"] = frozen["release_manifest_sha256"]
    freeze_check["agent"].update(
        id=frozen["agent_id"],
        version=frozen["agent_version"],
        binary_sha256=frozen["agent_binary_sha256"],
        model=frozen["model_version"],
        reasoning_effort=frozen["model_reasoning_effort"],
    )
    freeze_check["python"] = {
        "version": frozen["python_version"],
        "binary_sha256": frozen["python_binary_sha256"],
    }
    freeze_check["token_control"] = {
        "feature": "rollout_budget",
        "feature_row": "rollout_budget under development false",
        "strict_config": True,
        "limit_tokens": config["limits"]["total_model_tokens"],
        "prefill_token_weight": 1,
        "sampling_token_weight": 1,
    }
    freeze_check["lean"].update(
        commit=frozen["lean_commit"],
        binary_sha256=frozen["lean_binary_sha256"],
        mathlib_commit=frozen["mathlib_commit"],
        numstability_commit=frozen["numstability_commit"],
    )
    freeze_check["limits"] = {
        "wall_clock_seconds": config["limits"]["wall_clock_seconds"],
        "total_model_tokens": config["limits"]["total_model_tokens"],
    }
    freeze_check["bubblewrap"] = {
        "version": frozen["bubblewrap_version"],
        "binary_sha256": frozen["bubblewrap_binary_sha256"],
    }
    freeze_check["compiled_environment_summary"]["sha256"] = frozen[
        "compiled_environment_summary_sha256"
    ]
    freeze_check["packages_runtime"]["path"] = frozen[
        "packages_runtime_manifest"
    ]
    freeze_check["packages_runtime"]["sha256"] = frozen[
        "packages_runtime_manifest_sha256"
    ]
    if environment is not None and isinstance(environment.get("host_class"), dict):
        freeze_check["host_class"] = copy.deepcopy(environment["host_class"])
    freeze_check["metadata_document_sha256"] = {
        "config": hashlib.sha256(
            json.dumps(config, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "manifest": hashlib.sha256(
            json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "run_order": hashlib.sha256(
            json.dumps(run_order, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "environment": (
            hashlib.sha256(
                json.dumps(environment, sort_keys=True, separators=(",", ":")).encode()
            ).hexdigest()
            if environment is not None
            else SHA_A
        ),
    }
    freeze_digest = hashlib.sha256(
        json.dumps(freeze_check, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    for record in records:
        record["environment_id"] = frozen["environment_id"]
        record["frozen_run_verification"] = {
            "freeze_check_sha256": freeze_digest,
            "freeze_check": copy.deepcopy(freeze_check),
        }


class ResultSetTests(unittest.TestCase):
    def reference_fixture(self) -> tuple[dict, dict, dict, list[dict]]:
        config, manifest, run_order = benchmark_documents()
        return config, manifest, run_order, result_records(config, manifest, run_order)

    def test_library_use_and_declaration_names_must_agree(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        l_run = next(run for run in records if run["condition"] == "L")
        l_run["library_declarations"] = []
        report = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(report["ok"])
        self.assertTrue(
            any("claims library use without" in error for error in report["errors"]),
            report,
        )

    def test_each_run_must_match_frozen_environment_and_reasoning_effort(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        wrong_environment = copy.deepcopy(records)
        wrong_environment[0]["environment_id"] = "claimed-but-unfrozen"
        check = check_result_set(
            wrong_environment, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("expected frozen" in error for error in check["errors"]))

        wrong_effort = copy.deepcopy(records)
        wrong_effort[0]["agent"]["reasoning_effort"] = "high"
        check = check_result_set(
            wrong_effort, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("reasoning_effort" in error for error in check["errors"]))

    def test_missing_mismatched_and_stale_freeze_evidence_is_rejected(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        missing = copy.deepcopy(records)
        missing[0].pop("frozen_run_verification")
        check = check_result_set(
            missing, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("mandatory frozen-run" in error for error in check["errors"]))

        altered = copy.deepcopy(records)
        altered[0]["frozen_run_verification"]["freeze_check_sha256"] = "0" * 64
        check = check_result_set(
            altered, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("stale or altered" in error for error in check["errors"]))

        stale_config = copy.deepcopy(config)
        stale_config["frozen_note"] = "changed after startup verification"
        check = check_result_set(
            records, run_order=run_order, config=stale_config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("stale for config" in error for error in check["errors"]))

        truncated = copy.deepcopy(records)
        for record in truncated:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"].pop("lean")
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"], sort_keys=True, separators=(",", ":")
                ).encode()
            ).hexdigest()
        check = check_result_set(
            truncated, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("Lean identity" in error for error in check["errors"]))

        missing_runtime = copy.deepcopy(records)
        for record in missing_runtime:
            wrapper = record["frozen_run_verification"]
            wrapper["freeze_check"].pop("packages_runtime")
            wrapper["freeze_check_sha256"] = hashlib.sha256(
                json.dumps(
                    wrapper["freeze_check"], sort_keys=True, separators=(",", ":")
                ).encode()
            ).hexdigest()
        check = check_result_set(
            missing_runtime,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("packages-runtime evidence" in error for error in check["errors"])
        )

        wrong_python_config = copy.deepcopy(config)
        wrong_python_config["frozen_environment"]["python_version"] = "0.0.0"
        wrong_python_records = copy.deepcopy(records)
        refresh_freeze_evidence(
            wrong_python_records,
            wrong_python_config,
            manifest,
            run_order,
        )
        check = check_result_set(
            wrong_python_records,
            run_order=run_order,
            config=wrong_python_config,
            manifest=manifest,
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("current Python version" in error for error in check["errors"])
        )

    def test_complete_reference_matrix(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertTrue(check["reference_compliant"])
        self.assertTrue(check["official_scores_valid"])
        self.assertEqual(check["analysis_profile"], "reference")
        self.assertEqual(check["selected_final_record_count"], 6)
        self.assertEqual(check["expected_pairs_per_agent"], 3)
        require_complete_result_set(check)

    def test_complete_two_paper_matrix_uses_corpus_environment_id(self) -> None:
        config, manifest, run_order = benchmark_documents(
            paper_ids=("P01", "P02")
        )
        records = result_records(config, manifest, run_order)
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertEqual(
            config["frozen_environment"]["environment_id"],
            "highambench-p01-p02-" + SHA_C[:16],
        )
        self.assertEqual(check["selected_final_record_count"], 12)
        self.assertEqual(check["expected_pairs_per_agent"], 6)

    def test_environment_id_rejects_stale_or_reordered_corpus_prefix(self) -> None:
        config, manifest, run_order = benchmark_documents(
            paper_ids=("P01", "P02")
        )
        records = result_records(config, manifest, run_order)

        stale_config = copy.deepcopy(config)
        stale_config["frozen_environment"]["environment_id"] = (
            "highambench-p01-" + SHA_C[:16]
        )
        stale_records = copy.deepcopy(records)
        refresh_freeze_evidence(stale_records, stale_config, manifest, run_order)
        stale_check = check_result_set(
            stale_records,
            run_order=run_order,
            config=stale_config,
            manifest=manifest,
        )
        self.assertFalse(stale_check["ok"])
        self.assertTrue(
            any(
                "expected 'highambench-p01-p02-" in error
                for error in stale_check["errors"]
            ),
            stale_check,
        )

        reordered_manifest = copy.deepcopy(manifest)
        reordered_manifest["papers"].reverse()
        reordered_records = copy.deepcopy(records)
        refresh_freeze_evidence(
            reordered_records, config, reordered_manifest, run_order
        )
        reordered_check = check_result_set(
            reordered_records,
            run_order=run_order,
            config=config,
            manifest=reordered_manifest,
        )
        self.assertFalse(reordered_check["ok"])
        self.assertTrue(
            any(
                "expected 'highambench-p02-p01-" in error
                for error in reordered_check["errors"]
            ),
            reordered_check,
        )

    def test_package_runtime_support_count_is_required_and_reconciles(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        records[0]["frozen_run_verification"]["freeze_check"][
            "packages_runtime"
        ].pop("compiled_support_file_count")
        refresh_freeze_evidence(records, config, manifest, run_order)
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("packages-runtime evidence" in error for error in check["errors"]),
            check,
        )

        config, manifest, run_order, records = self.reference_fixture()
        records[0]["frozen_run_verification"]["freeze_check"][
            "packages_runtime"
        ]["compiled_support_file_count"] = 2
        refresh_freeze_evidence(records, config, manifest, run_order)
        check = check_result_set(
            records, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("packages-runtime evidence" in error for error in check["errors"]),
            check,
        )

    def test_incomplete_and_mismatched_matrices_are_rejected(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        cases: list[tuple[str, list[dict], dict]] = []

        missing = copy.deepcopy(records[:-1])
        cases.append(("missing", missing, run_order))

        wrong_hash = copy.deepcopy(records)
        wrong_hash[0]["paper_sha256"] = "0" * 64
        cases.append(("paper hash", wrong_hash, run_order))

        wrong_limit = copy.deepcopy(records)
        wrong_limit[0]["limits"]["time_seconds"] = 99
        cases.append(("limit", wrong_limit, run_order))

        wrong_agent = copy.deepcopy(records)
        wrong_agent[0]["agent"]["model"] = "different-model"
        cases.append(("agent metadata", wrong_agent, run_order))

        wrong_order = copy.deepcopy(records)
        pair = run_order["pairs"][0]
        first = next(run for run in wrong_order if run["run_id"] == pair["run_ids"][0])
        second = next(run for run in wrong_order if run["run_id"] == pair["run_ids"][1])
        second["started_at_utc"] = first["started_at_utc"]
        cases.append(("chronological order", wrong_order, run_order))

        corrupt_plan = copy.deepcopy(run_order)
        corrupt_plan["pairs"][0]["sha256"] = "f" * 64
        cases.append(("run-order digest", copy.deepcopy(records), corrupt_plan))

        for label, candidate_records, candidate_order in cases:
            with self.subTest(label=label):
                check = check_result_set(
                    candidate_records,
                    run_order=candidate_order,
                    config=config,
                    manifest=manifest,
                )
                self.assertFalse(check["ok"])
                self.assertFalse(check["reference_compliant"])
                with self.assertRaises(BenchmarkToolError):
                    require_complete_result_set(check)

    def test_one_system_error_followed_by_one_rerun_is_resolved(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        final = records[0]
        incident = copy.deepcopy(final)
        incident["planned_run_id"] = final["run_id"]
        incident["run_id"] = final["run_id"] + "-system-attempt-1"
        incident["pass"] = False
        incident["scored"] = False
        incident["failure_code"] = "SYSTEM_ERROR"
        incident["failure_note"] = "temporary executor fault before useful work"
        incident["actual_stop_seconds"] = 1
        incident["scored_elapsed_seconds"] = 1
        incident["token_usage"] = None
        incident["useful_work_started"] = False
        final_start = dt.datetime.fromisoformat(final["started_at_utc"])
        incident["started_at_utc"] = (final_start - dt.timedelta(seconds=10)).isoformat()
        incident["finished_at_utc"] = (final_start - dt.timedelta(seconds=5)).isoformat()
        check = check_result_set(
            [incident, *records],
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertTrue(check["system_error_handling_complete"])
        self.assertEqual(check["system_error_incident_count"], 1)
        self.assertEqual(check["input_record_count"], 7)

        unresolved = check_result_set(
            [incident, *records[1:]],
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(unresolved["ok"])
        self.assertFalse(unresolved["system_error_handling_complete"])
        self.assertTrue(unresolved["system_error_issues"])

    def test_system_error_after_useful_work_is_a_charged_final_failure(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        failed = records[0]
        failed["pass"] = False
        failed["failure_code"] = "SYSTEM_ERROR"
        failed["failure_note"] = "executor failed after the agent turn started"
        failed["useful_work_started"] = True
        failed["scored_elapsed_seconds"] = config["limits"]["failure_scored_time_seconds"]
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertEqual(check["system_error_incident_count"], 0)
        self.assertIn(failed["run_id"], check["selected_final_run_ids"])

    def test_file_hashes_are_re_read_when_repository_root_is_given(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            files = {
                "spec.pdf": b"specification",
                "paper.pdf": b"paper",
                "shared/Definitions.lean": b"shared",
                "targets/T1.lean": b"T1",
                "targets/T2.lean": b"T2",
                "targets/T3.lean": b"T3",
                "metadata/library_source.json": b'{"files":[{}]}',
                "metadata/library_olean.json": b'{"files":[{}]}',
                "metadata/packages_olean.json": (
                    b'{"toolchain":{"file_count":1},"packages":[{"file_count":1}]}'
                ),
                "metadata/packages_runtime.json": (
                    b'{"files":['
                    b'{"path":"mathlib/Mathlib.lean"},'
                    b'{"path":"mathlib/.lake/build/lib/lean/Mathlib.olean"},'
                    b'{"path":"mathlib/.lake/build/lib/lean/Mathlib.ir"}'
                    b']}'
                ),
                "metadata/release_files.json": b'{"files":[{}]}',
                "paper_bencmark/highambench/metadata/controlled/task-T1.json": b"controlled T1",
                "paper_bencmark/highambench/metadata/controlled/task-T2.json": b"controlled T2",
                "paper_bencmark/highambench/metadata/controlled/task-T3.json": b"controlled T3",
            }
            for relative, payload in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(payload)

            def digest(relative: str) -> str:
                return hashlib.sha256(files[relative]).hexdigest()

            manifest["specification"]["sha256"] = digest("spec.pdf")
            frozen = config["frozen_environment"]
            frozen["numstability_source_manifest_sha256"] = digest(
                "metadata/library_source.json"
            )
            frozen["numstability_compiled_manifest_sha256"] = digest(
                "metadata/library_olean.json"
            )
            frozen["compiled_environment_summary_sha256"] = digest(
                "metadata/packages_olean.json"
            )
            frozen["packages_runtime_manifest_sha256"] = digest(
                "metadata/packages_runtime.json"
            )
            frozen["release_manifest_sha256"] = digest(
                "metadata/release_files.json"
            )
            manifest["papers"][0]["source"]["sha256"] = digest("paper.pdf")
            manifest["controlled_shared_files"][0]["sha256"] = digest(
                "shared/Definitions.lean"
            )
            for target in manifest["papers"][0]["targets"]:
                target["lean_target"]["controlled_file_sha256"] = digest(
                    target["lean_target"]["file"]
                )
            for record in records:
                record["paper_sha256"] = digest("paper.pdf")
                if record["condition"] == "N":
                    controlled_path = (
                        f"paper_bencmark/highambench/metadata/controlled/"
                        f"{record['task_id']}.json"
                    )
                    record["n_preflight"]["controlled_task_staging"][
                        "manifest_sha256"
                    ] = digest(controlled_path)
            environment = {
                "environment_id": "placeholder",
                "environment_bundle_sha256": "0" * 64,
                "environment_bundle_definition": ENVIRONMENT_BUNDLE_DEFINITION,
                "release_manifest_sha256": frozen["release_manifest_sha256"],
                "runtime": {
                    "python": {
                        "version": frozen["python_version"],
                        "binary_sha256": frozen["python_binary_sha256"],
                    },
                    "packages_runtime_manifest": frozen[
                        "packages_runtime_manifest"
                    ],
                    "packages_runtime_manifest_sha256": frozen[
                        "packages_runtime_manifest_sha256"
                    ],
                },
                "host_class": {
                    "kernel": "test-os",
                    "virtualization": "TEST",
                    "processor": "test-cpu",
                    "online_logical_cpus": 1,
                    "visible_memory_bytes": 1,
                },
            }
            bundle = _environment_bundle_digest(config, environment)
            environment_id = "highambench-p01-" + bundle[:16]
            frozen["environment_bundle_sha256"] = bundle
            frozen["environment_id"] = environment_id
            environment["environment_bundle_sha256"] = bundle
            environment["environment_id"] = environment_id
            environment_path = (
                root / "paper_bencmark/highambench/metadata/environment.json"
            )
            environment_path.parent.mkdir(parents=True, exist_ok=True)
            environment_path.write_text(json.dumps(environment), encoding="utf-8")
            refresh_freeze_evidence(
                records, config, manifest, run_order, environment=environment
            )
            check = check_result_set(
                records,
                run_order=run_order,
                config=config,
                manifest=manifest,
                repository_root=root,
            )
            self.assertTrue(check["ok"], check["errors"])
            self.assertTrue(all(item["match"] for item in check["verified_hashes"]))

            (root / "targets/T2.lean").write_text("changed", encoding="utf-8")
            changed = check_result_set(
                records,
                run_order=run_order,
                config=config,
                manifest=manifest,
                repository_root=root,
            )
            self.assertFalse(changed["ok"])
            self.assertTrue(
                any("target task-T2" in error for error in changed["errors"])
            )

    def test_observational_bubblewrap_pilot_is_complete_but_not_a_score(self) -> None:
        config, manifest, run_order = benchmark_documents(
            backend_seed=None, bubblewrap=True
        )
        records = result_records(
            config, manifest, run_order, observational=True
        )
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
            allow_observational_unscored=True,
        )
        self.assertTrue(check["ok"], check["errors"])
        self.assertFalse(check["reference_compliant"])
        self.assertFalse(check["official_scores_valid"])
        self.assertEqual(check["analysis_profile"], "observational_pilot")
        self.assertEqual(check["official_final_record_count"], 0)
        reasons = " ".join(check["nonreference_reasons"])
        self.assertIn("backend seeds", reasons)
        self.assertIn("bubblewrap", reasons)
        self.assertIn("provider connection", reasons)

        official_attempt = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
        )
        self.assertFalse(official_attempt["ok"])

        analysis = analyze(
            records,
            include_unscored=False,
            bootstrap_resamples=25,
            bootstrap_seed=4,
            run_order=run_order,
            config=config,
            manifest=manifest,
            require_complete=True,
            observational_pilot=True,
        )
        self.assertFalse(analysis["official_scores_valid"])
        self.assertEqual(analysis["analyzed_run_count"], 0)
        self.assertEqual(analysis["condition_summaries"], [])
        self.assertEqual(analysis["paired_comparisons"], [])
        self.assertEqual(len(analysis["per_run_results"]), 6)
        pilot = analysis["observational_pilot_results"]
        self.assertIsNotNone(pilot)
        assert pilot is not None
        self.assertTrue(pilot["condition_summaries"])
        self.assertEqual(len(pilot["per_task_summaries"]), 6)
        self.assertEqual(len(pilot["per_task_paired_comparisons"]), 3)
        overall = next(
            row for row in pilot["paired_comparisons"] if row["scope"] == "overall"
        )
        self.assertEqual(overall["median_observed_paired_time_change"], -5)
        self.assertEqual(overall["median_observed_paired_token_change"], -20)
        self.assertFalse(overall["bootstrap"]["informative"])
        self.assertIn("degenerate", overall["bootstrap"]["note"])

        with tempfile.TemporaryDirectory() as raw:
            output = Path(raw)
            write_csv_tables(output, analysis)
            self.assertTrue((output / "observational_condition_summary.csv").is_file())
            self.assertTrue((output / "observational_task_summary.csv").is_file())
            self.assertTrue((output / "observational_paired_summary.csv").is_file())
            self.assertTrue(
                (output / "observational_task_paired_summary.csv").is_file()
            )
        latex = render_latex(analysis)
        self.assertIn("not official scores", latex)
        self.assertIn("degenerate", latex)
        self.assertIn("Observed per-task paired changes", latex)

    def test_observational_mode_does_not_relax_network_isolation(self) -> None:
        config, manifest, run_order = benchmark_documents(
            backend_seed=None, bubblewrap=True
        )
        records = result_records(config, manifest, run_order, observational=True)
        records[0]["protocol"]["claims"]["network_disabled"] = False
        check = check_result_set(
            records,
            run_order=run_order,
            config=config,
            manifest=manifest,
            allow_observational_unscored=True,
        )
        self.assertFalse(check["ok"])
        self.assertTrue(
            any("non-relaxable controls" in error for error in check["errors"])
        )

    def test_final_network_evidence_is_mandatory_and_coherent(self) -> None:
        config, manifest, run_order, records = self.reference_fixture()
        missing = copy.deepcopy(records)
        missing[0].pop("network_violation")
        check = check_result_set(
            missing, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("structured network" in error for error in check["errors"]))

        incoherent = copy.deepcopy(records)
        incoherent[0]["network_violation"]["detected"] = True
        incoherent[0]["network_violation"]["event_count"] = 1
        check = check_result_set(
            incoherent, run_order=run_order, config=config, manifest=manifest
        )
        self.assertFalse(check["ok"])
        self.assertTrue(any("unsafe network" in error for error in check["errors"]))


if __name__ == "__main__":
    unittest.main()
