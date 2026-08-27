from __future__ import annotations

import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, read_json, sha256_file, write_json  # noqa: E402
import refresh_snapshot as refresh_snapshot_module  # noqa: E402
from refresh_snapshot import (  # noqa: E402
    PHASE_CONSTRUCTION,
    PHASE_MEASUREMENT_READY,
    refresh_snapshot,
)
from codex_isolated import nested_submission_exec_yield_record  # noqa: E402
from task_tags import validate_t4_task_metadata  # noqa: E402
from paper_bencmark.highambench.tools.tests.test_task_tags import (  # noqa: E402
    base_t4_task,
)
from runner import PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT  # noqa: E402
from run_matrix import (  # noqa: E402
    canonical_document_digest,
    environment_bundle_digest,
    ultra_orchestration_record,
)


class RefreshSnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name) / "benchmark"
        (self.root / "metadata").mkdir(parents=True)
        (self.root / "shared" / "HighamBench").mkdir(parents=True)
        (self.root / "shared" / "HighamBench" / "Core.lean").write_text(
            "namespace HighamBench\nend HighamBench\n", encoding="utf-8"
        )
        for paper_id in ("P07", "P12"):
            (self.root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean").write_text(
                "import HighamBench.Core\n", encoding="utf-8"
            )
        (self.root / "agent_prompt.md").write_text("prove the task\n", encoding="utf-8")
        (self.root / "condition_prompts").mkdir()
        (self.root / "condition_prompts" / "L.md").write_text(
            "Condition L can search /library/NumStability.\n", encoding="utf-8"
        )
        (self.root / "tools").mkdir()
        shutil.copyfile(
            TOOLS / "provider_token_gate.py",
            self.root / "tools" / "provider_token_gate.py",
        )
        # Snapshot refresh deliberately hashes every execution component when
        # the isolation record is synthesized.  These minimal fixture files
        # keep that production invariant exercised without copying the whole
        # benchmark implementation into the temporary tree.
        for relative in (
            "codex_isolated.py",
            "lean_isolated.py",
            "offline_shell.c",
            "runner.py",
            "validator.py",
            "dependency_audit.lean",
        ):
            (self.root / "tools" / relative).write_text(
                f"fixture {relative}\n", encoding="utf-8"
            )
        (self.root / "tools" / "tests").mkdir()
        (self.root / "tools" / "tests" / "test_provider_token_gate.py").write_text(
            "# fixture provider gate test\n", encoding="utf-8"
        )

        papers = []
        for paper_id, tier, digest in (
            ("P07", "T1", "7" * 64),
            ("P12", "T3", "c" * 64),
        ):
            task_id = f"{paper_id}-{tier}"
            task_root = self.root / "tasks" / paper_id / tier
            task_root.mkdir(parents=True)
            (task_root / "Target.lean").write_text(
                f"namespace HighamBench\ntheorem {paper_id.lower()}_{tier.lower()} : True := by sorry\nend HighamBench\n",
                encoding="utf-8",
            )
            (task_root / "context.md").write_text("paper context\n", encoding="utf-8")
            write_json(
                task_root / "task.json",
                {
                    "schema_version": "highambench-task-0.3",
                    "task_id": task_id,
                    "paper_id": paper_id,
                    "tier": tier,
                    "source_tags": ["EQN"],
                    "author_label": None,
                    "classification_frozen_before_runs": True,
                    "source_locations": [{"anchor": "equation (1.1)"}],
                },
            )
            write_json(
                self.root / "tasks" / paper_id / "paper.json",
                {
                    "paper_id": paper_id,
                    "source": {"sha256": digest},
                    "classification_frozen_before_runs": True,
                    "included_tasks": [task_id],
                },
            )
            papers.append(
                {
                    "paper_id": paper_id,
                    "source": {"sha256": digest},
                    "targets": [
                        {
                            "task_id": task_id,
                            "tier": tier,
                            "availability": "available",
                            "lean_target": {
                                "declaration": f"{paper_id.lower()}_{tier.lower()}",
                                "file": f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/Target.lean",
                            },
                        }
                    ],
                }
            )

        write_json(
            self.root / "metadata" / "manifest.json",
            {
                "benchmark_id": "stale-id",
                "specification": {"version": "0.2"},
                "corpus": {"paper_count": 0, "paper_ids": []},
                "controlled_shared_files": [
                    {
                        "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                        "paper_ids": ["P07", "P12"],
                    },
                    {
                        "path": "paper_bencmark/highambench/shared/HighamBench/P07Definitions.lean",
                        "paper_ids": ["P07"],
                    },
                    {
                        "path": "paper_bencmark/highambench/shared/HighamBench/P12Definitions.lean",
                        "paper_ids": ["P12"],
                    },
                ],
                "papers": papers,
            },
        )
        write_json(
            self.root / "metadata" / "config.json",
            {
                "benchmark_id": "stale-id",
                "frozen_environment": {},
                "limits": {
                    "failure_scored_time_seconds": 900,
                    "total_model_tokens": 120000,
                    "wall_clock_seconds": 900,
                },
                "repetitions": [{"id": "rep-a"}, {"id": "rep-b"}],
            },
        )
        write_json(self.root / "metadata" / "environment.json", {})

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_construction_accepts_pending_safe_t4_plural_shape(self) -> None:
        task = base_t4_task()
        task["faithfulness_reviews"] = []
        for unit in task["review_units"]:
            unit["review_status"] = "pending"
        summary = refresh_snapshot_module._construction_t4_summary(
            task, label="P01-T4"
        )
        self.assertEqual(summary["declaration_count"], 3)
        self.assertEqual(summary["controlled_sorry_count"], 1)
        self.assertEqual(summary["review_count"], 0)
        self.assertFalse(summary["measurement_ready"])

    def test_measurement_readiness_rejects_skeleton_only_then_accepts_private_t4_proofs(self) -> None:
        task = base_t4_task()
        task["classification_frozen_before_runs"] = True
        summary = validate_t4_task_metadata(task, label="P01-T4")
        manifest_path = self.root / "metadata" / "manifest.json"
        task_ids = ["P01-T4"]
        profile = refresh_snapshot_module._readiness_profile([summary])
        skeleton_results = [
            {
                "task_id": "P01-T4",
                "condition": condition,
                "construction_kind": "designated-hole-skeleton",
                "pass": True,
                "validation": {
                    "pass": True,
                    "required_declaration_count": 3,
                    "required_declarations_checked": 3,
                    "controlled_sorry_count": 1,
                    "controlled_sorries_checked": 1,
                },
            }
            for condition in ("N", "L")
        ]
        evidence_path = (
            self.root / "metadata" / "evidence" / "construction_t4.json"
        )
        write_json(
            evidence_path,
            {
                "schema_version": 2,
                "kind": "highambench-private-construction-check",
                "record_status": "current_final",
                "pass": True,
                "scope": {
                    "complete_manifest_scope": True,
                    "selected_task_ids": task_ids,
                    "central_manifest_sha256": sha256_file(manifest_path),
                },
                "summary": {
                    "expected": 2,
                    "checked": 2,
                    "passed": 2,
                    "condition_n_passed": 1,
                    "condition_l_passed": 1,
                    **profile,
                },
                "results": skeleton_results,
            },
        )
        with self.assertRaisesRegex(
            BenchmarkToolError, "schema-aware construction record"
        ):
            refresh_snapshot_module._measurement_readiness(
                self.root,
                [("P01", "T4", "P01-T4", {})],
                [summary],
            )

        results = [
            {
                "task_id": "P01-T4",
                "condition": condition,
                "construction_kind": "t4-private-proof",
                "gold_source_sha256": "a" * 64,
                "pass": True,
                "validation": {
                    "pass": True,
                    "proof_holes_discharged": True,
                    "required_declaration_count": 3,
                    "required_declarations_checked": 3,
                    "controlled_sorry_count": 1,
                    "controlled_sorries_checked": 1,
                    "proof_declaration_count": 1,
                    "proof_declarations_audited": 1,
                },
                "controlled_skeleton": {
                    "construction_kind": "designated-hole-skeleton",
                    "pass": True,
                    "validation": {
                        "pass": True,
                        "required_declarations_checked": 3,
                        "controlled_sorries_checked": 1,
                    },
                },
            }
            for condition in ("N", "L")
        ]
        write_json(
            evidence_path,
            {
                "schema_version": 3,
                "kind": "highambench-private-construction-check",
                "record_status": "current_final",
                "pass": True,
                "scope": {
                    "complete_manifest_scope": True,
                    "selected_task_ids": task_ids,
                    "central_manifest_sha256": sha256_file(manifest_path),
                },
                "summary": {
                    "expected": 2,
                    "checked": 2,
                    "passed": 2,
                    "condition_n_passed": 1,
                    "condition_l_passed": 1,
                    **profile,
                },
                "results": results,
            },
        )
        policy = refresh_snapshot_module._measurement_readiness(
            self.root,
            [("P01", "T4", "P01-T4", {})],
            [summary],
        )
        self.assertEqual(policy["review_records"], [])
        self.assertEqual(
            policy["t4_claim_review_coverage"][0]["accepted_review_count"],
            2,
        )

    def test_provider_gate_refresh_rejects_legacy_freeze_protocols(self) -> None:
        legacy = {
            "schema_version": 1,
            "protocol": "highambench-provider-token-gate-v2",
            "implementation": {"version": "2"},
            "static_configuration": {
                "upstream_response_contract": dict(
                    PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT
                )
            },
        }
        with mock.patch.object(
            refresh_snapshot_module,
            "provider_token_gate_environment_record",
            return_value=legacy,
        ), self.assertRaisesRegex(BenchmarkToolError, "exact.*v6 freeze"):
            refresh_snapshot_module._sync_provider_token_gate(
                self.root,
                {"frozen_environment": {}},
                {},
            )

    def test_frozen_l_prompt_targets_candidate_and_hashes_match(self) -> None:
        benchmark = TOOLS.parent
        prompt_path = benchmark / "condition_prompts" / "L.md"
        text = prompt_path.read_text(encoding="utf-8")
        self.assertIn("`import NumStability...` lines to `Candidate.lean`", text)
        self.assertNotIn("`Submission.lean`", text)
        descriptor = {
            "path": "condition_prompts/L.md",
            "sha256": sha256_file(prompt_path),
            "bytes": len(prompt_path.read_bytes()),
        }
        config = read_json(benchmark / "metadata" / "config.json")
        environment = read_json(benchmark / "metadata" / "environment.json")
        self.assertEqual(
            config["frozen_environment"]["prompt_protocol"][
                "condition_supplements"
            ]["L"],
            descriptor,
        )
        self.assertEqual(
            environment["agent"]["prompt_protocol"]["condition_supplements"]["L"],
            descriptor,
        )

    def test_refresh_replaces_legacy_barrier_and_invalidates_canaries(self) -> None:
        refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")

        legacy_ultra = ultra_orchestration_record()
        legacy_ultra["submission_barrier"] = {
            "schema_version": 3,
            "submission_transport": "functions_exec_dynamic_submit_proof_v1",
            "legacy_canary_id": "ULTRA-ORCHESTRATION-SUBMISSION-CANARY-V5",
            "outer_exec_yield_time_ms": 10_000,
        }
        config["frozen_environment"]["ultra_orchestration"] = legacy_ultra
        environment["agent"]["ultra_orchestration"] = legacy_ultra
        stale_descriptor = {
            "path": "metadata/evidence/stale-live-canary.json",
            "sha256": "f" * 64,
            "status": "passed",
        }
        for key in ("ultra_orchestration_canary", "token_control_canary"):
            config["frozen_environment"][key] = dict(stale_descriptor)
            environment[key] = dict(stale_descriptor)
        write_json(self.root / "metadata" / "config.json", config)
        write_json(self.root / "metadata" / "environment.json", environment)

        refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")
        configured = config["frozen_environment"]["ultra_orchestration"]
        implemented = environment["agent"]["ultra_orchestration"]
        expected = ultra_orchestration_record()
        self.assertEqual(configured, expected)
        self.assertEqual(implemented, expected)

        barrier = configured["submission_barrier"]
        self.assertEqual(barrier["schema_version"], 5)
        self.assertEqual(
            barrier["submission_transport"],
            "functions_exec_dynamic_submit_proof_v3",
        )
        yield_record = nested_submission_exec_yield_record()
        self.assertEqual(len(yield_record), 8)
        self.assertEqual(
            {field: barrier[field] for field in yield_record},
            yield_record,
        )
        self.assertGreater(
            barrier["outer_exec_yield_time_ms"],
            barrier["outer_exec_yield_envelope_ms"],
        )
        self.assertTrue(barrier["outer_exec_yield_exceeds_envelope"])
        frozen_text = json.dumps(
            {
                "configured": configured,
                "implemented": implemented,
            },
            sort_keys=True,
        )
        self.assertNotIn("functions_exec_dynamic_submit_proof_v1", frozen_text)
        self.assertNotIn("functions_exec_dynamic_submit_proof_v2", frozen_text)
        self.assertNotIn("ULTRA-ORCHESTRATION-SUBMISSION-CANARY-V5", frozen_text)

        for key in ("ultra_orchestration_canary", "token_control_canary"):
            self.assertEqual(
                config["frozen_environment"][key],
                environment[key],
            )
            self.assertEqual(environment[key]["status"], "replacement_required")

    def test_common_prompt_rehash_preserves_task_and_shared_bytes(self) -> None:
        baseline = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        controlled_before = {
            path.name: sha256_file(path)
            for path in sorted((self.root / "metadata" / "controlled").glob("*.json"))
        }
        protected_before = {
            path.relative_to(self.root).as_posix(): path.read_bytes()
            for tree in (self.root / "tasks", self.root / "shared")
            for path in sorted(tree.rglob("*"))
            if path.is_file()
        }

        prompt = self.root / "agent_prompt.md"
        prompt.write_text(
            prompt.read_text(encoding="utf-8")
            + "Use the exact anti-yield submission wrapper.\n",
            encoding="utf-8",
        )
        prompt_sha256 = sha256_file(prompt)
        refreshed = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)

        protected_after = {
            path.relative_to(self.root).as_posix(): path.read_bytes()
            for tree in (self.root / "tasks", self.root / "shared")
            for path in sorted(tree.rglob("*"))
            if path.is_file()
        }
        self.assertEqual(protected_after, protected_before)

        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")
        self.assertEqual(config["frozen_environment"]["prompt_sha256"], prompt_sha256)
        self.assertEqual(environment["agent"]["prompt_sha256"], prompt_sha256)
        self.assertEqual(
            config["frozen_environment"]["prompt_protocol"]["common_prompt"],
            {
                "path": "agent_prompt.md",
                "sha256": prompt_sha256,
                "bytes": prompt.stat().st_size,
            },
        )
        self.assertEqual(
            config["frozen_environment"]["prompt_protocol"],
            environment["agent"]["prompt_protocol"],
        )

        for path in sorted((self.root / "metadata" / "controlled").glob("*.json")):
            controlled = read_json(path)
            prompt_entry = next(
                entry
                for entry in controlled["files"]
                if entry["path"] == "agent_prompt.md"
            )
            self.assertEqual(prompt_entry["sha256"], prompt_sha256)
            self.assertEqual(prompt_entry["bytes"], prompt.stat().st_size)
            self.assertNotEqual(sha256_file(path), controlled_before[path.name])

        release = read_json(self.root / "metadata" / "release_files.json")
        release_prompt = next(
            entry for entry in release["files"] if entry["path"] == "agent_prompt.md"
        )
        self.assertEqual(release_prompt["sha256"], prompt_sha256)
        self.assertEqual(release_prompt["bytes"], prompt.stat().st_size)
        self.assertEqual(
            refreshed["release_manifest_sha256"],
            sha256_file(self.root / "metadata" / "release_files.json"),
        )
        self.assertNotEqual(
            refreshed["release_manifest_sha256"],
            baseline["release_manifest_sha256"],
        )
        self.assertEqual(
            refreshed["environment_bundle_sha256"],
            environment_bundle_digest(config, environment),
        )
        self.assertEqual(
            environment["environment_bundle_sha256"],
            refreshed["environment_bundle_sha256"],
        )
        self.assertNotEqual(
            refreshed["environment_bundle_sha256"],
            baseline["environment_bundle_sha256"],
        )
        self.assertNotEqual(refreshed["environment_id"], baseline["environment_id"])

    def test_one_workflow_refreshes_arbitrary_paper_ids_and_both_phases(self) -> None:
        first = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        self.assertEqual(first["paper_ids"], ["P07", "P12"])
        self.assertEqual(first["benchmark_id"], "highambench-0.2-p07-p12")
        self.assertEqual(first["pair_count"], 4)
        self.assertEqual(first["run_count"], 8)

        manifest = read_json(self.root / "metadata" / "manifest.json")
        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")
        self.assertEqual(
            config["frozen_environment"]["prompt_protocol"],
            environment["agent"]["prompt_protocol"],
        )
        self.assertEqual(
            set(
                config["frozen_environment"]["prompt_protocol"][
                    "condition_supplements"
                ]
            ),
            {"L"},
        )
        self.assertEqual(manifest["corpus"]["paper_ids"], ["P07", "P12"])
        self.assertEqual(manifest["corpus"]["paper_count"], 2)
        self.assertEqual(config["limits"]["prompt_startup_timeout_seconds"], 120)
        self.assertEqual(
            environment["runtime"]["prompt_startup_timeout_seconds"], 120
        )
        self.assertEqual(
            config["limits"]["post_submission_validation_reserve_seconds"], 369
        )
        self.assertEqual(
            environment["runtime"][
                "post_submission_validation_reserve_seconds"
            ],
            369,
        )
        self.assertEqual(config["token_control"], environment["token_control"])
        provider_gate = environment["provider_token_gate"]
        self.assertEqual(
            config["frozen_environment"]["provider_token_gate_sha256"],
            canonical_document_digest(provider_gate),
        )
        self.assertEqual(provider_gate["schema_version"], 2)
        self.assertEqual(provider_gate["protocol"], "highambench-provider-token-gate-v6")
        self.assertEqual(provider_gate["implementation"]["version"], "6")
        self.assertEqual(
            provider_gate["static_configuration"]["upstream_response_contract"],
            PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT,
        )
        self.assertEqual(
            provider_gate["transport_provenance"]["connection_factory_mode"],
            "explicit_tls",
        )
        self.assertEqual(config["frozen_environment"]["model_version"], "gpt-5.6-sol")
        self.assertEqual(
            config["frozen_environment"]["model_reasoning_effort"], "ultra"
        )
        self.assertEqual(
            config["frozen_environment"]["ultra_orchestration"],
            environment["agent"]["ultra_orchestration"],
        )
        self.assertEqual(
            environment["agent"]["ultra_orchestration"][
                "max_concurrent_threads_per_session"
            ],
            4,
        )
        self.assertEqual(config["isolation"]["history_persistence"], "none")
        self.assertFalse(config["isolation"]["ephemeral_thread_start_per_run"])
        for paper_id, tier in (("P07", "T1"), ("P12", "T3")):
            task = read_json(self.root / "tasks" / paper_id / tier / "task.json")
            self.assertEqual(
                task["limits"],
                {"total_model_tokens": 120000, "wall_clock_seconds": 900},
            )
            self.assertNotIn("prompt_startup_timeout_seconds", task["limits"])
            self.assertNotIn(
                "post_submission_validation_reserve_seconds", task["limits"]
            )
        token_control = config["token_control"]
        self.assertEqual(token_control, environment["token_control"])
        self.assertEqual(token_control["limit_tokens"], 120000)
        self.assertEqual(
            token_control["control"], "loopback_provider_response_admission_gate"
        )
        self.assertFalse(token_control["concurrent_inflight_overshoot_possible"])
        self.assertTrue(token_control["one_response_overshoot_possible"])
        self.assertEqual(
            token_control["outcome_exactness"]["token_limit"][
                "provider_gate_close_reason"
            ],
            "token_limit",
        )
        for paper_id, tier in (("P07", "T1"), ("P12", "T3")):
            task = read_json(self.root / "tasks" / paper_id / tier / "task.json")
            paper = read_json(self.root / "tasks" / paper_id / "paper.json")
            self.assertIs(task["classification_frozen_before_runs"], False)
            self.assertIs(paper["classification_frozen_before_runs"], False)
            self.assertTrue(
                (self.root / "metadata" / "controlled" / f"{paper_id}-{tier}.json").is_file()
            )
            controlled = read_json(
                self.root / "metadata" / "controlled" / f"{paper_id}-{tier}.json"
            )
            controlled_paths = {entry["path"] for entry in controlled["files"]}
            self.assertNotIn("condition_prompts/L.md", controlled_paths)
            self.assertIn("shared/HighamBench/Core.lean", controlled_paths)
            self.assertIn(
                f"shared/HighamBench/{paper_id}Definitions.lean", controlled_paths
            )
            other = "P12" if paper_id == "P07" else "P07"
            self.assertNotIn(
                f"shared/HighamBench/{other}Definitions.lean", controlled_paths
            )
            target = next(
                item
                for entry in manifest["papers"]
                if entry["paper_id"] == paper_id
                for item in entry["targets"]
            )
            self.assertEqual(
                target["lean_target"]["controlled_file_sha256"],
                sha256_file(self.root / "tasks" / paper_id / tier / "Target.lean"),
            )

        run_order = read_json(self.root / "metadata" / "run_order.json")
        self.assertEqual(len(run_order["pairs"]), 4)
        self.assertEqual(run_order["method"]["version"], 2)
        self.assertNotIn("p01", run_order["method"]["salt"])
        release_paths = {
            item["path"]
            for item in read_json(self.root / "metadata" / "release_files.json")["files"]
        }
        self.assertIn("tasks/P07/T1/task.json", release_paths)
        self.assertIn("tasks/P12/T3/task.json", release_paths)
        self.assertIn("shared/HighamBench/Core.lean", release_paths)
        self.assertIn("shared/HighamBench/P07Definitions.lean", release_paths)
        self.assertIn("shared/HighamBench/P12Definitions.lean", release_paths)
        self.assertIn("condition_prompts/L.md", release_paths)
        self.assertIn("tools/provider_token_gate.py", release_paths)
        self.assertIn("tools/tests/test_provider_token_gate.py", release_paths)

        second = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        self.assertEqual(second["release_manifest_sha256"], first["release_manifest_sha256"])
        self.assertEqual(second["environment_bundle_sha256"], first["environment_bundle_sha256"])

        fixed_surface = {
            path.relative_to(self.root).as_posix(): sha256_file(path)
            for path in sorted((self.root / "tasks").rglob("*"))
            if path.is_file() and path.name in {"Target.lean", "context.md"}
        }
        l_prompt = self.root / "condition_prompts" / "L.md"
        l_prompt.write_text(
            l_prompt.read_text(encoding="utf-8") + "Search instructions revised.\n",
            encoding="utf-8",
        )
        revised = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        self.assertNotEqual(
            revised["release_manifest_sha256"], second["release_manifest_sha256"]
        )
        self.assertNotEqual(
            revised["environment_bundle_sha256"], second["environment_bundle_sha256"]
        )
        self.assertNotEqual(revised["environment_id"], second["environment_id"])
        self.assertEqual(
            fixed_surface,
            {
                path.relative_to(self.root).as_posix(): sha256_file(path)
                for path in sorted((self.root / "tasks").rglob("*"))
                if path.is_file() and path.name in {"Target.lean", "context.md"}
            },
        )

        with self.assertRaisesRegex(Exception, "passing full-corpus"):
            refresh_snapshot(self.root, phase=PHASE_MEASUREMENT_READY)

        task_ids = ["P07-T1", "P12-T3"]
        write_json(
            self.root / "metadata" / "evidence" / "construction_all.json",
            {
                "kind": "highambench-private-construction-check",
                "record_status": "current_final",
                "pass": True,
                "scope": {
                    "complete_manifest_scope": True,
                    "selected_task_ids": task_ids,
                    "central_manifest_sha256": sha256_file(
                        self.root / "metadata" / "manifest.json"
                    ),
                },
                "summary": {
                    "expected": 4,
                    "checked": 4,
                    "passed": 4,
                    "condition_n_passed": 2,
                    "condition_l_passed": 2,
                },
                "results": [
                    {"task_id": task_id, "condition": condition}
                    for task_id in task_ids
                    for condition in ("N", "L")
                ],
            },
        )
        for number in (1, 2):
            write_json(
                self.root / "metadata" / "reviews" / f"review_{number}.json",
                {
                    "record_status": "current_final",
                    "task_reviews": [
                        {"task_id": task_id, "outcome": "pass"} for task_id in task_ids
                    ],
                },
            )

        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")
        stale_descriptor = {
            "path": "metadata/evidence/stale-live-canary.json",
            "sha256": "f" * 64,
            "status": "passed",
        }
        config["frozen_environment"]["ultra_orchestration_canary"] = dict(
            stale_descriptor
        )
        config["frozen_environment"]["token_control_canary"] = dict(
            stale_descriptor
        )
        environment["ultra_orchestration_canary"] = dict(stale_descriptor)
        environment["token_control_canary"] = dict(stale_descriptor)
        write_json(self.root / "metadata" / "config.json", config)
        write_json(self.root / "metadata" / "environment.json", environment)

        ready = refresh_snapshot(self.root, phase=PHASE_MEASUREMENT_READY)
        self.assertEqual(ready["task_ids"], ["P07-T1", "P12-T3"])
        for paper_id, tier in (("P07", "T1"), ("P12", "T3")):
            task = read_json(self.root / "tasks" / paper_id / tier / "task.json")
            self.assertIs(task["classification_frozen_before_runs"], True)
        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")
        for key in ("ultra_orchestration_canary", "token_control_canary"):
            self.assertEqual(
                config["frozen_environment"][key]["status"],
                "replacement_required",
            )
            self.assertEqual(
                environment[key]["status"], "replacement_required"
            )
        self.assertEqual(
            environment["environment_bundle_sha256"],
            environment_bundle_digest(config, environment),
        )


if __name__ == "__main__":
    unittest.main()
