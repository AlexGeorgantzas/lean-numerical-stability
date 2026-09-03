from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, write_json  # noqa: E402
from task_tags import (  # noqa: E402
    ALLOWED_SOURCE_TAGS,
    T4_TASK_SCHEMA_VERSION,
    main,
    validate_t4_task_metadata,
    validate_task_catalog,
    validate_task_source_tags,
)


def base_task() -> dict:
    return {
        "schema_version": "highambench-task-0.3",
        "task_id": "P03-T1",
        "source_tags": ["EQN", "TXT"],
        "author_label": None,
        "classification_frozen_before_runs": False,
        "source_locations": [{"anchor": "equation (2.1) and following text"}],
    }


def accepted_review(
    *,
    review_order: int,
    review_id: str,
    review_unit_id: str,
    source_item_ids: list[str],
    declaration_ids: list[str],
    lean_names: list[str],
) -> dict:
    verdict = {
        "score": 3,
        "tag": "faithful-equivalent",
        "passed": True,
        "evidence": "All material mathematical content is preserved.",
        "discrepancies": [],
    }
    return {
        "review_order": review_order,
        "review_id": review_id,
        "review_unit_id": review_unit_id,
        "source_item_ids": list(source_item_ids),
        "declaration_ids": list(declaration_ids),
        "lean_names": list(lean_names),
        "revision": 1,
        "status": "accepted",
        "role_prompt_version": "t4-faithfulness-v1",
        "role_executions": {
            "direct_judge": {
                "agent_id": f"direct-agent-{review_order}",
                "model_identifier": "gpt-5.5",
            },
            "blind_translator": {
                "agent_id": f"translator-agent-{review_order}",
                "model_identifier": "gpt-5.5",
            },
            "round_trip_judge": {
                "agent_id": f"round-trip-agent-{review_order}",
                "model_identifier": "gpt-5.5",
            },
            "adjudicator": None,
        },
        "source_packet_sha256": "1" * 64,
        "lean_packet_sha256": "2" * 64,
        "locked_translation_sha256": "3" * 64,
        "direct_judge_output_sha256": "4" * 64,
        "round_trip_judge_output_sha256": "5" * 64,
        "adjudicator_output_sha256": None,
        "fresh_context": {
            "direct_judge": True,
            "blind_translator": True,
            "round_trip_judge": True,
            "adjudicator": False,
        },
        "blindness": {
            "direct_judge_received_only_packets": True,
            "translator_did_not_see_source": True,
            "round_trip_judge_did_not_see_lean": True,
            "roles_used_distinct_agents": True,
        },
        "direct_judge": copy.deepcopy(verdict),
        "round_trip_judge": copy.deepcopy(verdict),
        "adjudicator": None,
        "final_verdict": copy.deepcopy(verdict),
    }


def base_t4_task() -> dict:
    theorem_id = "P01-T4-D001"
    definition_id = "P01-T4-D002"
    transition_id = "P01-T4-D003"
    theorem_name = "HighamBench.P01T4.mainBound"
    definition_name = "HighamBench.P01T4.centralAlgorithm"
    transition_name = "HighamBench.P01T4.centralAlgorithmTransition"
    theorem_unit_id = "P01-T4-U001"
    algorithm_unit_id = "P01-T4-U002"
    return {
        "schema_version": "highambench-task-0.4",
        "task_id": "P01-T4",
        "paper_id": "P01",
        "tier": "T4",
        "classification_frozen_before_runs": False,
        "context_file": "paper_bencmark/highambench/tasks/P01/T4/context.md",
        "limits": {
            "total_model_tokens": 5_000_000,
            "wall_clock_seconds": 1_800,
        },
        "paper_source": {
            "local_path": "paper_bencmark/reference_papers/P01_TEST.pdf",
            "sha256": "f" * 64,
        },
        "construction_inputs": {
            "paper_definitions_sha256": "0" * 64,
            "source_inventory_sha256": "0" * 64,
            "target_sha256": "0" * 64,
            "review_campaign_status": "accepted",
        },
        "source_inventory_file": (
            "paper_bencmark/highambench/tasks/P01/T4/source_inventory.json"
        ),
        "source_inventory": [
            {
                "source_order": 1,
                "inventory_id": "P01-S001",
                "source_kind": "named_result",
                "source_locations": [
                    {
                        "pdf_page": 3,
                        "section": "2 Main result",
                        "anchor": "Theorem 2.1",
                    }
                ],
                "scope": "The theorem and its displayed conclusion.",
                "assumptions": [],
                "source_status": "assertive",
                "source_issue_notes": [],
                "source_tags": ["THM"],
                "author_label": "Theorem 2.1",
                "disposition": "included",
                "declaration_ids": [theorem_id, definition_id],
                "exclusion_reason": None,
                "declaration_mappings": [
                    {
                        "declaration_id": theorem_id,
                        "role": "primary_carrier",
                        "notes": "This theorem is part of the smallest carrier.",
                    },
                    {
                        "declaration_id": definition_id,
                        "role": "primary_carrier",
                        "notes": "This definition is part of the smallest carrier.",
                    },
                ],
                "duplicate_of_source_item_ids": [],
                "review_unit_id": theorem_unit_id,
                "smallest_group_reason": (
                    "The source theorem requires its primary statement and the "
                    "shared algorithm definition."
                ),
            },
            {
                "source_order": 2,
                "inventory_id": "P01-S002",
                "source_kind": "algorithm",
                "source_locations": [
                    {
                        "pdf_page": 4,
                        "section": "3 Algorithm",
                        "anchor": "Algorithm 1",
                    }
                ],
                "scope": "The complete state transformation.",
                "assumptions": [],
                "source_status": "definitional",
                "source_issue_notes": [],
                "source_tags": ["TXT"],
                "author_label": None,
                "disposition": "included",
                "declaration_ids": [definition_id, transition_id],
                "exclusion_reason": None,
                "declaration_mappings": [
                    {
                        "declaration_id": definition_id,
                        "role": "primary_carrier",
                        "notes": "This definition is part of the smallest carrier.",
                    },
                    {
                        "declaration_id": transition_id,
                        "role": "primary_carrier",
                        "notes": "This transition is part of the smallest carrier.",
                    },
                ],
                "duplicate_of_source_item_ids": [],
                "review_unit_id": algorithm_unit_id,
                "smallest_group_reason": (
                    "The algorithm claim requires its transparent definition and "
                    "transition specification together."
                ),
            },
            {
                "source_order": 3,
                "inventory_id": "P01-S003",
                "source_kind": "question",
                "source_locations": [
                    {
                        "pdf_page": 8,
                        "section": "6 Discussion",
                        "anchor": "Open question paragraph",
                    }
                ],
                "scope": "An explicitly unresolved question.",
                "assumptions": [],
                "source_status": "question",
                "source_issue_notes": [],
                "source_tags": ["TXT"],
                "author_label": None,
                "disposition": "excluded",
                "declaration_ids": [],
                "exclusion_reason": "The paper does not assert an answer.",
                "declaration_mappings": [],
                "duplicate_of_source_item_ids": [],
                "review_unit_id": None,
                "smallest_group_reason": None,
            },
        ],
        "declarations": [
            {
                "declaration_order": 1,
                "declaration_id": theorem_id,
                "lean_name": theorem_name,
                "controlled_source_file": (
                    "paper_bencmark/highambench/tasks/P01/T4/Target.lean"
                ),
                "controlled_source_line": 40,
                "declaration_kind": "theorem",
                "source_kind": "named_result",
                "source_tags": ["THM"],
                "author_label": "Theorem 2.1",
                "result_form_tag": "BND",
                "source_item_ids": ["P01-S001"],
                "semantic_dependency_hashes": [
                    {
                        "declaration": definition_name,
                        "sha256": "a" * 64,
                    }
                ],
                "placeholder_id": "P01-T4-H001",
            },
            {
                "declaration_order": 2,
                "declaration_id": definition_id,
                "lean_name": definition_name,
                "controlled_source_file": (
                    "paper_bencmark/highambench/shared/HighamBench/"
                    "P01Definitions.lean"
                ),
                "controlled_source_line": 10,
                "declaration_kind": "definition",
                "source_kind": "algorithm",
                "source_tags": ["TXT"],
                "author_label": None,
                "result_form_tag": None,
                "source_item_ids": ["P01-S001", "P01-S002"],
                "semantic_dependency_hashes": [
                    {
                        "declaration": transition_name,
                        "sha256": "b" * 64,
                    }
                ],
                "placeholder_id": None,
            },
            {
                "declaration_order": 3,
                "declaration_id": transition_id,
                "lean_name": transition_name,
                "controlled_source_file": (
                    "paper_bencmark/highambench/shared/HighamBench/"
                    "P01Definitions.lean"
                ),
                "controlled_source_line": 20,
                "declaration_kind": "definition",
                "source_kind": "algorithm",
                "source_tags": ["TXT"],
                "author_label": None,
                "result_form_tag": None,
                "source_item_ids": ["P01-S002"],
                "semantic_dependency_hashes": [],
                "placeholder_id": None,
            },
        ],
        "review_units": [
            {
                "review_unit_order": 1,
                "review_unit_id": theorem_unit_id,
                "source_item_ids": ["P01-S001"],
                "smallest_group_reason": (
                    "The source theorem requires its primary statement and the "
                    "shared algorithm definition."
                ),
                "declaration_ids": [theorem_id, definition_id],
                "reused_declaration_ids": [definition_id],
                "review_id": "P01-T4-R001",
                "review_status": "accepted",
            },
            {
                "review_unit_order": 2,
                "review_unit_id": algorithm_unit_id,
                "source_item_ids": ["P01-S002"],
                "smallest_group_reason": (
                    "The algorithm claim requires its transparent definition and "
                    "transition specification together."
                ),
                "declaration_ids": [definition_id, transition_id],
                "reused_declaration_ids": [definition_id],
                "review_id": "P01-T4-R002",
                "review_status": "accepted",
            },
        ],
        "validation": {
            "controlled_target_file": (
                "paper_bencmark/highambench/tasks/P01/T4/Target.lean"
            ),
            "required_declarations": [
                theorem_name,
                definition_name,
                transition_name,
            ],
            "controlled_sorries": [
                {
                    "placeholder_order": 1,
                    "placeholder_id": "P01-T4-H001",
                    "declaration_id": theorem_id,
                    "lean_name": theorem_name,
                    "marker": "-- PROOF_START P01-T4-H001",
                    "line": 40,
                    "column": 3,
                }
            ],
        },
        "faithfulness_reviews": [
            accepted_review(
                review_order=1,
                review_id="P01-T4-R001",
                review_unit_id=theorem_unit_id,
                source_item_ids=["P01-S001"],
                declaration_ids=[theorem_id, definition_id],
                lean_names=[theorem_name, definition_name],
            ),
            accepted_review(
                review_order=2,
                review_id="P01-T4-R002",
                review_unit_id=algorithm_unit_id,
                source_item_ids=["P01-S002"],
                declaration_ids=[definition_id, transition_id],
                lean_names=[definition_name, transition_name],
            ),
        ],
    }


def t4_task_with_semantic_context_only_declaration() -> dict:
    task = base_t4_task()
    algorithm_item = task["source_inventory"][1]
    algorithm_item["declaration_ids"] = ["P01-T4-D002"]
    algorithm_item["declaration_mappings"][1]["role"] = "semantic_context"
    algorithm_item["declaration_mappings"][1]["notes"] = (
        "This transition is context needed to interpret the primary carrier."
    )

    algorithm_unit = task["review_units"][1]
    algorithm_unit["declaration_ids"] = ["P01-T4-D002"]
    algorithm_review = task["faithfulness_reviews"][1]
    algorithm_review["declaration_ids"] = ["P01-T4-D002"]
    algorithm_review["lean_names"] = ["HighamBench.P01T4.centralAlgorithm"]
    return task


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stage_t4_task(root: Path, task: dict | None = None) -> dict:
    task = copy.deepcopy(base_t4_task() if task is None else task)
    definitions = root / "shared" / "HighamBench" / "P01Definitions.lean"
    target = root / "tasks" / "P01" / "T4" / "Target.lean"
    inventory = root / "tasks" / "P01" / "T4" / "source_inventory.json"
    definitions.parent.mkdir(parents=True, exist_ok=True)
    target.parent.mkdir(parents=True, exist_ok=True)
    definitions.write_text("import Mathlib\nnamespace HighamBench\ndef P01T4.centralAlgorithm := 0\ndef P01T4.centralAlgorithmTransition := 0\nend HighamBench\n")
    target.write_text("import HighamBench.P01Definitions\nnamespace HighamBench\ntheorem P01T4.mainBound : True := by sorry\nend HighamBench\n")
    write_json(
        inventory,
        {
            "schema_version": "highambench-t4-source-inventory-0.3",
            "paper_id": "P01",
            "title": "Synthetic T4 paper",
            "status": "construction",
            "inventory_method": "Synthetic complete source-order inventory.",
            "source": copy.deepcopy(task["paper_source"]),
            "named_results": ["Theorem 2.1"],
            "local_numbered_equations": [],
            "items": copy.deepcopy(task["source_inventory"]),
        },
    )
    task["construction_inputs"].update(
        {
            "paper_definitions_sha256": _sha256(definitions),
            "source_inventory_sha256": _sha256(inventory),
            "target_sha256": _sha256(target),
        }
    )
    write_json(root / "tasks" / "P01" / "T4" / "task.json", task)
    return task


class TaskTagTests(unittest.TestCase):
    def test_allowed_vocabulary_is_compact_and_fixed(self) -> None:
        self.assertEqual(
            ALLOWED_SOURCE_TAGS,
            ("THM", "LEM", "PROP", "COR", "EQN", "TXT", "UNL"),
        )

    def test_accepts_numbered_equation_with_essential_prose(self) -> None:
        result = validate_task_source_tags(base_task())
        self.assertEqual(result["source_tags"], ["EQN", "TXT"])
        self.assertIsNone(result["author_label"])

    def test_accepts_explicit_proposition_with_exact_label(self) -> None:
        task = base_task()
        task["source_tags"] = ["PROP"]
        task["author_label"] = "Proposition 4.5"
        result = validate_task_source_tags(task)
        self.assertEqual(result["author_label"], "Proposition 4.5")

        task["source_tags"] = ["THM"]
        task["author_label"] = "THEOREM 3.4"
        result = validate_task_source_tags(task)
        self.assertEqual(result["author_label"], "THEOREM 3.4")

    def test_rejects_malformed_tag_metadata(self) -> None:
        cases = {
            "old schema": {"schema_version": "highambench-task-0.2"},
            "missing tags": {"source_tags": None},
            "unknown tag": {"source_tags": ["OTHER"]},
            "duplicate": {"source_tags": ["EQN", "EQN"]},
            "wrong order": {"source_tags": ["TXT", "EQN"]},
            "named mixed with equation": {
                "source_tags": ["THM", "EQN"],
                "author_label": "Theorem 2.1",
            },
            "named without label": {"source_tags": ["LEM"], "author_label": None},
            "wrong named label": {
                "source_tags": ["COR"],
                "author_label": "Theorem 5.1",
            },
            "label on equation": {
                "source_tags": ["EQN"],
                "author_label": "Equation 2.1",
            },
            "numbered and unnumbered": {"source_tags": ["EQN", "UNL"]},
            "invalid construction state": {"classification_frozen_before_runs": "no"},
            "no evidence": {"source_locations": []},
        }
        for name, changes in cases.items():
            with self.subTest(name=name):
                task = copy.deepcopy(base_task())
                task.update(changes)
                with self.assertRaises(BenchmarkToolError):
                    validate_task_source_tags(task)

    def test_catalog_checks_path_identity_and_cli(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            task_path = root / "tasks" / "P03" / "T1" / "task.json"
            write_json(task_path, base_task())
            result = validate_task_catalog(root)
            self.assertEqual(result["task_count"], 1)
            self.assertEqual(main(["--benchmark-root", str(root)]), 0)

            changed = base_task()
            changed["task_id"] = "P99-T1"
            write_json(task_path, changed)
            with self.assertRaises(BenchmarkToolError):
                validate_task_catalog(root)

    def test_catalog_can_validate_one_paper_without_reading_a_peer(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            write_json(root / "tasks" / "P03" / "T1" / "task.json", base_task())
            malformed_peer = base_task()
            malformed_peer["task_id"] = "P99-T1"
            write_json(root / "tasks" / "P04" / "T1" / "task.json", malformed_peer)

            result = validate_task_catalog(root, paper_id="P03")
            self.assertEqual(result["paper_id"], "P03")
            self.assertEqual(result["task_count"], 1)
            self.assertEqual(
                main(["--benchmark-root", str(root), "--paper-id", "P03"]), 0
            )
            with self.assertRaises(BenchmarkToolError):
                validate_task_catalog(root)
            with self.assertRaises(BenchmarkToolError):
                validate_task_catalog(root, paper_id="not-a-paper")

    def test_real_catalog_has_tags_for_all_current_tasks(self) -> None:
        result = validate_task_catalog(TOOLS.parent)
        paths = sorted((TOOLS.parent / "tasks").glob("P*/T*/task.json"))
        self.assertEqual(result["task_count"], len(paths))
        self.assertGreater(result["task_count"], 0)
        self.assertTrue(
            all(
                row.get("source_tags") or row.get("tier") == "T4"
                for row in result["tasks"]
            )
        )


class TierFourTaskMetadataTests(unittest.TestCase):
    def test_t4_schema_is_separate_and_accepts_complete_record(self) -> None:
        self.assertEqual(T4_TASK_SCHEMA_VERSION, "highambench-task-0.4")
        result = validate_t4_task_metadata(base_t4_task())
        self.assertEqual(result["tier"], "T4")
        self.assertEqual(result["source_inventory_count"], 3)
        self.assertEqual(result["included_source_count"], 2)
        self.assertEqual(result["excluded_source_count"], 1)
        self.assertEqual(result["declaration_count"], 3)
        self.assertEqual(result["review_unit_count"], 2)
        self.assertEqual(result["controlled_sorry_count"], 1)
        self.assertEqual(result["review_count"], 2)

        dispatched = validate_task_source_tags(base_t4_task())
        self.assertEqual(dispatched, result)

    def test_rejects_shared_core_or_paper_specific_construction_bindings(self) -> None:
        for field in ("semantic_core_sha256", "p01_definitions_sha256"):
            with self.subTest(field=field):
                task = base_t4_task()
                task["construction_inputs"][field] = "a" * 64
                with self.assertRaisesRegex(
                    BenchmarkToolError, "paper-neutral definitions"
                ):
                    validate_t4_task_metadata(task)

    def test_catalog_authenticates_paper_local_t4_file_hashes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            stage_t4_task(root)
            self.assertEqual(validate_task_catalog(root)["task_count"], 1)
            inventory = root / "tasks" / "P01" / "T4" / "source_inventory.json"
            inventory.write_text(inventory.read_text() + "\n")
            with self.assertRaisesRegex(
                BenchmarkToolError, "source_inventory_sha256 does not match"
            ):
                validate_task_catalog(root)

            external = json.loads(inventory.read_text())
            external["items"][0]["scope"] = "Semantically drifted scope."
            write_json(inventory, external)
            task_path = root / "tasks" / "P01" / "T4" / "task.json"
            task = json.loads(task_path.read_text())
            task["construction_inputs"]["source_inventory_sha256"] = _sha256(
                inventory
            )
            write_json(task_path, task)
            with self.assertRaisesRegex(
                BenchmarkToolError, "external items must exactly equal"
            ):
                validate_task_catalog(root)

    def test_accepts_uniform_pre_review_construction_state(self) -> None:
        task = base_t4_task()
        for unit in task["review_units"]:
            unit["review_status"] = "pending"
        task["faithfulness_reviews"] = []
        task["construction_inputs"]["review_campaign_status"] = "not_started"

        result = validate_t4_task_metadata(task)

        self.assertEqual(result["review_status"], "pending")
        self.assertEqual(result["review_count"], 0)
        self.assertFalse(result["measurement_ready"])

    def test_rejects_pending_review_state_with_evidence_or_frozen_classification(
        self,
    ) -> None:
        pending_with_evidence = base_t4_task()
        for unit in pending_with_evidence["review_units"]:
            unit["review_status"] = "pending"
        pending_with_evidence["construction_inputs"]["review_campaign_status"] = (
            "not_started"
        )
        with self.assertRaisesRegex(
            BenchmarkToolError, "faithfulness_reviews must be empty"
        ):
            validate_t4_task_metadata(pending_with_evidence)

        frozen_pending = base_t4_task()
        for unit in frozen_pending["review_units"]:
            unit["review_status"] = "pending"
        frozen_pending["faithfulness_reviews"] = []
        frozen_pending["classification_frozen_before_runs"] = True
        frozen_pending["construction_inputs"]["review_campaign_status"] = (
            "not_started"
        )
        with self.assertRaisesRegex(
            BenchmarkToolError, "cannot freeze classification"
        ):
            validate_t4_task_metadata(frozen_pending)

    def test_t4_catalog_coexists_with_legacy_and_cli(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            stage_t4_task(root)
            write_json(root / "tasks" / "P03" / "T1" / "task.json", base_task())
            result = validate_task_catalog(root)
            self.assertEqual(result["task_count"], 2)
            self.assertEqual(
                {row["task_id"] for row in result["tasks"]}, {"P01-T4", "P03-T1"}
            )
            self.assertEqual(main(["--benchmark-root", str(root)]), 0)

    def test_rejects_incomplete_inventory_and_non_bidirectional_mappings(self) -> None:
        cases = {}

        wrong_order = base_t4_task()
        wrong_order["source_inventory"][1]["source_order"] = 3
        cases["inventory order"] = wrong_order

        included_without_mapping = base_t4_task()
        included_without_mapping["source_inventory"][0]["declaration_ids"] = []
        cases["included without mapping"] = included_without_mapping

        missing_reverse = base_t4_task()
        missing_reverse["declarations"][0]["source_item_ids"] = ["P01-S002"]
        cases["missing reverse mapping"] = missing_reverse

        excluded_with_mapping = base_t4_task()
        excluded_with_mapping["source_inventory"][2]["declaration_ids"] = [
            "P01-T4-D002"
        ]
        cases["excluded mapping"] = excluded_with_mapping

        duplicate_inventory_id = base_t4_task()
        duplicate_inventory_id["source_inventory"][1]["inventory_id"] = "P01-S001"
        cases["duplicate inventory id"] = duplicate_inventory_id

        for name, task in cases.items():
            with self.subTest(name=name):
                with self.assertRaises(BenchmarkToolError):
                    validate_t4_task_metadata(task)

    def test_accepts_claim_scoped_units_with_controlled_declaration_overlap(
        self,
    ) -> None:
        task = base_t4_task()
        shared_declaration = "P01-T4-D002"
        self.assertIn(shared_declaration, task["review_units"][0]["declaration_ids"])
        self.assertIn(shared_declaration, task["review_units"][1]["declaration_ids"])
        self.assertEqual(
            task["review_units"][0]["reused_declaration_ids"],
            [shared_declaration],
        )
        self.assertEqual(
            task["review_units"][1]["reused_declaration_ids"],
            [shared_declaration],
        )
        validate_t4_task_metadata(task)

    def test_semantic_context_backlinks_without_becoming_review_carriers(
        self,
    ) -> None:
        task = t4_task_with_semantic_context_only_declaration()

        result = validate_t4_task_metadata(task)

        self.assertEqual(result["declaration_count"], 3)
        self.assertEqual(
            task["source_inventory"][1]["declaration_ids"], ["P01-T4-D002"]
        )
        self.assertEqual(
            task["review_units"][1]["declaration_ids"], ["P01-T4-D002"]
        )
        self.assertNotIn(
            "P01-T4-D003",
            {
                declaration_id
                for unit in task["review_units"]
                for declaration_id in unit["declaration_ids"]
            },
        )

        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            stage_t4_task(root, task)
            self.assertEqual(validate_task_catalog(root)["task_count"], 1)

    def test_semantic_context_mappings_remain_strictly_bidirectional(self) -> None:
        missing_declaration_backlink = (
            t4_task_with_semantic_context_only_declaration()
        )
        missing_declaration_backlink["declarations"][2]["source_item_ids"] = [
            "P01-S001"
        ]
        with self.assertRaisesRegex(BenchmarkToolError, "not bidirectional"):
            validate_t4_task_metadata(missing_declaration_backlink)

        missing_inventory_mapping = t4_task_with_semantic_context_only_declaration()
        missing_inventory_mapping["source_inventory"][1][
            "declaration_mappings"
        ].pop()
        with self.assertRaisesRegex(BenchmarkToolError, "not bidirectional"):
            validate_t4_task_metadata(missing_inventory_mapping)

    def test_semantic_context_is_rejected_from_carrier_only_lists(self) -> None:
        item_includes_context = t4_task_with_semantic_context_only_declaration()
        item_includes_context["source_inventory"][1]["declaration_ids"].append(
            "P01-T4-D003"
        )
        with self.assertRaisesRegex(BenchmarkToolError, "primary-carrier"):
            validate_t4_task_metadata(item_includes_context)

        unit_includes_context = t4_task_with_semantic_context_only_declaration()
        unit_includes_context["review_units"][1]["declaration_ids"].append(
            "P01-T4-D003"
        )
        with self.assertRaisesRegex(BenchmarkToolError, "declaration-order union"):
            validate_t4_task_metadata(unit_includes_context)

    def test_rejects_duplicate_or_incomplete_review_unit_source_coverage(
        self,
    ) -> None:
        missing_source = base_t4_task()
        missing_source["review_units"].pop()
        missing_source["faithfulness_reviews"].pop()
        with self.assertRaisesRegex(
            BenchmarkToolError, "do not cover included source items"
        ):
            validate_t4_task_metadata(missing_source)

        duplicate_source = base_t4_task()
        duplicate_source["review_units"][1]["source_item_ids"] = [
            "P01-S001",
            "P01-S002",
        ]
        duplicate_source["review_units"][1]["declaration_ids"] = [
            "P01-T4-D001",
            "P01-T4-D002",
            "P01-T4-D003",
        ]
        with self.assertRaisesRegex(
            BenchmarkToolError, "occur in more than one review unit"
        ):
            validate_t4_task_metadata(duplicate_source)

        excluded_source = base_t4_task()
        excluded_source["review_units"][1]["source_item_ids"] = ["P01-S003"]
        with self.assertRaisesRegex(BenchmarkToolError, "maps excluded source items"):
            validate_t4_task_metadata(excluded_source)

    def test_rejects_duplicate_review_units_with_identical_sets(self) -> None:
        task = base_t4_task()
        duplicate = copy.deepcopy(task["review_units"][0])
        duplicate.update(
            {
                "review_unit_order": 3,
                "review_unit_id": "P01-T4-U003",
                "review_id": "P01-T4-R003",
            }
        )
        task["review_units"].append(duplicate)
        with self.assertRaisesRegex(
            BenchmarkToolError, "duplicates the source-item/declaration sets"
        ):
            validate_t4_task_metadata(task)

    def test_rejects_bad_review_unit_group_union_reason_or_reused_list(
        self,
    ) -> None:
        bad_union = base_t4_task()
        bad_union["review_units"][1]["declaration_ids"].pop()
        with self.assertRaisesRegex(BenchmarkToolError, "declaration-order union"):
            validate_t4_task_metadata(bad_union)

        extra_declaration = base_t4_task()
        extra_declaration["review_units"][1]["declaration_ids"].insert(
            0, "P01-T4-D001"
        )
        with self.assertRaisesRegex(BenchmarkToolError, "declaration-order union"):
            validate_t4_task_metadata(extra_declaration)

        blank_reason = base_t4_task()
        blank_reason["review_units"][0]["smallest_group_reason"] = " "
        with self.assertRaisesRegex(BenchmarkToolError, "nonempty string"):
            validate_t4_task_metadata(blank_reason)

        bad_reused_list = base_t4_task()
        bad_reused_list["review_units"][0]["reused_declaration_ids"] = []
        with self.assertRaisesRegex(
            BenchmarkToolError, "reused_declaration_ids must exactly list"
        ):
            validate_t4_task_metadata(bad_reused_list)

    def test_rejects_bad_review_unit_source_or_unit_order(self) -> None:
        wrong_source_order = base_t4_task()
        wrong_source_order["review_units"][1]["source_item_ids"] = [
            "P01-S002",
            "P01-S001",
        ]
        with self.assertRaisesRegex(
            BenchmarkToolError, "source_item_ids must follow source_order"
        ):
            validate_t4_task_metadata(wrong_source_order)

        wrong_unit_order = base_t4_task()
        wrong_unit_order["review_units"].reverse()
        for index, unit in enumerate(wrong_unit_order["review_units"], start=1):
            unit["review_unit_order"] = index
        with self.assertRaisesRegex(
            BenchmarkToolError, "earliest source_order"
        ):
            validate_t4_task_metadata(wrong_unit_order)

    def test_rejects_other_invalid_review_unit_declaration_metadata(self) -> None:
        cases = {}

        unknown_declaration = base_t4_task()
        unknown_declaration["review_units"][1]["declaration_ids"][1] = "P01-T4-D999"
        cases["unknown declaration"] = unknown_declaration

        wrong_declaration_order = base_t4_task()
        wrong_declaration_order["review_units"][1]["declaration_ids"].reverse()
        cases["wrong declaration order"] = wrong_declaration_order

        duplicate_review_id = base_t4_task()
        duplicate_review_id["review_units"][1]["review_id"] = "P01-T4-R001"
        cases["duplicate review id"] = duplicate_review_id

        declaration_review_field = base_t4_task()
        declaration_review_field["declarations"][0]["review_id"] = "P01-T4-R001"
        cases["review field on declaration"] = declaration_review_field

        for name, task in cases.items():
            with self.subTest(name=name):
                with self.assertRaises(BenchmarkToolError):
                    validate_t4_task_metadata(task)

    def test_rejects_compressed_or_incomplete_declaration_validation(self) -> None:
        cases = {}

        aggregate_tags = base_t4_task()
        aggregate_tags["source_tags"] = ["THM"]
        cases["aggregate tags"] = aggregate_tags

        singular_required = base_t4_task()
        singular_required["validation"]["required_declaration"] = (
            "HighamBench.P01T4.mainBound"
        )
        cases["singular required declaration"] = singular_required

        wrong_required_order = base_t4_task()
        wrong_required_order["validation"]["required_declarations"].reverse()
        cases["wrong required order"] = wrong_required_order

        missing_sorry = base_t4_task()
        missing_sorry["validation"]["controlled_sorries"] = []
        cases["missing controlled sorry"] = missing_sorry

        wrong_marker = base_t4_task()
        wrong_marker["validation"]["controlled_sorries"][0]["marker"] = "-- proof"
        cases["wrong marker"] = wrong_marker

        definition_with_placeholder = base_t4_task()
        definition_with_placeholder["declarations"][1]["placeholder_id"] = "P01-T4-H002"
        cases["definition placeholder"] = definition_with_placeholder

        invalid_dependency_hash = base_t4_task()
        invalid_dependency_hash["declarations"][0]["semantic_dependency_hashes"][0][
            "sha256"
        ] = "ABC"
        cases["dependency hash"] = invalid_dependency_hash

        missing_controlled_owner = base_t4_task()
        missing_controlled_owner["declarations"][1].pop("controlled_source_file")
        cases["missing controlled owner"] = missing_controlled_owner

        proof_in_shared_file = base_t4_task()
        proof_in_shared_file["declarations"][0]["controlled_source_file"] = (
            "paper_bencmark/highambench/shared/HighamBench/P01Definitions.lean"
        )
        cases["proof outside target"] = proof_in_shared_file

        foreign_controlled_owner = base_t4_task()
        foreign_controlled_owner["declarations"][1]["controlled_source_file"] = (
            "paper_bencmark/highambench/shared/HighamBench/P02Definitions.lean"
        )
        cases["foreign controlled owner"] = foreign_controlled_owner

        for name, task in cases.items():
            with self.subTest(name=name):
                with self.assertRaises(BenchmarkToolError):
                    validate_t4_task_metadata(task)

    def test_rejects_unaccepted_or_procedurally_invalid_reviews(self) -> None:
        cases = {}

        missing_review = base_t4_task()
        missing_review["faithfulness_reviews"].pop()
        cases["missing review"] = missing_review

        review_unit_not_accepted = base_t4_task()
        review_unit_not_accepted["review_units"][0]["review_status"] = "pending"
        cases["review unit pending"] = review_unit_not_accepted

        mismatched_unit = base_t4_task()
        mismatched_unit["faithfulness_reviews"][0]["review_unit_id"] = "P01-T4-U002"
        cases["review unit mismatch"] = mismatched_unit

        mismatched_sources = base_t4_task()
        mismatched_sources["faithfulness_reviews"][0]["source_item_ids"] = [
            "P01-S002"
        ]
        cases["review source items mismatch"] = mismatched_sources

        missing_sources = base_t4_task()
        missing_sources["faithfulness_reviews"][0].pop("source_item_ids")
        cases["review source items missing"] = missing_sources

        mismatched_declarations = base_t4_task()
        mismatched_declarations["faithfulness_reviews"][1]["declaration_ids"].pop()
        cases["review declarations mismatch"] = mismatched_declarations

        mismatched_names = base_t4_task()
        mismatched_names["faithfulness_reviews"][1]["lean_names"].reverse()
        cases["review names mismatch"] = mismatched_names

        singular_review_mapping = base_t4_task()
        singular_review_mapping["faithfulness_reviews"][0]["declaration_id"] = (
            "P01-T4-D001"
        )
        cases["singular declaration mapping"] = singular_review_mapping

        review_not_accepted = base_t4_task()
        review_not_accepted["faithfulness_reviews"][0]["status"] = "rejected"
        cases["review not accepted"] = review_not_accepted

        stale_direct_context = base_t4_task()
        stale_direct_context["faithfulness_reviews"][0]["fresh_context"][
            "direct_judge"
        ] = False
        cases["stale direct context"] = stale_direct_context

        translator_saw_source = base_t4_task()
        translator_saw_source["faithfulness_reviews"][0]["blindness"][
            "translator_did_not_see_source"
        ] = False
        cases["translator saw source"] = translator_saw_source

        invalid_packet_hash = base_t4_task()
        invalid_packet_hash["faithfulness_reviews"][0]["lean_packet_sha256"] = "bad"
        cases["invalid packet hash"] = invalid_packet_hash

        agreed_failure = base_t4_task()
        failing = {
            "score": 2,
            "tag": "semantic-mismatch",
            "passed": False,
            "evidence": "The formal statement drops a material source condition.",
            "discrepancies": ["A material source condition is absent."],
        }
        for field in ("direct_judge", "round_trip_judge", "final_verdict"):
            agreed_failure["faithfulness_reviews"][0][field] = copy.deepcopy(failing)
        cases["agreed failure"] = agreed_failure

        missing_adjudication = base_t4_task()
        missing_adjudication["faithfulness_reviews"][0]["round_trip_judge"] = {
            "score": 4,
            "tag": "faithful-stronger",
            "passed": True,
            "evidence": "The reconstruction states a valid strengthening.",
            "discrepancies": [],
        }
        cases["tag disagreement without adjudication"] = missing_adjudication

        for name, task in cases.items():
            with self.subTest(name=name):
                with self.assertRaises(BenchmarkToolError):
                    validate_t4_task_metadata(task)

    def test_rejects_missing_review_reproducibility_or_evidence(self) -> None:
        cases = {}

        blank_prompt_version = base_t4_task()
        blank_prompt_version["faithfulness_reviews"][0]["role_prompt_version"] = " "
        cases["blank role prompt version"] = blank_prompt_version

        missing_role_executions = base_t4_task()
        missing_role_executions["faithfulness_reviews"][0].pop("role_executions")
        cases["missing role executions"] = missing_role_executions

        missing_role = base_t4_task()
        missing_role["faithfulness_reviews"][0]["role_executions"].pop(
            "blind_translator"
        )
        cases["missing translator execution"] = missing_role

        unstable_agent_id = base_t4_task()
        unstable_agent_id["faithfulness_reviews"][0]["role_executions"][
            "direct_judge"
        ]["agent_id"] = "not a stable id"
        cases["unstable agent id"] = unstable_agent_id

        blank_model_identifier = base_t4_task()
        blank_model_identifier["faithfulness_reviews"][0]["role_executions"][
            "round_trip_judge"
        ]["model_identifier"] = ""
        cases["blank model identifier"] = blank_model_identifier

        reused_agent = base_t4_task()
        executions = reused_agent["faithfulness_reviews"][0]["role_executions"]
        executions["round_trip_judge"]["agent_id"] = executions["direct_judge"][
            "agent_id"
        ]
        cases["agent reused across roles"] = reused_agent

        reused_across_reviews = base_t4_task()
        reused_across_reviews["faithfulness_reviews"][1]["role_executions"][
            "direct_judge"
        ]["agent_id"] = "direct-agent-1"
        cases["agent reused across review units"] = reused_across_reviews

        missing_adjudicator_slot = base_t4_task()
        missing_adjudicator_slot["faithfulness_reviews"][0]["role_executions"].pop(
            "adjudicator"
        )
        cases["missing adjudicator execution slot"] = missing_adjudicator_slot

        spurious_adjudicator_execution = base_t4_task()
        spurious_adjudicator_execution["faithfulness_reviews"][0]["role_executions"][
            "adjudicator"
        ] = {
            "agent_id": "adjudicator-agent-1",
            "model_identifier": "gpt-5.5",
        }
        cases["adjudicator execution without disagreement"] = (
            spurious_adjudicator_execution
        )

        missing_adjudicator_execution = base_t4_task()
        review = missing_adjudicator_execution["faithfulness_reviews"][0]
        review["round_trip_judge"].update(
            {
                "score": 4,
                "tag": "faithful-stronger",
                "evidence": "The reconstruction states a valid strengthening.",
            }
        )
        review["fresh_context"]["adjudicator"] = True
        review["adjudicator_output_sha256"] = "6" * 64
        review["adjudicator"] = copy.deepcopy(review["direct_judge"])
        review["adjudicator"]["score"] = 3
        review["adjudicator"]["evidence"] = "The tag disagreement is resolved."
        review["final_verdict"] = copy.deepcopy(review["adjudicator"])
        cases["adjudication without execution identity"] = (
            missing_adjudicator_execution
        )

        missing_evidence = base_t4_task()
        missing_evidence["faithfulness_reviews"][0]["direct_judge"].pop("evidence")
        cases["missing verdict evidence"] = missing_evidence

        blank_evidence = base_t4_task()
        blank_evidence["faithfulness_reviews"][0]["final_verdict"]["evidence"] = ""
        cases["blank final evidence"] = blank_evidence

        discrepancies_not_list = base_t4_task()
        discrepancies_not_list["faithfulness_reviews"][0]["round_trip_judge"][
            "discrepancies"
        ] = "none"
        cases["discrepancies not list"] = discrepancies_not_list

        nonstring_discrepancy = base_t4_task()
        nonstring_discrepancy["faithfulness_reviews"][0]["direct_judge"][
            "discrepancies"
        ] = [7]
        cases["nonstring discrepancy"] = nonstring_discrepancy

        for name, task in cases.items():
            with self.subTest(name=name):
                with self.assertRaises(BenchmarkToolError):
                    validate_t4_task_metadata(task)

    def test_passing_scores_require_their_exact_semantic_tags(self) -> None:
        cases = {
            "score 4 cannot mean equivalent": (4, "faithful-equivalent"),
            "score 3 cannot mean stronger": (3, "faithful-stronger"),
        }
        for name, (score, tag) in cases.items():
            with self.subTest(name=name):
                task = base_t4_task()
                verdict = task["faithfulness_reviews"][0]["direct_judge"]
                verdict["score"] = score
                verdict["tag"] = tag
                with self.assertRaisesRegex(BenchmarkToolError, "reserved for"):
                    validate_t4_task_metadata(task)

    def test_tag_disagreement_requires_and_accepts_fresh_adjudication(self) -> None:
        task = base_t4_task()
        review = task["faithfulness_reviews"][0]
        review["round_trip_judge"] = {
            "score": 4,
            "tag": "faithful-stronger",
            "passed": True,
            "evidence": "The reconstruction states a valid strengthening.",
            "discrepancies": [],
        }
        review["fresh_context"]["adjudicator"] = True
        review["role_executions"]["adjudicator"] = {
            "agent_id": "adjudicator-agent-1",
            "model_identifier": "gpt-5.5",
        }
        review["adjudicator_output_sha256"] = "6" * 64
        review["adjudicator"] = {
            "score": 3,
            "tag": "faithful-equivalent",
            "passed": True,
            "evidence": "The differing tags resolve to semantic equivalence.",
            "discrepancies": [],
        }
        review["final_verdict"] = copy.deepcopy(review["adjudicator"])
        review["final_verdict"]["evidence"] = (
            "The adjudicator's controlling semantic verdict is accepted."
        )
        validate_t4_task_metadata(task)
