from __future__ import annotations

import json
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import finalize_audit
import split_paper_source_contract
from apply_dependency_reuse import dossier_sections
from common import AUDIT_SCHEMA_VERSION, SEMANTIC_CHECKS, implication_classification
from prepare_audit import (
    HIGHAMBENCH_ROOT,
    archive_existing_output,
    collect_local_imports,
    dependency_fingerprint,
    direct_imports,
    parse_task_id,
    parse_lean_report,
    theorem_source,
)
from prepare_paper_audit import paper_task_ids
from validate_audit import output_requires_adjudication

AUDIT_ROOT = SCRIPT_DIR.parent


class AuditSetupTests(unittest.TestCase):
    def test_task_id_normalization(self) -> None:
        self.assertEqual(parse_task_id("p11-t1"), ("P11", "T1"))
        with self.assertRaises(RuntimeError):
            parse_task_id("P11/T1")

    def test_import_parser_ignores_non_import_text(self) -> None:
        source = "import HighamBench.Core\n-- import Fake.Module\nnamespace X\n"
        self.assertEqual(direct_imports(source), ["HighamBench.Core"])

    def test_p11_import_closure(self) -> None:
        target = HIGHAMBENCH_ROOT / "tasks" / "P11" / "T1" / "Target.lean"
        order, graph, external = collect_local_imports(target.read_text(encoding="utf-8"))
        self.assertEqual(order, ["HighamBench.Core", "HighamBench.P11Definitions"])
        self.assertIn("Mathlib.Analysis.Matrix.Normed", external)
        self.assertEqual(graph["AuditTarget"], ["HighamBench.P11Definitions"])

    def test_theorem_extraction_removes_doc_comment_and_proof(self) -> None:
        target = HIGHAMBENCH_ROOT / "tasks" / "P11" / "T1" / "Target.lean"
        extracted = theorem_source(
            target.read_text(encoding="utf-8"),
            "p11_t1_first_column_residual_action",
        )
        self.assertTrue(extracted.startswith("theorem p11_t1"))
        self.assertNotIn("P11-T1:", extracted)
        self.assertNotIn("PROOF_START", extracted)
        self.assertNotIn("sorry", extracted)

    def test_all_60_targets_have_one_extractable_metadata_declaration(self) -> None:
        target_paths = sorted((HIGHAMBENCH_ROOT / "tasks").glob("P??/T?/Target.lean"))
        self.assertEqual(len(target_paths), 60)
        for target_path in target_paths:
            task = json.loads((target_path.parent / "task.json").read_text(encoding="utf-8"))
            theorem_name = task["formal_statement"]["theorem_name"]
            extracted = theorem_source(target_path.read_text(encoding="utf-8"), theorem_name)
            self.assertRegex(extracted, rf"^theorem\s+{re.escape(theorem_name)}\b")

    def test_semantic_check_ids_are_stable(self) -> None:
        self.assertEqual([item[0] for item in SEMANTIC_CHECKS], [f"S{i:02d}" for i in range(1, 17)])

    def test_implication_classification_is_fixed(self) -> None:
        self.assertEqual(implication_classification("yes", "yes"), "faithful-equivalent")
        self.assertEqual(implication_classification("yes", "no"), "faithful-stronger")
        self.assertEqual(implication_classification("no", "yes"), "not-faithful-weaker")
        self.assertEqual(implication_classification("no", "no"), "not-faithful-different")
        self.assertEqual(implication_classification("unclear", "yes"), "undetermined")

    def test_disagreement_requires_adjudication(self) -> None:
        source = {"ambiguities": []}
        blind = {"ambiguities": [], "dependency_coverage": []}
        direct = {
            "classification": "faithful-equivalent",
            "requires_adjudication": False,
            "dependency_coverage": [],
            "semantic_checklist": [],
        }
        roundtrip = {
            "classification": "not-faithful-weaker",
            "requires_adjudication": False,
            "semantic_checklist": [],
        }
        self.assertIn(
            "judge classifications differ",
            output_requires_adjudication(source, blind, direct, roundtrip),
        )

    def test_source_ambiguity_alone_does_not_require_adjudication(self) -> None:
        source = {"ambiguities": [{"issue": "notation"}]}
        blind = {"ambiguities": ["binder name"], "dependency_coverage": []}
        direct = {
            "classification": "faithful-equivalent",
            "requires_adjudication": False,
            "dependency_coverage": [],
            "semantic_checklist": [],
        }
        roundtrip = {
            "classification": "faithful-equivalent",
            "requires_adjudication": False,
            "semantic_checklist": [],
        }
        self.assertEqual(
            output_requires_adjudication(source, blind, direct, roundtrip), []
        )

    def test_force_refresh_archives_instead_of_deleting(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            inputs = output / "inputs"
            inputs.mkdir()
            (inputs / "old.txt").write_text("old", encoding="utf-8")
            archive = archive_existing_output(output)
            self.assertIsNotNone(archive)
            assert archive is not None
            self.assertEqual((archive / "inputs" / "old.txt").read_text(encoding="utf-8"), "old")
            self.assertFalse(inputs.exists())

    def test_lean_report_inventory_assigns_stable_dependency_ids(self) -> None:
        report = parse_lean_report(
            "\n".join(
                [
                    "target-readable\tReadable target",
                    "target-explicit\tExplicit target",
                    "dependency\tlocal\tLocal.foo\tLocal\t0\tdefinition\tNat\tNat\t0",
                    "dependency\texternal-frontier\tNat\tInit.Prelude\t1\tinductive\tType\tType\t",
                ]
            )
        )
        dependencies = report["dependencies"]
        self.assertEqual([item["id"] for item in dependencies], [f"D{i:03d}" for i in range(1, len(dependencies) + 1)])
        self.assertEqual(
            [item["role"] for item in dependencies],
            ["local", "external-frontier"],
        )
        self.assertTrue(
            all(re.fullmatch(r"[0-9a-f]{64}", item["semantic_sha256"]) for item in dependencies)
        )

    def test_dependency_fingerprint_ignores_task_local_metadata(self) -> None:
        dependency = {
            "id": "D001",
            "distance": 1,
            "role": "local",
            "name": "HighamBench.foo",
            "owner_module": "HighamBench.Core",
            "kind": "definition",
            "type_readable": "Nat",
            "type_explicit": "Nat",
            "body_readable": "1",
        }
        moved = {**dependency, "id": "D019", "distance": 7}
        changed = {**dependency, "body_readable": "2"}
        self.assertEqual(
            dependency_fingerprint(dependency), dependency_fingerprint(moved)
        )
        self.assertNotEqual(
            dependency_fingerprint(dependency), dependency_fingerprint(changed)
        )

    def test_paper_batch_inventory_is_t1_through_t3(self) -> None:
        self.assertEqual(paper_task_ids("p03"), ["P03-T1", "P03-T2", "P03-T3"])

    def test_paper_source_contract_splits_to_hash_bound_task_outputs(self) -> None:
        task_ids = ["P03-T1", "P03-T2", "P03-T3"]
        paper_hash = "a" * 64
        locator_hash = "b" * 64
        contracts = [
            {
                "task_id": task_id,
                "source_evidence": [],
                "statement": {},
                "undebatable_constraints": [],
                "ambiguities": [],
                "contract_plain_english": task_id,
            }
            for task_id in task_ids
        ]
        batch = {
            "schema_version": AUDIT_SCHEMA_VERSION,
            "role": "paper-source-contract",
            "paper_id": "P03",
            "paper_sha256": paper_hash,
            "source_locator_sha256": locator_hash,
            "task_ids": task_ids,
            "contracts": contracts,
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            audit_dirs = {task_id: root / task_id for task_id in task_ids}
            for audit_dir in audit_dirs.values():
                (audit_dir / "agent_outputs").mkdir(parents=True)
            input_path = root / "paper-source.json"
            input_path.write_text(json.dumps(batch), encoding="utf-8")

            manifest = {
                "paper": {"sha256": paper_hash},
                "paper_batch": {
                    "task_ids": task_ids,
                    "source_locator": {"sha256": locator_hash},
                },
            }
            with (
                patch.object(
                    split_paper_source_contract,
                    "validate_prepared",
                    return_value=(manifest, []),
                ),
                patch.object(
                    split_paper_source_contract,
                    "task_paths",
                    side_effect=lambda task_id: (
                        audit_dirs[task_id],
                        audit_dirs[task_id],
                    ),
                ),
                patch.object(split_paper_source_contract, "validate_role"),
            ):
                outputs = split_paper_source_contract.split_contract(input_path)

            self.assertEqual(len(outputs), 3)
            batch_hashes = set()
            for task_id, output in zip(task_ids, outputs, strict=True):
                value = json.loads(output.read_text(encoding="utf-8"))
                batch_hashes.add(value["paper_batch_sha256"])
                self.assertEqual(value["task_id"], task_id)
                self.assertEqual(value["contract_plain_english"], task_id)
            self.assertEqual(len(batch_hashes), 1)

    def test_dependency_dossier_sections_are_exact(self) -> None:
        prefix, sections = dossier_sections(
            "# Packet\n\n### D001: `A`\n\nfirst\n\n### D002: `B`\n\nsecond\n"
        )
        self.assertEqual(prefix, "# Packet\n\n")
        self.assertEqual(list(sections), ["D001", "D002"])
        self.assertIn("first", sections["D001"])
        self.assertNotIn("D002", sections["D001"])

    def test_all_json_schemas_parse(self) -> None:
        schemas = sorted((AUDIT_ROOT / "schemas").glob("*.json"))
        self.assertGreaterEqual(len(schemas), 6)
        for schema in schemas:
            parsed = json.loads(schema.read_text(encoding="utf-8"))
            self.assertEqual(parsed["$schema"], "https://json-schema.org/draft/2020-12/schema")
            self.assertEqual(
                parsed["properties"]["schema_version"]["const"],
                AUDIT_SCHEMA_VERSION,
            )

    def test_repository_skill_has_no_scaffold_markers(self) -> None:
        skill = AUDIT_ROOT / "skill" / "highambench-faithfulness-audit" / "SKILL.md"
        text = skill.read_text(encoding="utf-8")
        self.assertNotIn("TODO", text)
        self.assertIn("fork_context: false", text)
        self.assertIn("prepare_paper_audit.py", text)
        self.assertIn("direct_review_packet.md", text)
        self.assertIn("--role direct", text)

    def test_finalizer_writes_decision_report_and_hashes(self) -> None:
        source = {"ambiguities": []}
        blind = {"ambiguities": [], "dependency_coverage": []}
        direct = {
            "classification": "faithful-equivalent",
            "accepted": True,
            "requires_adjudication": False,
            "implications": {
                "lean_implies_paper": {"verdict": "yes", "reasoning": "same"},
                "paper_implies_lean": {"verdict": "yes", "reasoning": "same"},
            },
            "findings": [],
            "dependency_coverage": [],
            "semantic_checklist": [],
            "rationale": "The propositions agree.",
        }
        roundtrip = {
            "classification": "faithful-equivalent",
            "accepted": True,
            "requires_adjudication": False,
            "findings": [],
            "semantic_checklist": [],
        }
        with tempfile.TemporaryDirectory(dir=AUDIT_ROOT) as temporary:
            audit_dir = Path(temporary)
            output_dir = audit_dir / "agent_outputs"
            output_dir.mkdir()
            outputs = {
                "source_contract.json": source,
                "blind_translation.json": blind,
                "direct_judge.json": direct,
                "roundtrip_judge.json": roundtrip,
            }
            for filename, value in outputs.items():
                (output_dir / filename).write_text(json.dumps(value), encoding="utf-8")
            (audit_dir / "manifest.json").write_text(
                json.dumps(
                    {
                        "schema_version": AUDIT_SCHEMA_VERSION,
                        "target": {"sha256": "a" * 64},
                        "paper": {"sha256": "b" * 64},
                    }
                ),
                encoding="utf-8",
            )
            with (
                patch.object(
                    finalize_audit,
                    "adjudication_state",
                    return_value=([], audit_dir, (source, blind, direct, roundtrip)),
                ),
                patch.object(finalize_audit, "validate", return_value={}),
            ):
                report = finalize_audit.finalize("P11-T1")
            self.assertEqual(report, audit_dir / "report.md")
            decision = json.loads((audit_dir / "decision.json").read_text(encoding="utf-8"))
            manifest = json.loads((audit_dir / "manifest.json").read_text(encoding="utf-8"))
            self.assertEqual(decision["classification"], "faithful-equivalent")
            self.assertFalse(decision["adjudicated"])
            self.assertEqual(manifest["status"], "completed")
            self.assertIn("report", manifest["outputs"])


if __name__ == "__main__":
    unittest.main()
