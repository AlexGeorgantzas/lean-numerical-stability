from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
from design16_faithfulness_screen import (  # noqa: E402
    Design16FaithfulnessScreen,
    validate_screen_output,
)


PAPER_HASH = "a" * 64
SEMANTIC_HASH = "b" * 64
DEPENDENCIES = [("D001", "LocalDef001"), ("D002", "Nat")]


def valid_output(*, classification: str = "faithful-equivalent") -> dict:
    implication_pairs = {
        "faithful-equivalent": ("yes", "yes"),
        "faithful-stronger": ("yes", "no"),
        "unfaithful-weaker": ("no", "yes"),
        "unfaithful-different": ("no", "no"),
    }
    candidate_to_source, source_to_candidate = implication_pairs[classification]
    faithful = classification.startswith("faithful-")
    return {
        "schema_version": "formalization-design16-faithfulness-screen-1",
        "role": "condition-blind-faithfulness-screen",
        "paper_sha256": PAPER_HASH,
        "candidate_semantic_sha256": SEMANTIC_HASH,
        "dependency_coverage": [
            {
                "id": dependency_id,
                "name": dependency_name,
                "interpretation": "The declaration has the displayed exact semantics.",
                "effect_on_target": "It determines one part of the target proposition.",
                "paper_match": "Its use agrees with the selected paper result.",
                "status": "pass",
            }
            for dependency_id, dependency_name in DEPENDENCIES
        ],
        "semantic_checklist": [
            {
                "id": f"S{index:02d}",
                "status": "pass",
                "paper_evidence": "The selected result states this requirement.",
                "candidate_evidence": "The proposition encodes this requirement.",
                "reasoning": "The evidence agrees for this semantic dimension.",
            }
            for index in range(1, 17)
        ],
        "domain_assessment": {
            "covers_every_source_case": faithful,
            "source_cases_omitted": [] if faithful else ["One admissible source case."],
            "unjustified_extra_candidate_assumptions": [],
            "vacuity_risks": [],
            "genuine_added_strength": (
                ["The conclusion supplies an additional valid bound."]
                if classification == "faithful-stronger"
                else []
            ),
            "reasoning": "The candidate domain was compared against every source case.",
        },
        "implications": {
            "candidate_implies_source": {
                "verdict": candidate_to_source,
                "reasoning": "This direction follows from the compared requirements.",
            },
            "source_implies_candidate": {
                "verdict": source_to_candidate,
                "reasoning": "This direction follows from the compared requirements.",
            },
        },
        "classification": classification,
        "verdict": "faithful" if faithful else "unfaithful",
        "mismatches": [] if faithful else [
            {
                "paper_requirement": "Every admissible source case is covered.",
                "candidate_mismatch": "The candidate omits one admissible case.",
                "severity": "major",
            }
        ],
        "rationale": "The binary result follows from the complete evidence ledger.",
    }


class FakeScreen(Design16FaithfulnessScreen):
    def __init__(self, output: dict):
        self.output = output
        self.prompt: str | None = None
        self.workspace: Path | None = None

    def _fresh_role(self, *, prompt, workspace, validate, role, **kwargs):
        del kwargs
        self.prompt = prompt
        self.workspace = workspace
        self.asserted_role = role
        validate(self.output)
        return self.output, {
            "schema_version": "formalization-auditor-role-telemetry-1",
            "role": role,
            "selected_retry": 1,
            "retry": 1,
            "tries": [],
            "wall_seconds": 0.1,
            "usage": {
                "input_tokens": 1,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 1,
                "reasoning_output_tokens": 0,
                "total_tokens": 2,
            },
            "thread_id": "fresh-screen",
        }


class ScreenPolicyTests(unittest.TestCase):
    def validate(self, value: dict) -> None:
        validate_screen_output(
            value,
            paper_sha256=PAPER_HASH,
            semantic_sha256=SEMANTIC_HASH,
            dependencies=DEPENDENCIES,
        )

    def test_complete_equivalent_candidate_passes(self) -> None:
        self.validate(valid_output())

    def test_complete_genuine_strengthening_passes(self) -> None:
        self.validate(valid_output(classification="faithful-stronger"))

    def test_every_dependency_is_required_in_order_with_exact_blind_name(self) -> None:
        missing = valid_output()
        missing["dependency_coverage"].pop()
        with self.assertRaisesRegex(BenchmarkError, "omitted.*dependency"):
            self.validate(missing)
        renamed = valid_output()
        renamed["dependency_coverage"][0]["name"] = "NumStability.secret"
        with self.assertRaisesRegex(BenchmarkError, "does not match D001"):
            self.validate(renamed)

    def test_all_sixteen_checks_are_required_in_order(self) -> None:
        missing = valid_output()
        missing["semantic_checklist"].pop()
        with self.assertRaisesRegex(BenchmarkError, "mandatory semantic checks"):
            self.validate(missing)
        reordered = valid_output()
        reordered["semantic_checklist"][0]["id"] = "S02"
        with self.assertRaisesRegex(BenchmarkError, "S01"):
            self.validate(reordered)

    def test_partial_domain_cannot_be_accepted_as_stronger(self) -> None:
        partial = valid_output(classification="faithful-stronger")
        partial["domain_assessment"]["covers_every_source_case"] = False
        partial["domain_assessment"]["source_cases_omitted"] = [
            "The zero-dimensional source case."
        ]
        with self.assertRaisesRegex(BenchmarkError, "accepted despite a domain"):
            self.validate(partial)

    def test_added_assumption_or_vacuity_cannot_pass(self) -> None:
        restricted = valid_output()
        restricted["domain_assessment"]["unjustified_extra_candidate_assumptions"] = [
            "Every intermediate operation succeeds."
        ]
        with self.assertRaisesRegex(BenchmarkError, "accepted despite a domain"):
            self.validate(restricted)
        vacuous = valid_output()
        vacuous["domain_assessment"]["vacuity_risks"] = ["The hypotheses are inconsistent."]
        with self.assertRaisesRegex(BenchmarkError, "accepted despite a domain"):
            self.validate(vacuous)

    def test_strengthening_requires_an_explicit_genuine_strength(self) -> None:
        unsupported = valid_output(classification="faithful-stronger")
        unsupported["domain_assessment"]["genuine_added_strength"] = []
        with self.assertRaisesRegex(BenchmarkError, "without genuine added strength"):
            self.validate(unsupported)

    def test_unfaithful_is_binary_and_requires_a_concrete_mismatch(self) -> None:
        unfaithful = valid_output(classification="unfaithful-weaker")
        self.validate(unfaithful)
        unfaithful["mismatches"] = []
        with self.assertRaisesRegex(BenchmarkError, "no concrete mismatch"):
            self.validate(unfaithful)

    def test_fail_status_cannot_hide_inside_a_faithful_verdict(self) -> None:
        failed = valid_output()
        failed["semantic_checklist"][8]["status"] = "fail"
        with self.assertRaisesRegex(BenchmarkError, "accepted despite"):
            self.validate(failed)

    def test_runner_exposes_only_condition_blind_inputs_and_marks_non_scientific(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "paper.pdf"
            source = root / "source.md"
            dossier = root / "dossier.json"
            paper.write_bytes(b"%PDF synthetic")
            source.write_text("Selected theorem and source locator.", encoding="utf-8")
            dossier.write_text(
                json.dumps(
                    {
                        "schema_version": "candidate-semantic-dossier-1",
                        "semantic_sha256": SEMANTIC_HASH,
                        "dependencies": [
                            {"id": dependency_id, "name": dependency_name}
                            for dependency_id, dependency_name in DEPENDENCIES
                        ],
                    }
                ),
                encoding="utf-8",
            )
            output = valid_output()
            output["paper_sha256"] = sha256_file(paper)
            screen = FakeScreen(output)
            decision = screen.run_screen(
                task_id="H5-5",
                paper_path=paper,
                paper_sha256=sha256_file(paper),
                source_packet=source,
                dossier_path=dossier,
                semantic_sha256=SEMANTIC_HASH,
                screen_root=root / "screen",
            )
            self.assertTrue(decision["accepted"])
            self.assertTrue(decision["condition_blind"])
            self.assertTrue(decision["full_scientific_audit_required"])
            self.assertEqual(
                decision["scientific_status"],
                "DEVELOPMENT_SCREEN_ONLY_NOT_SCIENTIFIC_AUDIT",
            )
            self.assertEqual(
                sorted(path.name for path in screen.workspace.iterdir()),
                ["blind_semantic_dossier.json", "paper.pdf", "source_packet.md"],
            )
            self.assertNotIn("H5-5", screen.prompt)
            self.assertNotIn("condition L", screen.prompt.lower())
            self.assertEqual(
                screen.asserted_role, "condition-blind-faithfulness-screen"
            )

    def test_runner_rejects_unblinded_or_hash_changed_dossier(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "paper.pdf"
            source = root / "source.md"
            dossier = root / "dossier.json"
            paper.write_bytes(b"%PDF synthetic")
            source.write_text("source", encoding="utf-8")
            dossier.write_text(
                json.dumps(
                    {
                        "schema_version": "private-semantic-manifest",
                        "semantic_sha256": SEMANTIC_HASH,
                        "dependencies": [],
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(BenchmarkError, "blinded semantic dossier"):
                FakeScreen(valid_output()).run_screen(
                    task_id="H5-5",
                    paper_path=paper,
                    paper_sha256=sha256_file(paper),
                    source_packet=source,
                    dossier_path=dossier,
                    semantic_sha256=SEMANTIC_HASH,
                    screen_root=root / "screen",
                )


if __name__ == "__main__":
    unittest.main()
