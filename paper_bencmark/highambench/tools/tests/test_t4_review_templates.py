from __future__ import annotations

import json
from pathlib import Path
import re
import unittest


REVIEW_ROOT = (
    Path(__file__).resolve().parents[2] / "templates" / "T4" / "review"
)


class T4ReviewTemplateTests(unittest.TestCase):
    def _last_json_object(self, name: str) -> dict[str, object]:
        text = (REVIEW_ROOT / name).read_text(encoding="utf-8")
        matches = re.findall(r"\{[^{}]*\}", text, flags=re.DOTALL)
        self.assertTrue(matches, name)
        return json.loads(matches[-1])

    def test_role_outputs_match_established_runtime_schema(self) -> None:
        expected_verdict = {
            "score",
            "tag",
            "passed",
            "evidence",
            "discrepancies",
        }
        for name in (
            "direct-judge.v1.md",
            "round-trip-judge.v1.md",
            "adjudicator.v1.md",
        ):
            with self.subTest(name=name):
                self.assertEqual(set(self._last_json_object(name)), expected_verdict)
        self.assertEqual(
            set(self._last_json_object("blind-translator.v1.md")),
            {"reconstruction"},
        )

    def test_direct_blind_and_round_trip_invariants_are_literal(self) -> None:
        direct = (REVIEW_ROOT / "direct-judge.v1.md").read_text(encoding="utf-8")
        blind = (REVIEW_ROOT / "blind-translator.v1.md").read_text(encoding="utf-8")
        round_trip = (REVIEW_ROOT / "round-trip-judge.v1.md").read_text(
            encoding="utf-8"
        )
        self.assertIn(
            "paper source claim against the actual proof-erased Lean declarations",
            direct,
        )
        self.assertIn("Inspect only the one supplied sanitized Lean packet", blind)
        self.assertIn("Do not inspect any other file", blind)
        self.assertIn(
            "paper source claim against the locked Blind Translator natural-language reconstruction",
            round_trip,
        )
        self.assertIn(
            "Lean target → blind ordinary-language translation → comparison with the paper source claim",
            round_trip,
        )

    def test_durable_policy_excludes_hidden_transcript_dependency(self) -> None:
        policy = (REVIEW_ROOT / "durable-artifact-policy.v1.md").read_text(
            encoding="utf-8"
        )
        for required in (
            "role prompts",
            "packets",
            "manifests",
            "campaign plans",
            "checkpoints",
            "validated final JSON",
            "provenance",
            "semantic audit/repair ledgers",
        ):
            self.assertIn(required, policy)
        self.assertIn("Do not make raw hidden reasoning", policy)
        self.assertIn("without replaying a prior chat", policy)

    def test_authorization_template_is_pending_and_never_authorizes_measurement(self) -> None:
        template = json.loads(
            (
                REVIEW_ROOT
                / "standing-authorization-receipt.pending.template.json"
            ).read_text(encoding="utf-8")
        )
        self.assertEqual(template["authorization_status"], "pending")
        self.assertEqual(template["runtime"]["reasoning"], "ultra")
        self.assertEqual(template["runtime"]["speed_mode"], "standard")
        for field in (
            "measurements_authorized",
            "measurement_ready_authorized",
            "commit_authorized",
            "push_authorized",
        ):
            self.assertIs(template[field], False)
        isolation = template["role_isolation"]
        self.assertIs(isolation["fresh_role_contexts"], True)
        self.assertIs(isolation["role_blindness"], True)
        self.assertIs(isolation["host_repository_access"], False)
        self.assertIs(isolation["private_proof_access"], False)
        self.assertIs(isolation["web_access"], False)

    def test_authorization_schema_is_closed_and_fail_closed(self) -> None:
        schema = json.loads(
            (
                REVIEW_ROOT
                / "standing-authorization-receipt-0.1.schema.json"
            ).read_text(encoding="utf-8")
        )
        self.assertIs(schema["additionalProperties"], False)
        self.assertEqual(
            schema["properties"]["runtime"]["properties"]["reasoning"]["const"],
            "ultra",
        )
        self.assertEqual(
            schema["properties"]["runtime"]["properties"]["speed_mode"]["const"],
            "standard",
        )
        for field in (
            "measurements_authorized",
            "measurement_ready_authorized",
            "commit_authorized",
            "push_authorized",
        ):
            self.assertIs(schema["properties"][field]["const"], False)


if __name__ == "__main__":
    unittest.main()
