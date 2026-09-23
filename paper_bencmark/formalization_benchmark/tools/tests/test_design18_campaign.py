from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
import design18_campaign  # noqa: E402


class Pilot18CampaignTests(unittest.TestCase):
    def test_treatment_uptake_follows_candidate_helper_edges(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            attempt = root / "R1" / "submissions" / "01"
            (attempt / "audit-preparation").mkdir(parents=True)
            (attempt / "audit-preparation" / "private_semantic_manifest.json").write_text(
                json.dumps({"raw_semantic_report": {
                    "dependencies": [
                        {"name": "Candidate.helper", "owner_module": "Candidate"},
                        {"name": "NumStability.gamma", "owner_module": "NumStability.Analysis.Gamma"},
                    ],
                    "edges": [
                        {"parent": "HighamBenchCandidate.target", "child": "Candidate.helper"},
                        {"parent": "Candidate.helper", "child": "NumStability.gamma"},
                    ],
                }}), encoding="utf-8")
            (attempt / "treatment-interface.json").write_text(
                json.dumps({"observed_numstability_imports": ["NumStability.Analysis.Gamma"]}),
                encoding="utf-8")
            pair = {"conditions": {"R1": {"attempts": [{"status": "ACCEPTED_FAITHFUL"}]}}}
            uptake = design18_campaign._treatment_uptake(root, pair)
            self.assertEqual(uptake["status"], "DIRECT_TREATMENT_REACHED")
            self.assertEqual(uptake["direct_reached"], ["NumStability.gamma"])

    def _args(self, output: Path) -> types.SimpleNamespace:
        return types.SimpleNamespace(
            deployment=Path("/synthetic/deployment.json"),
            mathlib_atlas=Path("/synthetic/mathlib/declarations.jsonl"),
            numstability_atlas=Path("/synthetic/numstability"),
            model_qualification=Path("/synthetic/qualification.json"),
            warm_root=Path("/synthetic/warm"),
            output_root=output,
        )

    def _pair_runner(self, ratios: list[float], seen: list) -> object:
        def run(args):
            index = len(seen)
            seen.append((args.task_id, args.condition_order))
            args.output_root.mkdir(parents=True)
            pair = {
                "status": "AUDITED_FAITHFUL_PAIR",
                "conditions": {"R0": {}, "R1": {}},
                "comparison": {"r1_over_r0": {
                    "contestant_system_wall_seconds": ratios[index],
                }},
            }
            (args.output_root / "pair-report.json").write_text(json.dumps(pair))
            return pair
        return run

    def test_first_bad_pair_stops_without_running_next(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            corpus = {"status": "ADMITTED_FOR_MEASUREMENT",
                      "scheduled_order": [f"T{i}" for i in range(12)],
                      "early_review_order": ["T0", "T1", "T2"]}
            seen = []
            with mock.patch.object(design18_campaign, "check_corpus",
                                   return_value=(corpus, [], [])):
                journal = design18_campaign.run_campaign(
                    self._args(root / "campaign"),
                    pair_runner=self._pair_runner([1.7], seen),
                    uptake_reader=lambda *_: {"status": "DIRECT_TREATMENT_REACHED"},
                    require_envelope=False,
                )
            self.assertEqual(journal["status"], "PAUSED_EARLY_REVIEW")
            self.assertEqual(seen, [("T0", "R0,R1")])
            self.assertIn("R1_CONTESTANT_SYSTEM_SLOWDOWN_AT_LEAST_1_5",
                          journal["pairs"][0]["early_review_reasons"])

    def test_good_early_pairs_finish_all_twelve_and_alternate_order(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            corpus = {"status": "ADMITTED_FOR_MEASUREMENT",
                      "scheduled_order": [f"T{i}" for i in range(12)],
                      "early_review_order": ["T0", "T1", "T2"]}
            seen = []
            with mock.patch.object(design18_campaign, "check_corpus",
                                   return_value=(corpus, [], [])):
                journal = design18_campaign.run_campaign(
                    self._args(root / "campaign"),
                    pair_runner=self._pair_runner([0.9] * 12, seen),
                    uptake_reader=lambda *_: {"status": "DIRECT_TREATMENT_REACHED"},
                    require_envelope=False,
                )
            self.assertEqual(journal["status"], "COMPLETE")
            self.assertEqual(len(seen), 12)
            self.assertEqual([order for _, order in seen[:4]],
                             ["R0,R1", "R1,R0", "R0,R1", "R1,R0"])

    def test_unadmitted_release_stops_before_campaign_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            output = Path(raw) / "campaign"
            with self.assertRaisesRegex(BenchmarkError, "not admitted"):
                design18_campaign.run_campaign(self._args(output), require_envelope=False)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
