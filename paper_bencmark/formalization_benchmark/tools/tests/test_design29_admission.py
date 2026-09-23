from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from common import BenchmarkError, sha256_file
import design29_admission


def save(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value), encoding="utf-8")


class Pilot29AdmissionTests(unittest.TestCase):
    def test_new_private_candidate_requires_audited_direct_reach(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            packet = root / "packet.json"
            paper = root / "paper.pdf"
            save(packet, {"task_id": "TEST"})
            paper.write_bytes(b"paper")
            corpus = root / "corpus.json"
            save(corpus, {"scheduled_order": ["TEST"]})
            review = root / "review" / "source-contract-review.json"
            copied = review.parent / "workspace" / "source" / "packet.json"
            save(copied, {"task_id": "TEST"})
            save(review, {
                "task_id": "TEST",
                "status": "SOURCE_CONTRACT_REVIEWED_NOT_ADMITTED",
                "assessment": "faithful",
                "reviewer_model": "gpt-6-astra",
                "reasoning_effort": "high",
                "source_pdf_sha256": sha256_file(paper),
            })
            candidate = root / "Candidate.lean"
            candidate.write_text("theorem target : True := by sorry\n", encoding="utf-8")
            manifest = root / "audit" / "preparation" / "private_semantic_manifest.json"
            save(manifest, {
                "candidate": {"sha256": sha256_file(candidate)},
                "raw_semantic_report": {
                    "dependencies": [{"name": "NumStability.useful"}],
                },
            })
            result = root / "audit" / "result.json"
            save(result, {
                "task_id": "TEST",
                "candidate_sha256": sha256_file(candidate),
                "source_contract": "statement-only-single-target-sorry",
                "condition_blind": True,
                "attempt_blind": True,
                "decision": {"accepted": True},
                "private_manifest_sha256": sha256_file(manifest),
            })
            prior = root / "prior.json"
            save(prior, {"tasks": {}})
            campaign_root = root / "campaign"
            campaign = campaign_root / "campaign.json"
            save(campaign, {"status": "COMPLETE", "pairs": []})
            admission = root / "admission.json"
            task = {
                "status": "ADMITTED_DEVELOPMENT",
                "model_stratum": "algorithm_error",
                "source_packet_sha256": sha256_file(packet),
                "source_pdf_sha256": sha256_file(paper),
                "target_collision_review": "NO_TARGET_RESULT_FOUND",
                "collision_review_note": "The full target is absent in a reviewed declaration scan.",
                "source_review_path": str(review),
                "source_review_sha256": sha256_file(review),
                "evidence_kind": "new_private_audit",
                "private_candidate_path": str(candidate),
                "private_candidate_sha256": sha256_file(candidate),
                "private_audit_result_path": str(result),
                "private_audit_result_sha256": sha256_file(result),
                "required_direct_names": ["NumStability.useful"],
            }
            save(admission, {
                "schema_version": design29_admission.SCHEMA,
                "status": "ADMITTED_DEVELOPMENT",
                "prior_admission_path": "prior.json",
                "prior_admission_sha256": sha256_file(prior),
                "prior_campaign_path": str(campaign_root),
                "prior_campaign_sha256": sha256_file(campaign),
                "tasks": {"TEST": task},
            })
            with mock.patch.object(design29_admission, "ROOT", root):
                self.assertEqual(design29_admission.verify_admission(
                    "TEST", packet_path=packet, paper=paper,
                    admission_path=admission, corpus_path=corpus,
                ), task)
                candidate.write_text("theorem target : False := by sorry\n",
                                     encoding="utf-8")
                with self.assertRaises(BenchmarkError):
                    design29_admission.verify_admission(
                        "TEST", packet_path=packet, paper=paper,
                        admission_path=admission, corpus_path=corpus,
                    )


if __name__ == "__main__":
    unittest.main()
