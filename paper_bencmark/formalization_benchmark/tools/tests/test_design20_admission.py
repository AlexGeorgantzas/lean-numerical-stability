from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from common import BenchmarkError, sha256_file
import design20_admission


class Pilot20AdmissionTests(unittest.TestCase):
    def test_hash_bound_source_review_preflight_and_component(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            packet = root / "packets" / "TEST.json"
            packet.parent.mkdir()
            packet.write_text(json.dumps({"task_id": "TEST"}), encoding="utf-8")
            paper = root / "paper.pdf"
            paper.write_bytes(b"source")
            corpus = root / "CORPUS_3.json"
            corpus.write_text("{}", encoding="utf-8")
            reviewer = root / "review" / "source-contract-review.json"
            copied = reviewer.parent / "workspace" / "source" / "packet.json"
            copied.parent.mkdir(parents=True)
            copied.write_bytes(packet.read_bytes())
            reviewer.write_text(json.dumps({
                "task_id": "TEST", "status": "SOURCE_CONTRACT_REVIEWED_NOT_ADMITTED",
                "assessment": "faithful", "source_pdf_sha256": sha256_file(paper),
                "reviewer_model": "gpt-6-astra", "reasoning_effort": "high",
            }), encoding="utf-8")
            preflight = root / "preflight.json"
            preflight.write_text(json.dumps({
                "status": "PASS", "corpus_sha256": sha256_file(corpus),
                "tasks": {"TEST": {"R0": {"status": "PASS"},
                                   "R1": {"status": "PASS",
                                          "selected_roots": ["NumStability.component"]}}},
            }), encoding="utf-8")
            skeleton = root / "private.lean"
            skeleton.write_text("theorem target : True := by sorry\n", encoding="utf-8")
            compilation = root / "skeleton-compilation.json"
            compilation.write_text(json.dumps({
                "status": "PASS",
                "tasks": {"TEST": {
                    "status": "COMPILED_SORRY_STATEMENT_ONLY",
                    "private_source_sha256": sha256_file(skeleton),
                    "compile": {"pass": True},
                }},
            }), encoding="utf-8")
            admission = root / "ADMISSION_3.json"
            task = {
                "status": "ADMITTED_DEVELOPMENT",
                "source_packet_sha256": sha256_file(packet),
                "source_pdf_sha256": sha256_file(paper),
                "target_collision_review": "NO_TARGET_RESULT_FOUND",
                "source_review_path": str(reviewer),
                "source_review_sha256": sha256_file(reviewer),
                "direct_component_names": ["NumStability.component"],
                "private_skeleton_path": str(skeleton),
                "private_skeleton_sha256": sha256_file(skeleton),
            }
            admission.write_text(json.dumps({
                "schema_version": "pilot-20-development-admission-1",
                "static_preflight_path": str(preflight),
                "static_preflight_sha256": sha256_file(preflight),
                "private_skeleton_compile_path": str(compilation),
                "private_skeleton_compile_sha256": sha256_file(compilation),
                "tasks": {"TEST": task},
            }), encoding="utf-8")
            with mock.patch.object(design20_admission, "ROOT", root), \
                 mock.patch.object(design20_admission, "ADMISSION", admission):
                self.assertEqual(design20_admission.verify_admission(
                    "TEST", packet_path=packet, paper=paper), task)
                task["source_packet_sha256"] = "0" * 64
                admission.write_text(json.dumps({
                    "schema_version": "pilot-20-development-admission-1",
                    "static_preflight_path": str(preflight),
                    "static_preflight_sha256": sha256_file(preflight),
                    "private_skeleton_compile_path": str(compilation),
                    "private_skeleton_compile_sha256": sha256_file(compilation),
                    "tasks": {"TEST": task},
                }), encoding="utf-8")
                with self.assertRaises(BenchmarkError):
                    design20_admission.verify_admission(
                        "TEST", packet_path=packet, paper=paper)


if __name__ == "__main__":
    unittest.main()
