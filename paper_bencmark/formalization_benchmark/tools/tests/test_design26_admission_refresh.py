from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace
from unittest import mock

from common import BenchmarkError, sha256_file
from design26_admission_refresh import refresh


class Pilot26AdmissionRefreshTests(unittest.TestCase):
    def test_rebinds_unchanged_source_records_to_new_preflight(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus = root / "corpus.json"
            corpus.write_text(json.dumps({"scheduled_order": ["A"]}))
            preflight = root / "preflight.json"
            preflight.write_text(json.dumps({
                "status": "PASS", "corpus_sha256": sha256_file(corpus),
                "tasks": {"A": {}},
            }))
            previous = root / "previous.json"
            previous.write_text(json.dumps({
                "schema_version": "pilot-20-development-admission-1",
                "tasks": {"A": {"source_review_path": "/frozen/review.json"}},
                "private_skeleton_compile_path": "/frozen/compile.json",
            }))
            packet = root / "packets" / "A.json"
            packet.parent.mkdir()
            packet.write_text(json.dumps({
                "paper_pdf": {"path_basename": "paper.pdf"},
            }))
            paper = root / "sources" / "paper.pdf"
            paper.parent.mkdir()
            paper.write_bytes(b"source")
            output = root / "new" / "admission.json"
            with (mock.patch("design26_admission_refresh.ROOT", root),
                  mock.patch("design26_admission_refresh.load_deployment",
                             return_value=SimpleNamespace(pdf_root=paper.parent)),
                  mock.patch("design26_admission_refresh.verify_admission") as verify):
                record = refresh(
                    previous=previous, preflight=preflight, corpus=corpus,
                    deployment_path=root / "deployment.json", output=output,
                )
            self.assertEqual(record["static_preflight_sha256"], sha256_file(preflight))
            self.assertEqual(record["previous_admission_sha256"], sha256_file(previous))
            self.assertEqual(json.loads(output.read_text()), record)
            self.assertEqual(verify.call_count, 1)
            self.assertEqual(verify.call_args.kwargs["paper"], paper)

    def test_rejects_preflight_for_a_different_corpus(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus = root / "corpus.json"
            corpus.write_text(json.dumps({"scheduled_order": ["A"]}))
            preflight = root / "preflight.json"
            preflight.write_text(json.dumps({
                "status": "PASS", "corpus_sha256": "wrong", "tasks": {"A": {}},
            }))
            previous = root / "previous.json"
            previous.write_text(json.dumps({
                "schema_version": "pilot-20-development-admission-1",
                "tasks": {"A": {}},
            }))
            output = root / "admission.json"
            with self.assertRaises(BenchmarkError):
                refresh(previous=previous, preflight=preflight, corpus=corpus,
                        deployment_path=root / "deployment.json", output=output)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
