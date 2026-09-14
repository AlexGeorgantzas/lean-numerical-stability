from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import (  # noqa: E402
    BenchmarkError,
    assert_no_credentials_in_bytes,
    assert_no_credentials_in_tree,
    bounded_tree_usage,
    freeze_candidate,
    make_repair_feedback,
    treatment_free_runtime_manifest,
)


class RepairFeedbackTests(unittest.TestCase):
    def test_removes_formal_code_and_provenance(self) -> None:
        feedback = make_repair_feedback(
            [
                {
                    "paper_requirement": "Use NumStability.Secret theorem foo := by exact rfl",
                    "candidate_mismatch": "Import Gold.lean and apply D17 with `simp`.",
                }
            ]
        )
        rendered = str(feedback)
        for forbidden in (
            "NumStability",
            "Gold.lean",
            "theorem",
            ":=",
            " exact ",
            "D17",
            "simp",
            "`",
        ):
            self.assertNotIn(forbidden, rendered)


class CredentialScanTests(unittest.TestCase):
    def test_accepts_clean_closure_and_rejects_token_value(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            auth = root / "auth-source.json"
            auth.write_text(
                '{"tokens":{"access_token":"test-secret-token-123456789"}}\n',
                encoding="utf-8",
            )
            clean = root / "clean"
            clean.mkdir()
            (clean / "artifact.json").write_text('{"status":"ok"}\n', encoding="utf-8")
            self.assertTrue(assert_no_credentials_in_tree(clean, auth)["passed"])
            (clean / "leak.log").write_text(
                "prefix test-secret-token-123456789 suffix\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(BenchmarkError, "credential material detected"):
                assert_no_credentials_in_tree(clean, auth)
            self.assertTrue(
                assert_no_credentials_in_bytes([("future.json", b'{"status":"ok"}\n')], auth)[
                    "passed"
                ]
            )
            with self.assertRaisesRegex(BenchmarkError, "prospective result artifact"):
                assert_no_credentials_in_bytes(
                    [("future.json", b"test-secret-token-123456789")], auth
                )

    def test_tree_scan_enforces_entry_and_byte_ceilings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            auth = root / "auth.json"
            auth.write_text(
                '{"tokens":{"access_token":"test-secret-token-123456789"}}\n',
                encoding="utf-8",
            )
            closure = root / "closure"
            closure.mkdir()
            (closure / "one").write_bytes(b"1234")
            (closure / "two").write_bytes(b"5678")
            with self.assertRaisesRegex(BenchmarkError, "entry ceiling"):
                assert_no_credentials_in_tree(
                    closure, auth, maximum_entries=1, maximum_bytes=100
                )
            with self.assertRaisesRegex(BenchmarkError, "byte ceiling"):
                assert_no_credentials_in_tree(
                    closure, auth, maximum_entries=10, maximum_bytes=7
                )

    def test_candidate_credential_is_rejected_before_publication(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            auth = root / "auth.json"
            secret = "test-secret-token-123456789"
            auth.write_text(
                '{"tokens":{"access_token":"' + secret + '"}}\n',
                encoding="utf-8",
            )
            source = root / "Candidate.lean"
            source.write_text("-- " + secret + "\n", encoding="utf-8")
            destination = root / "frozen" / "Candidate.lean"
            with self.assertRaisesRegex(BenchmarkError, "prospective result artifact"):
                freeze_candidate(source, destination, auth_file=auth)
            self.assertFalse(destination.exists())


class TreatmentAbsenceTests(unittest.TestCase):
    def test_manifest_is_location_independent_and_detects_marker_content(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            first = root / "first"
            second = root / "second"
            first.mkdir()
            second.mkdir()
            payload = b"safe runtime bytes\n"
            (first / "runtime.bin").write_bytes(payload)
            (second / "runtime.bin").write_bytes(payload)
            first_record = treatment_free_runtime_manifest({"packages": first})
            second_record = treatment_free_runtime_manifest({"packages": second})
            self.assertTrue(first_record["treatment_absent"])
            self.assertEqual(first_record["scan_sha256"], second_record["scan_sha256"])

            (second / "runtime.bin").write_bytes(
                b"x" * (1024 * 1024 - 3) + b"num" + b"stability"
            )
            with self.assertRaisesRegex(BenchmarkError, "treatment-related bytes"):
                treatment_free_runtime_manifest({"packages": second})

    def test_manifest_detects_marker_in_path(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "NumStability-cache").mkdir()
            with self.assertRaisesRegex(BenchmarkError, "treatment-related path"):
                treatment_free_runtime_manifest({"toolchain": root})


class WorkspaceLimitTests(unittest.TestCase):
    def test_bounded_tree_usage_stops_at_entry_and_byte_ceilings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "one").write_bytes(b"1234")
            nested = root / "nested"
            nested.mkdir()
            (nested / "two").write_bytes(b"567")
            self.assertEqual(
                bounded_tree_usage(root, maximum_entries=3, maximum_bytes=7),
                {"entries": 3, "bytes": 7},
            )
            with self.assertRaisesRegex(BenchmarkError, "entry ceiling"):
                bounded_tree_usage(root, maximum_entries=2, maximum_bytes=100)
            with self.assertRaisesRegex(BenchmarkError, "byte ceiling"):
                bounded_tree_usage(root, maximum_entries=10, maximum_bytes=6)


if __name__ == "__main__":
    unittest.main()
