from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
import uuid


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in os.sys.path:
    os.sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError  # noqa: E402
from t4_writer_lease import (  # noqa: E402
    main,
    manage_lease,
    read_lease_credentials,
)


class T4WriterLeaseTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.scratch = self.root / "scratch"
        self.scratch.mkdir()

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def _credentials() -> tuple[str, str]:
        return str(uuid.uuid4()), "test-token-" + uuid.uuid4().hex

    def test_claim_check_renew_and_release(self) -> None:
        invocation_id, token = self._credentials()
        claimed = manage_lease(
            self.scratch,
            "P06",
            "claim",
            invocation_id=invocation_id,
            token=token,
            ttl_seconds=120,
            now=1000,
        )
        self.assertTrue(claimed["acquired"])
        lease_path = Path(claimed["lease_path"])
        stored = json.loads(lease_path.read_text(encoding="utf-8"))
        self.assertNotIn(token, lease_path.read_text(encoding="utf-8"))
        self.assertEqual(stored["invocation_id"], invocation_id)
        self.assertEqual(lease_path.stat().st_mode & 0o777, 0o600)

        checked = manage_lease(
            self.scratch,
            "P06",
            "check",
            invocation_id=invocation_id,
            token=token,
            now=1010,
        )
        self.assertTrue(checked["held"])
        self.assertTrue(checked["holder_matches"])
        self.assertTrue(checked["lease"]["active"])

        renewed = manage_lease(
            self.scratch,
            "P06",
            "renew",
            invocation_id=invocation_id,
            token=token,
            ttl_seconds=300,
            now=1020,
        )
        self.assertEqual(renewed["lease"]["generation"], 2)
        self.assertEqual(renewed["lease"]["expires_at_unix"], 1320)

        released = manage_lease(
            self.scratch,
            "P06",
            "release",
            invocation_id=invocation_id,
            token=token,
            now=1030,
        )
        self.assertTrue(released["released"])
        self.assertFalse(lease_path.exists())
        self.assertTrue(Path(released["archived_lease"]).is_file())
        self.assertFalse(
            manage_lease(self.scratch, "P06", "check", now=1031)["held"]
        )

    def test_check_unclaimed_paper_is_read_only_and_reports_absent(self) -> None:
        faithfulness = self.scratch / "t4_source_faithfulness"
        result = manage_lease(self.scratch, "P06", "check", now=1000)
        self.assertFalse(result["held"])
        self.assertFalse(result["active"])
        self.assertFalse(faithfulness.exists())
        self.assertEqual(
            Path(result["lease_path"]),
            faithfulness / "P06" / "writer_lease.json",
        )

        invocation_id, token = self._credentials()
        result = manage_lease(
            self.scratch,
            "P06",
            "check",
            invocation_id=invocation_id,
            token=token,
            now=1000,
        )
        self.assertFalse(result["held"])
        self.assertFalse(faithfulness.exists())

        with self.assertRaisesRegex(BenchmarkToolError, "invalid invocation UUID"):
            manage_lease(
                self.scratch,
                "P06",
                "check",
                invocation_id="not-a-uuid",
                token=token,
                now=1000,
            )

    def test_concurrent_same_paper_claim_allows_exactly_one(self) -> None:
        credentials = [self._credentials(), self._credentials()]

        def claim(pair: tuple[str, str]) -> str:
            try:
                manage_lease(
                    self.scratch,
                    "P06",
                    "claim",
                    invocation_id=pair[0],
                    token=pair[1],
                    ttl_seconds=120,
                    now=1000,
                )
            except BenchmarkToolError:
                return "blocked"
            return "acquired"

        with ThreadPoolExecutor(max_workers=2) as executor:
            outcomes = list(executor.map(claim, credentials))
        self.assertEqual(sorted(outcomes), ["acquired", "blocked"])

    def test_concurrent_distinct_papers_are_independent(self) -> None:
        pairs = [(paper_id, *self._credentials()) for paper_id in ("P06", "P07")]

        def claim(item: tuple[str, str, str]) -> dict[str, object]:
            paper_id, invocation_id, token = item
            return manage_lease(
                self.scratch,
                paper_id,
                "claim",
                invocation_id=invocation_id,
                token=token,
                ttl_seconds=120,
                now=1000,
            )

        with ThreadPoolExecutor(max_workers=2) as executor:
            results = list(executor.map(claim, pairs))
        self.assertTrue(all(result["acquired"] for result in results))
        self.assertNotEqual(results[0]["lease_path"], results[1]["lease_path"])

    def test_expired_takeover_is_explicit_and_archives_prior_claim(self) -> None:
        old_id, old_token = self._credentials()
        new_id, new_token = self._credentials()
        first = manage_lease(
            self.scratch,
            "P06",
            "claim",
            invocation_id=old_id,
            token=old_token,
            ttl_seconds=10,
            now=1000,
        )
        old_bytes = Path(first["lease_path"]).read_bytes()
        with self.assertRaisesRegex(BenchmarkToolError, "takeover-expired"):
            manage_lease(
                self.scratch,
                "P06",
                "claim",
                invocation_id=new_id,
                token=new_token,
                ttl_seconds=20,
                now=1011,
            )
        takeover = manage_lease(
            self.scratch,
            "P06",
            "claim",
            invocation_id=new_id,
            token=new_token,
            ttl_seconds=20,
            takeover_expired=True,
            now=1011,
        )
        archive = Path(takeover["archived_expired_lease"])
        self.assertEqual(archive.read_bytes(), old_bytes)
        self.assertEqual(takeover["lease"]["generation"], 2)
        self.assertEqual(takeover["lease"]["invocation_id"], new_id)

    def test_wrong_holder_cannot_renew_or_release(self) -> None:
        invocation_id, token = self._credentials()
        manage_lease(
            self.scratch,
            "P06",
            "claim",
            invocation_id=invocation_id,
            token=token,
            now=1000,
        )
        other_id, other_token = self._credentials()
        for action in ("renew", "release"):
            with self.subTest(action=action), self.assertRaisesRegex(
                BenchmarkToolError, "credentials"
            ):
                manage_lease(
                    self.scratch,
                    "P06",
                    action,
                    invocation_id=other_id,
                    token=other_token,
                    now=1001,
                )

    def test_rejects_symlinked_root_components_and_lease_file(self) -> None:
        outside = self.root / "outside"
        outside.mkdir()
        symlinked_scratch = self.root / "scratch-link"
        symlinked_scratch.symlink_to(self.scratch, target_is_directory=True)
        invocation_id, token = self._credentials()
        with self.assertRaisesRegex(BenchmarkToolError, "non-symlink"):
            manage_lease(
                symlinked_scratch,
                "P06",
                "claim",
                invocation_id=invocation_id,
                token=token,
            )

        faithfulness = self.scratch / "t4_source_faithfulness"
        faithfulness.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(BenchmarkToolError, "non-symlink"):
            manage_lease(
                self.scratch,
                "P06",
                "claim",
                invocation_id=invocation_id,
                token=token,
            )
        faithfulness.unlink()

        claimed = manage_lease(
            self.scratch,
            "P06",
            "claim",
            invocation_id=invocation_id,
            token=token,
            now=1000,
        )
        lease_path = Path(claimed["lease_path"])
        lease_path.unlink()
        lease_path.symlink_to(outside / "lease.json")
        with self.assertRaisesRegex(BenchmarkToolError, "symlink"):
            manage_lease(self.scratch, "P06", "check", now=1001)

    def test_cli_claim_redacts_token_and_hands_off_owner_only_credentials(
        self,
    ) -> None:
        credential_directory = self.root / "credential"
        credential_directory.mkdir(mode=0o700)
        credential_file = credential_directory / "P06.json"
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--credential-out",
                    str(credential_file),
                    "--ttl-seconds",
                    "120",
                ]
            )
        self.assertEqual(status, 0, stderr.getvalue())
        public = json.loads(stdout.getvalue())
        self.assertNotIn("token", public)
        self.assertEqual(public["credential_file"], str(credential_file))
        self.assertEqual(credential_file.stat().st_mode & 0o777, 0o600)
        invocation_id, token = read_lease_credentials(
            credential_file, self.scratch, "P06"
        )
        self.assertEqual(invocation_id, public["lease"]["invocation_id"])
        self.assertNotIn(token, stdout.getvalue())
        self.assertNotIn(token, stderr.getvalue())
        self.assertNotIn(
            token,
            Path(public["lease_path"]).read_text(encoding="utf-8"),
        )

        release_stdout = io.StringIO()
        release_stderr = io.StringIO()
        with redirect_stdout(release_stdout), redirect_stderr(release_stderr):
            release_status = main(
                [
                    "release",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--credential-file",
                    str(credential_file),
                ]
            )
        self.assertEqual(release_status, 0, release_stderr.getvalue())
        released = json.loads(release_stdout.getvalue())
        self.assertTrue(released["released"])
        self.assertTrue(released["credential_file_removed"])
        self.assertFalse(credential_file.exists())
        self.assertNotIn(token, release_stdout.getvalue())
        self.assertNotIn(token, release_stderr.getvalue())

    def test_cli_redacts_caller_supplied_token_and_requires_generated_sink(
        self,
    ) -> None:
        no_sink_stdout = io.StringIO()
        no_sink_stderr = io.StringIO()
        with redirect_stdout(no_sink_stdout), redirect_stderr(no_sink_stderr):
            status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                ]
            )
        self.assertEqual(status, 2)
        self.assertIn("--credential-out", no_sink_stderr.getvalue())
        self.assertFalse(
            manage_lease(self.scratch, "P06", "check")["held"]
        )

        invocation_id, token = self._credentials()
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--invocation-id",
                    invocation_id,
                    "--token",
                    token,
                ]
            )
        self.assertEqual(status, 0, stderr.getvalue())
        self.assertNotIn(token, stdout.getvalue())
        self.assertNotIn(token, stderr.getvalue())
        self.assertNotIn("token", json.loads(stdout.getvalue()))

        reused_stdout = io.StringIO()
        reused_stderr = io.StringIO()
        with redirect_stdout(reused_stdout), redirect_stderr(reused_stderr):
            reused_status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--invocation-id",
                    invocation_id,
                    "--token",
                    token,
                ]
            )
        self.assertEqual(reused_status, 0, reused_stderr.getvalue())
        reused = json.loads(reused_stdout.getvalue())
        self.assertTrue(reused["reused"])
        self.assertNotIn("token", reused)
        self.assertNotIn(token, reused_stdout.getvalue())
        self.assertNotIn(token, reused_stderr.getvalue())
        manage_lease(
            self.scratch,
            "P06",
            "release",
            invocation_id=invocation_id,
            token=token,
        )

    def test_cli_claim_rejects_insecure_or_existing_credential_destination(
        self,
    ) -> None:
        insecure_directory = self.root / "insecure-credential"
        insecure_directory.mkdir(mode=0o755)
        insecure_file = insecure_directory / "P06.json"
        stderr = io.StringIO()
        with redirect_stdout(io.StringIO()), redirect_stderr(stderr):
            status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--credential-out",
                    str(insecure_file),
                ]
            )
        self.assertEqual(status, 2)
        self.assertIn("no group/other permissions", stderr.getvalue())
        self.assertFalse(insecure_file.exists())
        self.assertFalse(
            manage_lease(self.scratch, "P06", "check")["held"]
        )

        secure_directory = self.root / "secure-credential"
        secure_directory.mkdir(mode=0o700)
        existing = secure_directory / "P06.json"
        existing.write_text("user-owned\n", encoding="utf-8")
        existing.chmod(0o600)
        stderr = io.StringIO()
        with redirect_stdout(io.StringIO()), redirect_stderr(stderr):
            status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--credential-out",
                    str(existing),
                ]
            )
        self.assertEqual(status, 2)
        self.assertIn("refusing overwrite", stderr.getvalue())
        self.assertEqual(existing.read_text(encoding="utf-8"), "user-owned\n")
        self.assertFalse(
            manage_lease(self.scratch, "P06", "check")["held"]
        )

    def test_cli_claim_conflict_removes_newly_generated_credential_file(
        self,
    ) -> None:
        invocation_id, token = self._credentials()
        manage_lease(
            self.scratch,
            "P06",
            "claim",
            invocation_id=invocation_id,
            token=token,
        )
        credential_directory = self.root / "conflicting-credential"
        credential_directory.mkdir(mode=0o700)
        credential_file = credential_directory / "P06.json"
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            status = main(
                [
                    "claim",
                    "--scratch-root",
                    str(self.scratch),
                    "--paper-id",
                    "P06",
                    "--credential-out",
                    str(credential_file),
                ]
            )
        self.assertEqual(status, 2)
        self.assertIn("active writer lease", stderr.getvalue())
        self.assertFalse(credential_file.exists())
        self.assertNotIn(token, stdout.getvalue())
        self.assertNotIn(token, stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
