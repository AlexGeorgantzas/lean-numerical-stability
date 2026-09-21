from __future__ import annotations

import argparse
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest.mock import Mock, patch


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from design16_full_audit import run_cli  # noqa: E402


def _args(root: Path) -> argparse.Namespace:
    candidate = root / "Candidate.lean"
    paper = root / "paper.pdf"
    packet = root / "task.md"
    candidate.write_text("theorem HighamBenchCandidate.target : True := by trivial\n")
    paper.write_bytes(b"%PDF-test")
    packet.write_text("source packet\n")
    return argparse.Namespace(
        deployment=root / "deployment.json",
        task_id="H5-5",
        candidate=candidate,
        paper=paper,
        source_packet=packet,
        output_root=root / "audit-output",
        condition="N",
        model="gpt-6-astra",
        reasoning_effort="high",
        timeout_seconds=7200,
        validation_timeout_seconds=600,
        infrastructure_retries=2,
        statement_only=False,
    )


class Design16FullAuditTests(unittest.TestCase):
    @patch("design16_full_audit.AuditController")
    @patch("design16_full_audit.extractor_command", return_value=["extractor"])
    @patch("design16_full_audit.compiler_command", return_value=["lean"])
    @patch("design16_full_audit.prepare_candidate_audit")
    @patch("design16_full_audit.load_deployment")
    def test_run_seals_condition_blind_canonical_result(
        self,
        load_deployment: Mock,
        prepare: Mock,
        _compiler: Mock,
        _extractor: Mock,
        controller_class: Mock,
    ) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root)
            load_deployment.return_value = types.SimpleNamespace(
                codex_binary=root / "codex",
                code_mode_host_sha256="a" * 64,
                auth_file=root / "auth.json",
                bwrap_binary=root / "bwrap",
                offline_shell=root / "shell",
                toolchain_root=root / "lean",
                packages_root=root / "packages",
            )
            prepare.return_value = (
                {"semantic_sha256": "b" * 64},
                {
                    "blind_semantic_sha256": "b" * 64,
                    "candidate": {"sha256": "c" * 64},
                },
            )
            controller_class.return_value.run.return_value = {
                "verdict": "faithful",
                "accepted": True,
            }
            result = run_cli(args)
            self.assertEqual(result["decision"]["verdict"], "faithful")
            self.assertTrue(result["condition_blind"])
            self.assertTrue(result["attempt_blind"])
            self.assertTrue(result["auditor_tokens_excluded_from_benchmark"])
            self.assertTrue((args.output_root / "result.json").is_file())
            controller_class.return_value.run.assert_called_once()

    def test_refuses_existing_output_root(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root)
            args.output_root.mkdir()
            with self.assertRaises(BenchmarkError):
                run_cli(args)


if __name__ == "__main__":
    unittest.main()
