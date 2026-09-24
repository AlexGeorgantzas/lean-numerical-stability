"""Small deterministic checks for the predeclared proof-code-line counter."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from common import BenchmarkError
from design29_report import _code_lines


class ProofCodeLineCountTests(unittest.TestCase):
    def test_nested_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Candidate.lean"
            source.write_text(
                'import Mathlib\n'
                '/- outer\n'
                '   /- nested -/\n'
                '   -/\n'
                'def s := "not -- a comment" -- trailing comment\n'
                '-- only a comment\n'
                'theorem target : True := by\n'
                '  trivial\n',
                encoding="utf-8",
            )
            self.assertEqual(_code_lines(source), 4)

    def test_unterminated_comment_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Candidate.lean"
            source.write_text("/- not closed\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                _code_lines(source)


if __name__ == "__main__":
    unittest.main()
