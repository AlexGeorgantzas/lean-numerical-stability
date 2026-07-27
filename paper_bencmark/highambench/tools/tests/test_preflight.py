from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from preflight import probe_forbidden_import, run_preflight, scan_artifact_leaks  # noqa: E402


class PreflightTests(unittest.TestCase):
    def _script(self, directory: Path, body: str) -> Path:
        path = directory / "probe_driver.py"
        path.write_text(body, encoding="utf-8")
        return path

    def test_scan_reports_names_contents_and_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "workspace"
            root.mkdir()
            (root / "NumStability.olean").write_bytes(b"compiled")
            (root / "lakefile.toml").write_text(
                'moreLinkArgs := #["lean-fp-analysis"]\n', encoding="utf-8"
            )
            target = Path(raw) / "outside"
            target.write_text("x", encoding="utf-8")
            try:
                (root / "escape").symlink_to(target)
            except OSError:
                pass
            kinds = {entry["kind"] for entry in scan_artifact_leaks(root)}
            self.assertIn("path", kinds)
            self.assertIn("content", kinds)
            if (root / "escape").is_symlink():
                self.assertIn("symlink", kinds)

    def test_missing_module_is_a_reliable_successful_preflight(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            outer = Path(raw)
            root = outer / "workspace"
            root.mkdir()
            (root / "task").mkdir()
            (root / "task" / "Target.lean").write_text(
                "theorem target : True := by trivial\n", encoding="utf-8"
            )
            script = self._script(
                outer,
                "import sys\n"
                "print(\"error: unknown module prefix 'NumStability'\")\n"
                "raise SystemExit(1)\n",
            )
            result = run_preflight(root, probe_command=[sys.executable, str(script)])
            self.assertTrue(result["ok"])
            self.assertTrue(result["complete"])
            self.assertIs(result["import_probe"]["importable"], False)
            self.assertEqual(result["filesystem_scan"]["regular_file_count"], 1)
            self.assertEqual(result["filesystem_scan"]["directory_count"], 1)
            self.assertEqual(
                result["filesystem_scan"]["markers"],
                ["NumStability", "numStability", "lean-fp-analysis"],
            )

    def test_unrelated_compiler_failure_is_not_evidence_of_isolation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            outer = Path(raw)
            root = outer / "workspace"
            root.mkdir()
            script = self._script(
                outer,
                "print('toolchain configuration is broken')\nraise SystemExit(1)\n",
            )
            result = probe_forbidden_import(root, [sys.executable, str(script)])
            self.assertFalse(result["reliable"])
            self.assertIsNone(result["importable"])

    def test_importable_module_fails_preflight(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            outer = Path(raw)
            root = outer / "workspace"
            root.mkdir()
            script = self._script(outer, "raise SystemExit(0)\n")
            result = run_preflight(root, probe_command=[sys.executable, str(script)])
            self.assertFalse(result["ok"])
            self.assertIs(result["import_probe"]["importable"], True)


if __name__ == "__main__":
    unittest.main()
