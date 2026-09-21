from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from library_atlas import build_library_atlas  # noqa: E402


class LibraryAtlasTests(unittest.TestCase):
    def test_builds_deterministic_searchable_atlas(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "NumStability"
            (source / "FloatingPoint").mkdir(parents=True)
            module = source / "FloatingPoint" / "Model.lean"
            module.write_text(
                "namespace NumStability\n"
                "/-- Standard relative-error coefficient. -/\n"
                "def gamma (n : Nat) (u : Real) : Real := n * u / (1 - n * u)\n"
                "theorem gamma_nonneg (h : 0 ≤ u) : 0 ≤ gamma n u := by sorry\n"
                "end NumStability\n",
                encoding="utf-8",
            )
            output = root / "atlas-a"
            metadata = build_library_atlas(
                source_root=source,
                root_module=None,
                output_root=output,
                library_commit="a" * 40,
            )
            self.assertEqual(metadata["declaration_count"], 2)
            records = [
                json.loads(line)
                for line in (output / "declarations.jsonl").read_text().splitlines()
            ]
            self.assertEqual(records[0]["name"], "NumStability.gamma")
            self.assertIn("relative-error coefficient", records[0]["documentation"])
            self.assertEqual(records[0]["module"], "NumStability.FloatingPoint.Model")
            self.assertIn("reuse-first", (output / "GUIDE.md").read_text().lower())
            query = (output / "query.py").read_text(encoding="utf-8")
            self.assertIn("--limit", query)
            inspector = subprocess.run(
                [
                    sys.executable,
                    str(output / "show.py"),
                    "NumStability.gamma",
                    "--source-root",
                    str(root),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertIn("PRIMARY", inspector.stdout)
            self.assertIn("SOURCE NumStability/FloatingPoint/Model.lean", inspector.stdout)
            self.assertIn("NumStability.gamma_nonneg", inspector.stdout)
            self.assertIn("bounded API/source view", (output / "GUIDE.md").read_text())

            output_b = root / "atlas-b"
            metadata_b = build_library_atlas(
                source_root=source,
                root_module=None,
                output_root=output_b,
                library_commit="a" * 40,
            )
            self.assertEqual(metadata, metadata_b)
            self.assertEqual(
                (output / "declarations.jsonl").read_bytes(),
                (output_b / "declarations.jsonl").read_bytes(),
            )


if __name__ == "__main__":
    unittest.main()
