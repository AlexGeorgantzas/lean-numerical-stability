from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
import design18_atlas  # noqa: E402


class Pilot18AtlasTests(unittest.TestCase):
    def test_release_verification_fails_on_catalog_change(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            atlas = root / "numstability"
            atlas.mkdir()
            metadata = {"library_commit": "a" * 40,
                        "source_closure_sha256": "b" * 64,
                        "declaration_count": 1}
            for name in ("GUIDE.md", "atlas.json", "declarations.jsonl",
                         "modules.tsv", "query.py", "show.py"):
                (atlas / name).write_text(json.dumps(metadata) if name == "atlas.json" else name)
            metadata["declarations_sha256"] = sha256_file(atlas / "declarations.jsonl")
            (atlas / "atlas.json").write_text(json.dumps(metadata))
            files = {path.name: sha256_file(path) for path in atlas.iterdir()}
            release = {"schema_version": "pilot-18-atlas-release-1",
                       "numstability": {**metadata,
                                        "atlas_json_sha256": files["atlas.json"],
                                        "files": files}}
            (root / "ATLAS_RELEASE.json").write_text(json.dumps(release))
            with mock.patch.object(design18_atlas, "DESIGN_ROOT", root):
                self.assertEqual(design18_atlas.verify_release_atlas(
                    "numstability", atlas), atlas.resolve())
                (atlas / "query.py").write_text("tampered")
                with self.assertRaisesRegex(BenchmarkError, "file changed"):
                    design18_atlas.verify_release_atlas("numstability", atlas)


if __name__ == "__main__":
    unittest.main()
