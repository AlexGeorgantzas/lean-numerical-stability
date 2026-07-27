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

from common import BenchmarkToolError, write_json  # noqa: E402
from hashes import (  # noqa: E402
    create_manifest,
    load_manifest,
    stage_manifest_files,
    verify_manifest,
)


class HashManifestTests(unittest.TestCase):
    def test_create_verify_stage_and_detect_change(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "source"
            root.mkdir()
            (root / "a.txt").write_text("alpha\n", encoding="utf-8")
            (root / "nested").mkdir()
            (root / "nested" / "b.lean").write_text("#check True\n", encoding="utf-8")
            (root / "ignored.log").write_text("ignore\n", encoding="utf-8")

            manifest = create_manifest(root, excludes=["*.log"])
            self.assertEqual(
                [entry["path"] for entry in manifest["files"]],
                ["a.txt", "nested/b.lean"],
            )
            self.assertTrue(verify_manifest(root, manifest)["ok"])

            destination = Path(raw) / "staged"
            staged = stage_manifest_files(root, destination, manifest)
            self.assertTrue(staged["ok"])
            self.assertEqual((destination / "a.txt").read_text(), "alpha\n")

            (destination / "a.txt").write_text("changed\n", encoding="utf-8")
            report = verify_manifest(destination, manifest)
            self.assertFalse(report["ok"])
            self.assertEqual(report["changed"][0]["path"], "a.txt")

    def test_manifest_rejects_path_traversal_and_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "source"
            root.mkdir()
            (root / "real.txt").write_text("value", encoding="utf-8")
            symlink = root / "link.txt"
            try:
                symlink.symlink_to(root / "real.txt")
            except OSError:
                self.skipTest("symlinks are unavailable")
            with self.assertRaises(BenchmarkToolError):
                create_manifest(root)

            bad = Path(raw) / "bad.json"
            bad.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "kind": "highambench-controlled-files",
                        "label": "bad",
                        "files": [
                            {"path": "../escape", "sha256": "0" * 64, "bytes": 0}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaises(BenchmarkToolError):
                load_manifest(bad)

    def test_manifest_round_trip(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "source"
            root.mkdir()
            (root / "one").write_bytes(b"1")
            manifest = create_manifest(root, requested=["one"], label="test")
            path = Path(raw) / "manifest.json"
            write_json(path, manifest)
            self.assertEqual(load_manifest(path), manifest)

    def test_include_filter_and_hardlink_staging_build_a_pruned_tree(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "source"
            (root / "pkg" / "build").mkdir(parents=True)
            kept = root / "pkg" / "build" / "Module.olean"
            kept.write_bytes(b"compiled")
            (root / "pkg" / "build" / "Module.trace").write_text(
                "unfrozen path", encoding="utf-8"
            )
            source = root / "pkg" / "Source.lean"
            source.write_text("#check True\n", encoding="utf-8")
            manifest = create_manifest(
                root,
                includes=["*.olean", "pkg/Source.lean"],
                label="runtime-view",
            )
            self.assertEqual(
                [entry["path"] for entry in manifest["files"]],
                ["pkg/Source.lean", "pkg/build/Module.olean"],
            )
            destination = Path(raw) / "runtime"
            stage_manifest_files(root, destination, manifest, hardlink=True)
            staged = destination / "pkg" / "build" / "Module.olean"
            self.assertEqual(staged.stat().st_ino, kept.stat().st_ino)
            self.assertFalse((destination / "pkg" / "build" / "Module.trace").exists())

    def test_stage_cli_copies_only_manifested_files(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "source"
            root.mkdir()
            (root / "kept.txt").write_text("kept\n", encoding="utf-8")
            (root / "extra.txt").write_text("extra\n", encoding="utf-8")
            manifest_path = Path(raw) / "manifest.json"
            write_json(
                manifest_path,
                create_manifest(root, requested=["kept.txt"], label="pruned"),
            )
            destination = Path(raw) / "destination"
            completed = subprocess.run(
                [
                    sys.executable,
                    str(TOOLS / "hashes.py"),
                    "stage",
                    "--root",
                    str(root),
                    "--manifest",
                    str(manifest_path),
                    "--destination",
                    str(destination),
                ],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertTrue((destination / "kept.txt").is_file())
            self.assertFalse((destination / "extra.txt").exists())


if __name__ == "__main__":
    unittest.main()
