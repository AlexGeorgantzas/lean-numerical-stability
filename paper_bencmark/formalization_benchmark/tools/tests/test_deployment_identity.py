from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from deployment import GLOBAL_REGISTRY_ROOT, load_deployment  # noqa: E402


class DeploymentIdentityTests(unittest.TestCase):
    def test_loader_requires_pilot2_release_and_account_global_registry(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            artifact = root / "artifact"
            artifact.write_bytes(b"fixture")
            directory = root / "directory"
            directory.mkdir()
            predecessor = root / "predecessor-runs"
            predecessor.mkdir()
            record = {
                "schema_version": "formalization-deployment-1",
                "pilot_id": "formalization-benchmark-t2-pilot-2",
                "release_commit": "a" * 40,
                "release_manifest_sha256": "b" * 64,
                "manifest_payload_sha256": "c" * 64,
                "global_registry_root": str(GLOBAL_REGISTRY_ROOT),
                "predecessor_run_root": str(predecessor),
                "run_root": str(root / "runs"),
                "strict_hardware": False,
            }
            for name in (
                "codex_binary", "auth_file", "bwrap_binary", "offline_shell",
                "library_snapshot_record", "runtime_snapshot_record",
            ):
                record[name] = str(artifact)
            for name in (
                "pdf_root", "toolchain_root", "packages_root", "library_source",
                "library_olean",
            ):
                record[name] = str(directory)
            path = root / "deployment.json"

            def read(value: dict[str, object]):
                path.write_text(json.dumps(value), encoding="utf-8")
                return load_deployment(path)

            loaded = read(record)
            self.assertEqual(loaded.pilot_id, "formalization-benchmark-t2-pilot-2")
            self.assertEqual(loaded.global_registry_root, GLOBAL_REGISTRY_ROOT)
            self.assertEqual(loaded.predecessor_run_root, predecessor.resolve())
            for field, replacement in (
                ("pilot_id", "formalization-benchmark-t2-pilot-1"),
                ("manifest_payload_sha256", "not-a-sha256"),
                ("global_registry_root", str(root / "another-registry")),
            ):
                with self.subTest(field=field), self.assertRaises(BenchmarkError):
                    read({**record, field: replacement})


if __name__ == "__main__":
    unittest.main()
