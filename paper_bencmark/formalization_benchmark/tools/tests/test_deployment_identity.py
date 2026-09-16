from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
from deployment import GLOBAL_REGISTRY_ROOT, load_deployment  # noqa: E402


class DeploymentIdentityTests(unittest.TestCase):
    def test_loader_requires_pilot4_release_host_and_three_predecessors(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            artifact = root / "artifact"
            artifact.write_bytes(b"fixture")
            codex = root / "codex"
            codex.write_bytes(b"fixture-codex")
            codex.chmod(0o700)
            host = root / "codex-code-mode-host"
            host.write_bytes(b"fixture-host")
            host.chmod(0o700)
            directory = root / "directory"
            directory.mkdir()
            predecessor = root / "predecessor-runs"
            predecessor.mkdir()
            legacy_predecessor = root / "legacy-predecessor-runs"
            legacy_predecessor.mkdir()
            ancestral_predecessor = root / "ancestral-predecessor-runs"
            ancestral_predecessor.mkdir()
            record = {
                "schema_version": "formalization-deployment-1",
                "pilot_id": "formalization-benchmark-t2-pilot-4",
                "release_commit": "a" * 40,
                "release_manifest_sha256": "b" * 64,
                "manifest_payload_sha256": "c" * 64,
                "global_registry_root": str(GLOBAL_REGISTRY_ROOT),
                "predecessor_run_root": str(predecessor),
                "legacy_predecessor_run_root": str(legacy_predecessor),
                "ancestral_predecessor_run_root": str(ancestral_predecessor),
                "code_mode_host_binary": str(host),
                "code_mode_host_sha256": sha256_file(host),
                "run_root": str(root / "runs"),
                "strict_hardware": False,
            }
            for name in (
                "auth_file", "bwrap_binary", "offline_shell",
                "library_snapshot_record", "runtime_snapshot_record",
            ):
                record[name] = str(artifact)
            record["codex_binary"] = str(codex)
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
            self.assertEqual(loaded.pilot_id, "formalization-benchmark-t2-pilot-4")
            self.assertEqual(loaded.global_registry_root, GLOBAL_REGISTRY_ROOT)
            self.assertEqual(loaded.predecessor_run_root, predecessor.resolve())
            self.assertEqual(
                loaded.legacy_predecessor_run_root, legacy_predecessor.resolve()
            )
            self.assertEqual(
                loaded.ancestral_predecessor_run_root, ancestral_predecessor.resolve()
            )
            self.assertEqual(loaded.code_mode_host_sha256, sha256_file(host))
            for field, replacement in (
                ("pilot_id", "formalization-benchmark-t2-pilot-3"),
                ("manifest_payload_sha256", "not-a-sha256"),
                ("global_registry_root", str(root / "another-registry")),
                ("legacy_predecessor_run_root", str(predecessor)),
                ("ancestral_predecessor_run_root", str(predecessor)),
                ("code_mode_host_sha256", "0" * 64),
                ("code_mode_host_binary", str(codex)),
            ):
                with self.subTest(field=field), self.assertRaises(BenchmarkError):
                    read({**record, field: replacement})
            with self.assertRaisesRegex(BenchmarkError, "legacy_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "legacy_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "ancestral_predecessor_run_root"})


if __name__ == "__main__":
    unittest.main()
