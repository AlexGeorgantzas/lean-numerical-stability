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
    def test_loader_requires_pilot13_release_host_and_eleven_predecessors(self) -> None:
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
            great_ancestral_predecessor = root / "great-ancestral-predecessor-runs"
            great_ancestral_predecessor.mkdir()
            fifth_ancestral_predecessor = root / "fifth-ancestral-predecessor-runs"
            fifth_ancestral_predecessor.mkdir()
            sixth_ancestral_predecessor = root / "sixth-ancestral-predecessor-runs"
            sixth_ancestral_predecessor.mkdir()
            seventh_ancestral_predecessor = root / "seventh-ancestral-predecessor-runs"
            seventh_ancestral_predecessor.mkdir()
            eighth_ancestral_predecessor = root / "eighth-ancestral-predecessor-runs"
            eighth_ancestral_predecessor.mkdir()
            ninth_ancestral_predecessor = root / "ninth-ancestral-predecessor-runs"
            ninth_ancestral_predecessor.mkdir()
            tenth_ancestral_predecessor = root / "tenth-ancestral-predecessor-runs"
            tenth_ancestral_predecessor.mkdir()
            eleventh_ancestral_predecessor = root / "eleventh-ancestral-predecessor-runs"
            eleventh_ancestral_predecessor.mkdir()
            record = {
                "schema_version": "formalization-deployment-1",
                "pilot_id": "formalization-benchmark-pilot-13",
                "release_commit": "a" * 40,
                "release_manifest_sha256": "b" * 64,
                "manifest_payload_sha256": "c" * 64,
                "global_registry_root": str(GLOBAL_REGISTRY_ROOT),
                "predecessor_run_root": str(predecessor),
                "legacy_predecessor_run_root": str(legacy_predecessor),
                "ancestral_predecessor_run_root": str(ancestral_predecessor),
                "great_ancestral_predecessor_run_root": str(great_ancestral_predecessor),
                "fifth_ancestral_predecessor_run_root": str(fifth_ancestral_predecessor),
                "sixth_ancestral_predecessor_run_root": str(sixth_ancestral_predecessor),
                "seventh_ancestral_predecessor_run_root": str(seventh_ancestral_predecessor),
                "eighth_ancestral_predecessor_run_root": str(eighth_ancestral_predecessor),
                "ninth_ancestral_predecessor_run_root": str(ninth_ancestral_predecessor),
                "tenth_ancestral_predecessor_run_root": str(tenth_ancestral_predecessor),
                "eleventh_ancestral_predecessor_run_root": str(eleventh_ancestral_predecessor),
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
            self.assertEqual(loaded.pilot_id, "formalization-benchmark-pilot-13")
            self.assertEqual(loaded.global_registry_root, GLOBAL_REGISTRY_ROOT)
            self.assertEqual(loaded.predecessor_run_root, predecessor.resolve())
            self.assertEqual(
                loaded.legacy_predecessor_run_root, legacy_predecessor.resolve()
            )
            self.assertEqual(
                loaded.ancestral_predecessor_run_root, ancestral_predecessor.resolve()
            )
            self.assertEqual(
                loaded.great_ancestral_predecessor_run_root,
                great_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.fifth_ancestral_predecessor_run_root,
                fifth_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.sixth_ancestral_predecessor_run_root,
                sixth_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.seventh_ancestral_predecessor_run_root,
                seventh_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.eighth_ancestral_predecessor_run_root,
                eighth_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.ninth_ancestral_predecessor_run_root,
                ninth_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.tenth_ancestral_predecessor_run_root,
                tenth_ancestral_predecessor.resolve(),
            )
            self.assertEqual(
                loaded.eleventh_ancestral_predecessor_run_root,
                eleventh_ancestral_predecessor.resolve(),
            )
            self.assertEqual(loaded.code_mode_host_sha256, sha256_file(host))
            for field, replacement in (
                ("pilot_id", "formalization-benchmark-t2-pilot-4"),
                ("manifest_payload_sha256", "not-a-sha256"),
                ("global_registry_root", str(root / "another-registry")),
                ("legacy_predecessor_run_root", str(predecessor)),
                ("ancestral_predecessor_run_root", str(predecessor)),
                ("great_ancestral_predecessor_run_root", str(predecessor)),
                ("fifth_ancestral_predecessor_run_root", str(predecessor)),
                ("sixth_ancestral_predecessor_run_root", str(predecessor)),
                ("seventh_ancestral_predecessor_run_root", str(predecessor)),
                ("eighth_ancestral_predecessor_run_root", str(predecessor)),
                ("ninth_ancestral_predecessor_run_root", str(predecessor)),
                ("tenth_ancestral_predecessor_run_root", str(predecessor)),
                ("eleventh_ancestral_predecessor_run_root", str(predecessor)),
                ("code_mode_host_sha256", "0" * 64),
                ("code_mode_host_binary", str(codex)),
            ):
                with self.subTest(field=field), self.assertRaises(BenchmarkError):
                    read({**record, field: replacement})
            with self.assertRaisesRegex(BenchmarkError, "legacy_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "legacy_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "great_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "great_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "fifth_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "fifth_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "sixth_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "sixth_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "seventh_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "seventh_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "eighth_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "eighth_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "ninth_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "ninth_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "tenth_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "tenth_ancestral_predecessor_run_root"})
            with self.assertRaisesRegex(BenchmarkError, "eleventh_ancestral_predecessor_run_root is missing"):
                read({key: value for key, value in record.items() if key != "eleventh_ancestral_predecessor_run_root"})


if __name__ == "__main__":
    unittest.main()
