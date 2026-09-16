from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import freeze_manifest  # noqa: E402
import manifest_control  # noqa: E402
from common import BenchmarkError  # noqa: E402


class FreezeManifestCliTests(unittest.TestCase):
    def test_manifest_rejects_different_config_pilot_even_with_valid_self_hash(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            config = root / "config.json"
            config.write_text(json.dumps({"pilot_id": "pilot-2"}), encoding="utf-8")
            manifest = {
                "schema_version": "formalization-benchmark-manifest-1",
                "base_commit": manifest_control.EXPECTED_BASE_COMMIT,
                "pilot_id": "pilot-1",
                "config": {"relative_path": "config.json", "sha256": "0" * 64},
            }
            manifest["manifest_payload_sha256"] = manifest_control.manifest_payload_sha256(manifest)
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            with (
                mock.patch.object(manifest_control, "MANIFEST_PATH", manifest_path),
                mock.patch.object(manifest_control, "verify_file_ref", return_value=config),
                self.assertRaisesRegex(BenchmarkError, "pilot identities disagree"),
            ):
                manifest_control.verify_manifest()

    def test_help_is_side_effect_free(self) -> None:
        with (
            mock.patch.object(freeze_manifest, "build") as build,
            mock.patch.object(freeze_manifest, "write_json_atomic") as write,
            redirect_stdout(StringIO()),
            redirect_stderr(StringIO()),
            self.assertRaises(SystemExit) as stopped,
        ):
            freeze_manifest.main(["--help"])

        self.assertEqual(stopped.exception.code, 0)
        build.assert_not_called()
        write.assert_not_called()

    def test_every_non_help_argument_is_rejected_without_writing(self) -> None:
        for arguments in (["unexpected"], ["--"], ["--help", "unexpected"]):
            with self.subTest(arguments=arguments):
                with (
                    mock.patch.object(freeze_manifest, "build") as build,
                    mock.patch.object(freeze_manifest, "write_json_atomic") as write,
                    redirect_stdout(StringIO()),
                    redirect_stderr(StringIO()),
                    self.assertRaises(SystemExit) as stopped,
                ):
                    freeze_manifest.main(arguments)

                self.assertEqual(stopped.exception.code, 2)
                build.assert_not_called()
                write.assert_not_called()

    def test_no_arguments_runs_the_release_authoring_action(self) -> None:
        manifest = {"manifest_payload_sha256": "a" * 64}
        output = StringIO()
        with (
            mock.patch.object(freeze_manifest, "build", return_value=manifest) as build,
            mock.patch.object(freeze_manifest, "write_json_atomic") as write,
            redirect_stdout(output),
        ):
            self.assertEqual(freeze_manifest.main([]), 0)

        build.assert_called_once_with()
        write.assert_called_once_with(
            freeze_manifest.MANIFEST_PATH, manifest, mode=0o644
        )
        self.assertEqual(output.getvalue(), "a" * 64 + "\n")


if __name__ == "__main__":
    unittest.main()
