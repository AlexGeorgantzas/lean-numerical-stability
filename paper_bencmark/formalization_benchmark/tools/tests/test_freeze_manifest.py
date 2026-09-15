from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import sys
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import freeze_manifest  # noqa: E402


class FreezeManifestCliTests(unittest.TestCase):
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
