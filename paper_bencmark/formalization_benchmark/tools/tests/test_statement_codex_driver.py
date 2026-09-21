from __future__ import annotations

from pathlib import Path
import tempfile
from unittest import mock
import unittest


TOOLS = Path(__file__).resolve().parents[1]
import sys

if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from codex_driver import CodexDriver  # noqa: E402
from statement_codex_driver import StatementCodexDriver  # noqa: E402


class StatementCodexDriverTests(unittest.TestCase):
    def test_replaces_full_package_mount_with_compiled_trees(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            packages = root / "packages"
            mathlib_olean = packages / "mathlib" / ".lake" / "build" / "lib" / "lean"
            mathlib_olean.mkdir(parents=True)
            source = packages / "mathlib" / "Mathlib"
            source.mkdir()
            (source / "Secret.lean").write_text("source must not be mounted\n")
            driver = object.__new__(StatementCodexDriver)
            driver.packages_root = packages
            base = [
                "bwrap",
                "--ro-bind",
                str(packages.resolve()),
                "/packages",
                "inner",
            ]
            with mock.patch.object(CodexDriver, "_bwrap_command", return_value=base):
                command = driver._bwrap_command(
                    ["inner"],
                    workspace=root,
                    artifact_dir=root,
                    output_schema=None,
                )
            mounts = [command[index : index + 3] for index in range(len(command) - 2)]
            self.assertNotIn(
                ["--ro-bind", str(packages.resolve()), "/packages"], mounts
            )
            self.assertIn(
                [
                    "--ro-bind",
                    str(mathlib_olean.resolve()),
                    "/packages/mathlib/.lake/build/lib/lean",
                ],
                mounts,
            )
            self.assertNotIn(str(source.resolve()), command)


if __name__ == "__main__":
    unittest.main()
