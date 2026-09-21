"""Source-stripped contestant driver for the Design-17 statement benchmark."""

from __future__ import annotations

from pathlib import Path
import re

from codex_driver import CodexDriver
from common import BenchmarkError


class StatementCodexDriver(CodexDriver):
    """Expose compiled package trees without mounting their Lean source."""

    def _bwrap_command(
        self,
        inner: list[str],
        *,
        workspace: Path,
        artifact_dir: Path,
        output_schema: Path | None,
        network_marker: Path | None = None,
    ) -> list[str]:
        command = super()._bwrap_command(
            inner,
            workspace=workspace,
            artifact_dir=artifact_dir,
            output_schema=output_schema,
            network_marker=network_marker,
        )
        assert self.packages_root is not None
        full_mount = [
            "--ro-bind",
            str(self.packages_root.resolve()),
            "/packages",
        ]
        mount_index = next(
            (
                index
                for index in range(len(command) - 2)
                if command[index : index + 3] == full_mount
            ),
            None,
        )
        if mount_index is None:
            raise BenchmarkError("statement driver could not replace the package mount")
        replacement = ["--dir", "/packages"]
        compiled_count = 0
        for package in sorted(self.packages_root.iterdir(), key=lambda path: path.name):
            if (
                package.is_symlink()
                or not package.is_dir()
                or not re.fullmatch(r"[A-Za-z0-9._-]+", package.name)
            ):
                raise BenchmarkError(f"unsafe package runtime entry: {package}")
            compiled = package / ".lake" / "build" / "lib" / "lean"
            if not compiled.is_dir() or compiled.is_symlink():
                continue
            compiled_count += 1
            target = f"/packages/{package.name}"
            replacement.extend(
                [
                    "--dir",
                    target,
                    "--dir",
                    target + "/.lake",
                    "--dir",
                    target + "/.lake/build",
                    "--dir",
                    target + "/.lake/build/lib",
                    "--ro-bind",
                    str(compiled.resolve()),
                    target + "/.lake/build/lib/lean",
                ]
            )
        if compiled_count == 0:
            raise BenchmarkError("statement driver found no compiled package runtimes")
        command[mount_index : mount_index + 3] = replacement
        return command
