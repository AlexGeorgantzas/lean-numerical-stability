from __future__ import annotations

from pathlib import Path

from common import BenchmarkError, minimal_system_mount_args
from deployment import Deployment


def _lean_path(deployment: Deployment, condition: str) -> str:
    paths: list[str] = []
    if condition == "L":
        paths.append("/library-olean")
    elif condition != "N":
        raise BenchmarkError(f"unknown benchmark condition: {condition}")
    mathlib = deployment.packages_root / "mathlib" / ".lake" / "build" / "lib" / "lean"
    if not mathlib.is_dir():
        raise BenchmarkError(f"Mathlib olean directory is missing: {mathlib}")
    paths.append("/packages/mathlib/.lake/build/lib/lean")
    for package in sorted(deployment.packages_root.iterdir(), key=lambda item: item.name):
        compiled = package / ".lake" / "build" / "lib" / "lean"
        if package.name != "mathlib" and compiled.is_dir():
            paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
    paths.extend(["/lean/lib/lean", "/workspace"])
    return ":".join(paths)


def _base(deployment: Deployment, condition: str) -> list[str]:
    """Return a no-network, minimal-filesystem Bubblewrap command prefix.

    ``{workspace}`` is deliberately left as a placeholder.  The validator and
    dossier builder substitute their fresh scratch directory immediately
    before invoking this argv array.
    """

    command = [
        str(deployment.bwrap_binary.resolve()),
        "--unshare-all",
        "--die-with-parent",
        "--new-session",
        "--clearenv",
    ]
    command.extend(minimal_system_mount_args())
    command.extend(
        [
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--tmpfs",
            "/tmp",
            "--dir",
            "/home",
            "--dir",
            "/home/bench",
            "--bind",
            "{workspace}",
            "/workspace",
            "--ro-bind",
            str(deployment.toolchain_root.resolve()),
            "/lean",
            "--ro-bind",
            str(deployment.packages_root.resolve()),
            "/packages",
        ]
    )
    if condition == "L":
        command.extend(
            [
                "--ro-bind",
                str(deployment.library_olean.resolve()),
                "/library-olean",
            ]
        )
    elif condition != "N":
        raise BenchmarkError(f"unknown benchmark condition: {condition}")
    command.extend(
        [
            "--setenv",
            "HOME",
            "/home/bench",
            "--setenv",
            "PATH",
            "/lean/bin:/usr/bin",
            "--setenv",
            "LEAN_PATH",
            _lean_path(deployment, condition),
            "--setenv",
            "NO_COLOR",
            "1",
            "--chdir",
            "/workspace",
        ]
    )
    return command


def compiler_command(deployment: Deployment, condition: str) -> tuple[str, ...]:
    return tuple(
        _base(deployment, condition)
        + [
            "/lean/bin/lean",
            "--root",
            "/workspace",
            "-o",
            "/workspace/Candidate.olean",
            "/workspace/Candidate.lean",
        ]
    )


def extractor_command(
    deployment: Deployment, condition: str, helper: Path
) -> tuple[str, ...]:
    if not helper.is_file() or helper.is_symlink():
        raise BenchmarkError(f"semantic extractor helper is missing or unsafe: {helper}")
    base = _base(deployment, condition)
    # Insert the trusted helper before environment setup and command execution.
    command_index = base.index("--setenv")
    base[command_index:command_index] = [
        "--ro-bind",
        str(helper.resolve()),
        "/audit-helper.lean",
    ]
    return tuple(
        base
        + [
            "/lean/bin/lean",
            "--run",
            "/audit-helper.lean",
            "Candidate",
            "HighamBenchCandidate.target",
            "/workspace/recursive-prefixes.txt",
        ]
    )


def signature_interface_command(
    deployment: Deployment, helper: Path
) -> tuple[str, ...]:
    """Run the trusted one-hop type-dependency extractor in the L environment."""

    if not helper.is_file() or helper.is_symlink():
        raise BenchmarkError(
            f"signature-interface helper is missing or unsafe: {helper}"
        )
    base = _base(deployment, "L")
    command_index = base.index("--setenv")
    base[command_index:command_index] = [
        "--ro-bind",
        str(helper.resolve()),
        "/signature-interface-helper.lean",
    ]
    return tuple(
        base
        + [
            "/lean/bin/lean",
            "--run",
            "/signature-interface-helper.lean",
            "/workspace/signature-interface-seeds.tsv",
        ]
    )


def signature_render_command(deployment: Deployment) -> tuple[str, ...]:
    """Render packet signatures through Lean's ordinary command frontend."""

    return tuple(
        _base(deployment, "L")
        + [
            "/lean/bin/lean",
            "--root",
            "/workspace",
            "-o",
            "/tmp/signature-render.olean",
            "/workspace/signature-render.lean",
        ]
    )
