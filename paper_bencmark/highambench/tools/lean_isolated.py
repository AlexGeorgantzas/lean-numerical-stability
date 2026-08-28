#!/usr/bin/env python3
"""Compile, probe, or dependency-audit Lean code in an offline N/L namespace."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys
from typing import Sequence

try:
    from .codex_isolated import _below, _bind
except ImportError:  # Direct script execution.
    from codex_isolated import _below, _bind  # type: ignore


def namespace_prefix(args: argparse.Namespace) -> list[str]:
    workspace = args.workspace.resolve()
    command = [
        str(args.bwrap.resolve()),
        "--unshare-all",
        "--die-with-parent",
        "--ro-bind",
        "/usr",
        "/usr",
        "--ro-bind",
        "/bin",
        "/bin",
        "--ro-bind",
        "/lib",
        "/lib",
        "--ro-bind",
        "/lib64",
        "/lib64",
        "--ro-bind",
        "/etc",
        "/etc",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
    ]
    _bind(command, workspace, "/workspace", writable=True)
    _bind(command, args.toolchain_root, "/lean", writable=False)
    _bind(command, args.packages_root, "/packages", writable=False)
    if args.shared_olean_root is not None:
        _bind(command, args.shared_olean_root, "/shared-olean", writable=False)

    # Trusted, read-only modules must precede the candidate workspace.  The
    # workspace remains on the path so Submission and proved helper modules can
    # be loaded, but it may not shadow the frozen shared setting or libraries.
    lean_paths = [
        f"/workspace/{args.shared_root_relative}",
        "/packages/mathlib/.lake/build/lib/lean",
    ]
    if args.shared_olean_root is not None:
        lean_paths.insert(0, "/shared-olean")
    for package in sorted(args.packages_root.iterdir(), key=lambda item: item.name):
        build_path = package / ".lake" / "build" / "lib" / "lean"
        if package.name != "mathlib" and build_path.is_dir():
            lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
    lean_paths.append("/lean/lib/lean")

    if args.condition == "L":
        if args.library_source is None or args.library_olean is None:
            raise RuntimeError("condition L requires --library-source and --library-olean")
        command.extend(("--dir", "/library"))
        _bind(command, args.library_source, "/library/NumStability", writable=False)
        if args.library_root_file is not None:
            _bind(command, args.library_root_file, "/library/NumStability.lean", writable=False)
        _bind(command, args.library_olean, "/library-olean", writable=False)
        lean_paths.insert(0, "/library-olean")

    lean_paths.append("/workspace")

    command.extend(
        (
            "--setenv",
            "PATH",
            "/lean/bin:/usr/bin:/bin",
            "--setenv",
            "LEAN_PATH",
            ":".join(lean_paths),
            "--chdir",
            "/workspace",
        )
    )
    return command


def inside_source(workspace: Path, source: Path) -> str:
    source = _below(workspace, source)
    return "/workspace/" + source.relative_to(workspace.resolve()).as_posix()


def run_command(command: Sequence[str]) -> int:
    completed = subprocess.run(
        list(command),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        env={"PATH": "/usr/bin:/bin", "LANG": os.environ.get("LANG", "C.UTF-8")},
    )
    sys.stdout.write(completed.stdout)
    return completed.returncode


def run(args: argparse.Namespace) -> int:
    workspace = args.workspace.resolve()
    if not workspace.is_dir():
        raise RuntimeError(f"workspace is not a directory: {workspace}")
    prefix = namespace_prefix(args)
    source = inside_source(workspace, args.source)
    if args.action in ("compile", "probe"):
        return run_command(prefix + ["/lean/bin/lean", source])

    relative = _below(workspace, args.source).relative_to(workspace).with_suffix(".olean")
    inside_olean = "/workspace/" + relative.as_posix()
    if args.action == "olean":
        return run_command(prefix + ["/lean/bin/lean", "-o", inside_olean, source])

    audit_pairs_file = getattr(args, "audit_pairs_file", None)
    target_theorem = getattr(args, "target_theorem", None)
    plural_audit = audit_pairs_file is not None
    if args.audit_helper is None or not args.submission_module:
        raise RuntimeError("audit needs --audit-helper and --submission-module")
    if plural_audit == bool(target_theorem):
        raise RuntimeError(
            "audit needs exactly one of --target-theorem or --audit-pairs-file"
        )
    if args.action == "build-audit":
        compile_code = run_command(prefix + ["/lean/bin/lean", "-o", inside_olean, source])
        if compile_code != 0:
            return compile_code
    elif not (workspace / relative).is_file():
        raise RuntimeError(
            "audit requires a previously compiler-produced olean for the checked source"
        )
    audit_prefix = list(prefix)
    _bind(audit_prefix, args.audit_helper, "/audit.lean", writable=False)
    if plural_audit:
        if not args.expected_module or args.expected_theorem:
            raise RuntimeError(
                "plural semantic audit needs --expected-module but not --expected-theorem"
            )
        if args.local_modules_file is None:
            raise RuntimeError("plural semantic audit needs --local-modules-file")
        audit_arguments = [
            args.submission_module,
            "--pairs-file",
            inside_source(workspace, audit_pairs_file),
            args.expected_module,
            inside_source(workspace, args.local_modules_file),
        ]
    else:
        audit_arguments = [args.submission_module, target_theorem]
        if args.expected_module or args.expected_theorem:
            if not args.expected_module or not args.expected_theorem:
                raise RuntimeError(
                    "semantic audit needs both --expected-module and --expected-theorem"
                )
            audit_arguments.extend([args.expected_module, args.expected_theorem])
            if args.local_modules_file is None:
                raise RuntimeError("semantic audit needs --local-modules-file")
            audit_arguments.append(inside_source(workspace, args.local_modules_file))
    return run_command(
        audit_prefix
        + [
            "/lean/bin/lean",
            "--run",
            "/audit.lean",
            *audit_arguments,
        ]
    )


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "action", choices=("compile", "probe", "olean", "audit", "build-audit")
    )
    parser.add_argument("--condition", required=True, choices=("N", "L"))
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--toolchain-root", required=True, type=Path)
    parser.add_argument("--packages-root", required=True, type=Path)
    parser.add_argument("--shared-olean-root", type=Path)
    parser.add_argument("--shared-root-relative", default="task/shared")
    parser.add_argument("--library-source", type=Path)
    parser.add_argument("--library-root-file", type=Path)
    parser.add_argument("--library-olean", type=Path)
    parser.add_argument("--audit-helper", type=Path)
    parser.add_argument("--submission-module")
    parser.add_argument("--target-theorem")
    parser.add_argument("--audit-pairs-file", type=Path)
    parser.add_argument("--expected-module")
    parser.add_argument("--expected-theorem")
    parser.add_argument("--local-modules-file", type=Path)
    parser.add_argument("--bwrap", type=Path, default=Path("/bin/bwrap"))
    return parser


def main() -> int:
    try:
        return run(make_parser().parse_args())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"isolated Lean adapter error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
