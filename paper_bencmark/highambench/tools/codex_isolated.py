#!/usr/bin/env python3
"""Run one fresh Codex proof attempt inside a curated bubblewrap filesystem.

The Codex control process needs provider network access.  Model-generated shell
commands are launched through ``offline_shell.c``.  That launcher installs a
kernel seccomp rule that denies socket operations and is inherited by every
command descendant.  The outer filesystem contains only system programs, the
frozen Lean toolchain, mathlib, the task workspace, and (for condition L)
NumStability.  Codex's own nested filesystem sandbox is disabled because nested
user namespaces are unavailable inside the outer bubblewrap namespace; the
outer namespace supplies the filesystem boundary instead.

Authentication is copied into a fresh temporary Codex state directory only for
startup.  It is removed as soon as Codex reports that the new thread started,
before the model can issue a shell command.

The runner also supplies a fresh marker file.  The offline shell appends to it
whenever the kernel blocks a socket-related system call, so the outer runner can
reject an attempt even if that attempt later writes a valid proof.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Iterable


DISABLED_FEATURES = (
    "apps",
    "browser_use",
    "computer_use",
    "goals",
    "image_generation",
    "memories",
    "multi_agent",
    "plugins",
    "remote_plugin",
    "skill_search",
    "standalone_web_search",
)

NETWORK_VIOLATION_MARKER_ENV = "HIGHAMBENCH_NETWORK_VIOLATION_MARKER"


def positive_int(raw: str) -> int:
    try:
        value = int(raw)
    except ValueError as error:
        raise argparse.ArgumentTypeError("must be an integer") from error
    if value <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def _below(root: Path, path: Path) -> Path:
    root = root.resolve()
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise ValueError(f"path must stay below workspace {root}: {path}") from error
    return path


def _read_required(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as error:
        raise RuntimeError(f"cannot read fixed prompt input {path}: {error}") from error


def build_prompt(prompt_file: Path, context_file: Path, target_file: Path) -> str:
    return "\n\n".join(
        (
            _read_required(prompt_file).rstrip(),
            "## Task context\n\n" + _read_required(context_file).rstrip(),
            "## Fixed Lean target\n\n```lean\n"
            + _read_required(target_file).rstrip()
            + "\n```",
        )
    ) + "\n"


def normalized_usage(event: dict[str, Any]) -> dict[str, int] | None:
    if event.get("type") != "turn.completed" or not isinstance(event.get("usage"), dict):
        return None
    usage = event["usage"]
    fields = ("input_tokens", "cached_input_tokens", "output_tokens")
    if not all(
        isinstance(usage.get(field), int)
        and not isinstance(usage[field], bool)
        and usage[field] >= 0
        for field in fields
    ):
        return None
    return {field: int(usage[field]) for field in fields}


def _bind(command: list[str], source: Path, destination: str, *, writable: bool) -> None:
    source = source.resolve()
    if not source.exists():
        raise RuntimeError(f"required bind source does not exist: {source}")
    command.extend(("--bind" if writable else "--ro-bind", str(source), destination))


def bubblewrap_command(args: argparse.Namespace, state_home: Path) -> list[str]:
    if args.token_limit <= 0:
        raise RuntimeError("token limit must be positive")
    marker = getattr(args, "network_violation_marker", None)
    if not isinstance(marker, Path):
        raise RuntimeError("a per-run network-violation marker is required")
    marker = _below(args.workspace, marker)
    if marker.is_symlink() or not marker.is_file():
        raise RuntimeError("network-violation marker must be a regular file")
    marker_relative = marker.relative_to(args.workspace.resolve())
    marker_inside = "/workspace/" + marker_relative.as_posix()
    command = [
        str(args.bwrap.resolve()),
        "--unshare-all",
        "--share-net",
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
        "--dir",
        "/run",
        "--dir",
        "/run/systemd",
    ]
    _bind(command, args.resolver_root, "/run/systemd/resolve", writable=False)
    command.extend(("--dir", "/u501"))
    _bind(command, state_home, args.inside_home, writable=True)
    _bind(command, args.workspace, "/workspace", writable=True)
    if args.controlled_relative:
        controlled = _below(args.workspace, args.workspace / args.controlled_relative)
        _bind(command, controlled, f"/workspace/{args.controlled_relative}", writable=False)
    _bind(command, args.codex, "/codex", writable=False)
    _bind(command, args.offline_shell, "/offline-bash", writable=False)
    _bind(command, args.toolchain_root, "/lean", writable=False)
    _bind(command, args.packages_root, "/packages", writable=False)
    if args.shared_olean_root is not None:
        _bind(command, args.shared_olean_root, "/shared-olean", writable=False)

    # Trusted, frozen paths must win module-name resolution.  The writable
    # workspace is deliberately last so a generated file cannot shadow a
    # controlled definition, NumStability, mathlib, or the Lean toolchain.
    lean_paths: list[str] = []
    if args.shared_olean_root is not None:
        lean_paths.append("/shared-olean")
    if args.shared_root_relative:
        lean_paths.append(f"/workspace/{args.shared_root_relative}")
    if args.condition == "L":
        lean_paths.append("/library-olean")
    lean_paths.append("/packages/mathlib/.lake/build/lib/lean")
    for package in sorted(args.packages_root.iterdir(), key=lambda item: item.name):
        build_path = package / ".lake" / "build" / "lib" / "lean"
        if package.name != "mathlib" and build_path.is_dir():
            lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
    lean_paths.append("/lean/lib/lean")
    lean_paths.append("/workspace")

    if args.condition == "L":
        if args.library_source is None or args.library_olean is None:
            raise RuntimeError("condition L requires --library-source and --library-olean")
        command.extend(("--dir", "/library"))
        _bind(command, args.library_source, "/library/NumStability", writable=False)
        if args.library_root_file is not None:
            _bind(command, args.library_root_file, "/library/NumStability.lean", writable=False)
        _bind(command, args.library_olean, "/library-olean", writable=False)
    command.extend(
        (
            "--setenv",
            "PATH",
            "/lean/bin:/usr/bin:/bin",
            "--setenv",
            "LEAN_PATH",
            ":".join(lean_paths),
            "--setenv",
            "SHELL",
            "/offline-bash",
            "--setenv",
            NETWORK_VIOLATION_MARKER_ENV,
            marker_inside,
            "--chdir",
            "/workspace",
            "/codex",
            "exec",
            "--ephemeral",
            "--ignore-user-config",
            "--ignore-rules",
            "--skip-git-repo-check",
            "--strict-config",
            "--dangerously-bypass-approvals-and-sandbox",
            "--model",
            args.model,
            "--config",
            f'model_reasoning_effort="{args.reasoning_effort}"',
            "--config",
            "features.rollout_budget=true",
            "--config",
            f"features.rollout_budget.limit_tokens={args.token_limit}",
            "--config",
            "features.rollout_budget.prefill_token_weight=1",
            "--config",
            "features.rollout_budget.sampling_token_weight=1",
            "--json",
        )
    )
    for feature in DISABLED_FEATURES:
        command.extend(("--disable", feature))
    command.append("-")
    return command


def _sanitized_environment() -> dict[str, str]:
    allowed = ("HOME", "LANG", "LC_ALL", "LOGNAME", "TERM", "TZ", "USER")
    environment = {key: os.environ[key] for key in allowed if key in os.environ}
    environment["PATH"] = "/usr/bin:/bin"
    return environment


def run(args: argparse.Namespace) -> int:
    workspace = args.workspace.resolve()
    if not workspace.is_dir():
        raise RuntimeError(f"workspace is not a directory: {workspace}")
    if args.token_limit <= 0:
        raise RuntimeError("token limit must be positive")
    usage_output = _below(workspace, args.usage_output)
    marker_raw = os.environ.get(NETWORK_VIOLATION_MARKER_ENV)
    if not marker_raw:
        raise RuntimeError(
            f"runner did not supply {NETWORK_VIOLATION_MARKER_ENV}"
        )
    marker_input = Path(marker_raw)
    if not marker_input.is_absolute():
        raise RuntimeError("network-violation marker path must be absolute")
    args.network_violation_marker = _below(workspace, marker_input)
    prompt = build_prompt(args.prompt_file, args.context_file, args.target_file)

    state_parent = args.state_parent.resolve()
    state_parent.mkdir(parents=True, exist_ok=True)
    state_root = Path(tempfile.mkdtemp(prefix="highambench-codex-", dir=state_parent))
    state_home = state_root / "home"
    codex_state = state_home / ".codex"
    codex_state.mkdir(parents=True)
    temporary_auth = codex_state / "auth.json"
    try:
        shutil.copyfile(args.auth_file, temporary_auth)
        temporary_auth.chmod(0o600)
        command = bubblewrap_command(args, state_home)
        process = subprocess.Popen(
            command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            env=_sanitized_environment(),
            start_new_session=True,
        )
        assert process.stdin is not None and process.stdout is not None
        process.stdin.write(prompt)
        process.stdin.close()
        auth_removed = False
        for line in process.stdout:
            sys.stdout.write(line)
            sys.stdout.flush()
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not auth_removed and event.get("type") in ("thread.started", "turn.started"):
                temporary_auth.unlink(missing_ok=True)
                auth_removed = True
            usage = normalized_usage(event)
            if usage is not None:
                usage_output.parent.mkdir(parents=True, exist_ok=True)
                temporary = usage_output.with_suffix(usage_output.suffix + ".tmp")
                temporary.write_text(json.dumps(usage, sort_keys=True) + "\n", encoding="utf-8")
                os.replace(temporary, usage_output)
        return process.wait()
    finally:
        temporary_auth.unlink(missing_ok=True)
        shutil.rmtree(state_root, ignore_errors=True)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--condition", required=True, choices=("N", "L"))
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--controlled-relative", default="task")
    parser.add_argument("--shared-root-relative", default="task/shared")
    parser.add_argument("--prompt-file", required=True, type=Path)
    parser.add_argument("--context-file", required=True, type=Path)
    parser.add_argument("--target-file", required=True, type=Path)
    parser.add_argument("--usage-output", required=True, type=Path)
    parser.add_argument("--codex", required=True, type=Path)
    parser.add_argument("--auth-file", required=True, type=Path)
    parser.add_argument("--offline-shell", required=True, type=Path)
    parser.add_argument("--toolchain-root", required=True, type=Path)
    parser.add_argument("--packages-root", required=True, type=Path)
    parser.add_argument("--shared-olean-root", type=Path)
    parser.add_argument("--library-source", type=Path)
    parser.add_argument("--library-root-file", type=Path)
    parser.add_argument("--library-olean", type=Path)
    parser.add_argument("--bwrap", type=Path, default=Path("/bin/bwrap"))
    parser.add_argument(
        "--resolver-root", type=Path, default=Path("/run/systemd/resolve")
    )
    parser.add_argument("--inside-home", default="/u501/m2fetrat")
    parser.add_argument("--state-parent", type=Path, default=Path("/tmp"))
    parser.add_argument("--model", default="gpt-5.6-terra")
    parser.add_argument("--reasoning-effort", default="medium")
    parser.add_argument("--token-limit", type=positive_int, required=True)
    return parser


def main() -> int:
    try:
        return run(make_parser().parse_args())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"isolated Codex adapter error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
