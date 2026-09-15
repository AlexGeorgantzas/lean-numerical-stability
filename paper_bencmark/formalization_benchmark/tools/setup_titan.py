from __future__ import annotations

import argparse
import json
import os
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping

from codex_driver import CodexDriver
from common import (
    BenchmarkError,
    file_tree_fingerprint,
    minimal_system_mount_args,
    sha256_bytes,
    sha256_file,
    stable_regular_bytes,
    treatment_free_runtime_manifest,
    tree_manifest,
    utc_now,
    visible_system_runtime_manifest,
    write_bytes_atomic,
    write_json_atomic,
)
from deployment import Deployment
from formalization_validator import run_bounded_command
from hardware import (
    frozen_hardware_identity,
    host_cpu_selection,
    snapshot_hardware,
    systemd_service_envelope_prefix,
)
from manifest_control import EXPECTED_BASE_COMMIT, task_record, verify_manifest
from measure_library_build import validate_build_record
from runtime_canary import run_runtime_canaries


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY_ROOT = ROOT.parents[1]
FROZEN_LIBRARY_COMMIT = "45813a95dacf577461bae13f033af0dbc985a225"
FROZEN_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc3"


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def run(command: list[str], *, cwd: Path | None = None) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        raise BenchmarkError(
            f"command failed ({completed.returncode}): {' '.join(command)}\n{completed.stdout}"
        )
    return completed.stdout.strip()


def command_path(name: str) -> Path:
    raw = shutil.which(name)
    if raw is None:
        raise BenchmarkError(f"required Titan command is missing: {name}")
    return Path(raw).resolve()


def measured_build_service_environment(deployment_root: Path) -> dict[str, str]:
    """Prepare stable, private paths passed into the measured build service."""

    tooling_root = deployment_root.parent / "tooling"
    paths = {
        "TMPDIR": tooling_root / "tmp",
        "XDG_CACHE_HOME": tooling_root / "cache",
        "ELAN_HOME": tooling_root / "elan",
    }
    for path in (tooling_root, *paths.values()):
        path.mkdir(parents=True, exist_ok=True, mode=0o700)
        metadata = path.lstat()
        if (
            path.is_symlink()
            or not path.is_dir()
            or metadata.st_uid != os.getuid()
            or metadata.st_mode & 0o077
        ):
            raise BenchmarkError(f"measured-build tooling path is unsafe: {path.name}")
    return {key: str(path.resolve()) for key, path in sorted(paths.items())}


def measured_build_command(
    *,
    systemd_run: Path,
    build_runner: Path,
    checkout: Path,
    artifact_root: Path,
    toolchain_root: Path,
    expected_commit: str,
    mathlib_commit: str,
    lean_toolchain: str,
    service_environment: Mapping[str, str],
) -> list[str]:
    environment_arguments = [
        argument
        for key, value in sorted(service_environment.items())
        for argument in ("--setenv", f"{key}={value}")
    ]
    return [
        *systemd_service_envelope_prefix(str(systemd_run)),
        *environment_arguments,
        *isolated_runner_command(
            build_runner,
            "--checkout",
            str(checkout),
            "--artifact-root",
            str(artifact_root),
            "--toolchain-root",
            str(toolchain_root),
            "--expected-commit",
            expected_commit,
            "--mathlib-commit",
            mathlib_commit,
            "--lean-toolchain",
            lean_toolchain,
        ),
    ]


def copy_tree_read_only(source: Path, destination: Path) -> None:
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination, symlinks=False)
    for path in [destination, *destination.rglob("*")]:
        mode = path.stat().st_mode
        if path.is_dir():
            path.chmod((mode & 0o555) or 0o500)
        else:
            path.chmod((mode & 0o555) or 0o400)


def find_toolchain_root(*, cwd: Path) -> Path:
    lean = Path(run(["elan", "which", "lean"], cwd=cwd)).resolve()
    if lean.name != "lean" or lean.parent.name != "bin":
        raise BenchmarkError(f"could not derive Lean toolchain root from {lean}")
    return lean.parent.parent


def isolated_runner_command(runner: Path, *arguments: str) -> list[str]:
    """Invoke a frozen sibling-import script without weakening Python isolation."""

    runner = runner.resolve()
    bootstrap = (
        "import runpy,sys;"
        f"sys.path.insert(0,{json.dumps(str(runner.parent))});"
        f"sys.argv[0]={json.dumps(str(runner))};"
        f"runpy.run_path({json.dumps(str(runner))},run_name='__main__')"
    )
    return [sys.executable, "-I", "-B", "-c", bootstrap, *arguments]


def launcher_bytes(
    deployment_record: Path, deployment_sha256: str, runner: Path
) -> bytes:
    command = " ".join(shlex.quote(item) for item in isolated_runner_command(runner))
    source = f"""#!/bin/sh
set -eu
export HIGHAMBENCH_FORMALIZATION_DEPLOYMENT={shlex.quote(str(deployment_record))}
export HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256={shlex.quote(deployment_sha256)}
exec {command} "$@"
    """
    return source.encode("utf-8")


def write_launcher(
    path: Path, deployment_record: Path, deployment_sha256: str, runner: Path
) -> None:
    payload = launcher_bytes(deployment_record, deployment_sha256, runner)
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o500)
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
        os.fchmod(descriptor, 0o500)
    finally:
        os.close(descriptor)
    fsync_directory(path.parent)


def install_skill_atomically(source: Path, destination: Path) -> None:
    """Replace an installed skill without deleting the prior copy first.

    Staging and backup names are unique so concurrent installer invocations do
    not delete one another's files.  The old directory is restored if the
    final rename fails.  A backup that cannot be cleaned after a successful
    install is deliberately retained in its uniquely named transaction
    directory rather than turning a usable installation into a failed setup.
    """

    if not source.is_dir() or source.is_symlink():
        raise BenchmarkError(f"skill source is missing or unsafe: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    for abandoned in destination.parent.glob(f".{destination.name}.install-*"):
        if not abandoned.is_dir() or abandoned.is_symlink():
            raise BenchmarkError(f"unsafe abandoned skill transaction: {abandoned}")
        previous = abandoned / "previous"
        staged_abandoned = abandoned / "staged"
        if not os.path.lexists(destination) and previous.is_dir() and not previous.is_symlink():
            os.replace(previous, destination)
            fsync_directory(destination.parent)
        if os.path.lexists(destination):
            shutil.rmtree(abandoned, ignore_errors=True)
        elif staged_abandoned.is_dir() and not staged_abandoned.is_symlink():
            shutil.rmtree(abandoned, ignore_errors=True)
    if destination.exists() or destination.is_symlink():
        if not destination.is_dir() or destination.is_symlink():
            raise BenchmarkError(f"installed skill destination is unsafe: {destination}")

    transaction_root = Path(
        tempfile.mkdtemp(
            prefix=f".{destination.name}.install-", dir=str(destination.parent)
        )
    )
    staged = transaction_root / "staged"
    backup = transaction_root / "previous"
    destination_existed = destination.exists()
    try:
        shutil.copytree(source, staged)
        if destination_existed:
            os.replace(destination, backup)
            fsync_directory(destination.parent)
        os.replace(staged, destination)
        fsync_directory(destination.parent)
    except BaseException as install_error:
        try:
            if backup.is_dir() and not backup.is_symlink():
                if os.path.lexists(destination):
                    os.replace(destination, staged)
                    fsync_directory(destination.parent)
                os.replace(backup, destination)
                fsync_directory(destination.parent)
            elif not destination_existed and os.path.lexists(destination):
                os.replace(destination, staged)
                fsync_directory(destination.parent)
        except BaseException as restore_error:
            raise BenchmarkError(
                "skill install failed and its previous installation could not be "
                f"restored; recover it from {transaction_root}: {restore_error}"
            ) from install_error
        shutil.rmtree(transaction_root, ignore_errors=True)
        raise
    # The destination is now durably committed. Cleanup is best-effort and
    # must not turn a usable deployment into a rollback after the skill swap.
    try:
        shutil.rmtree(transaction_root)
    except BaseException:
        pass


def make_tree_read_only(root: Path) -> None:
    for path in sorted(root.rglob("*"), key=lambda item: len(item.parts), reverse=True):
        if path.is_symlink():
            raise BenchmarkError(f"frozen release contains a symlink: {path}")
        mode = path.stat().st_mode
        path.chmod((mode & 0o555) or (0o500 if path.is_dir() else 0o400))
    root.chmod(0o500)


def directory_identity(path: Path) -> tuple[int, int]:
    """Read a directory identity without following its final path component."""

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        opened = os.fstat(descriptor)
        named = os.stat(path, follow_symlinks=False)
    finally:
        os.close(descriptor)
    if not stat.S_ISDIR(opened.st_mode) or not stat.S_ISDIR(named.st_mode):
        raise BenchmarkError(f"deployment root is no longer a directory: {path}")
    opened_identity = (opened.st_dev, opened.st_ino)
    if opened_identity != (named.st_dev, named.st_ino):
        raise BenchmarkError("deployment root changed while its identity was checked")
    return opened_identity


def assert_directory_identity(
    path: Path, expected: tuple[int, int], *, phase: str
) -> None:
    try:
        actual = directory_identity(path)
    except (OSError, BenchmarkError) as error:
        raise BenchmarkError(
            f"installer-owned deployment root became unsafe during {phase}: {error}"
        ) from error
    if actual != expected:
        raise BenchmarkError(
            f"installer-owned deployment root identity changed during {phase}"
        )


def remove_owned_deployment_root(
    path: Path, expected_identity: tuple[int, int]
) -> None:
    """Remove only a failed root created by the current installer invocation."""

    assert_directory_identity(path, expected_identity, phase="failure cleanup entry")
    quarantine = path.parent / f".{path.name}.failed-{os.getpid()}-{os.urandom(8).hex()}"
    os.rename(path, quarantine)
    fsync_directory(path.parent)
    # Reauthenticate after the atomic rename. A last-moment substitution is
    # preserved at the quarantine name and is never recursively deleted.
    assert_directory_identity(
        quarantine, expected_identity, phase="failure cleanup quarantine"
    )
    for current, directories, files in os.walk(quarantine, topdown=True):
        assert_directory_identity(
            quarantine, expected_identity, phase="failure cleanup traversal"
        )
        os.chmod(current, 0o700)
        for name in directories:
            candidate = Path(current) / name
            if not candidate.is_symlink():
                candidate.chmod(0o700)
        for name in files:
            candidate = Path(current) / name
            if not candidate.is_symlink():
                candidate.chmod(0o600)
    assert_directory_identity(
        quarantine, expected_identity, phase="failure cleanup removal"
    )
    shutil.rmtree(quarantine)
    fsync_directory(path.parent)


def run_command_sandbox_canary(deployment: Deployment, condition: str) -> dict:
    """Exercise Landlock, seccomp, control isolation, and Lean through Bash."""

    if condition not in {"N", "L"}:
        raise BenchmarkError(f"invalid command-canary condition: {condition}")
    with tempfile.TemporaryDirectory(
        prefix=f"formalization-command-{condition}-", dir=deployment.path.parent
    ) as temporary:
        root = Path(temporary)
        workspace = root / "workspace"
        control = root / "control"
        workspace.mkdir()
        control.mkdir()
        marker = root / "network-violations.bin"
        write_bytes_atomic(marker, b"", mode=0o600)
        fake_auth = control / "auth.json"
        fake_secret = b"command-canary-secret\n"
        write_bytes_atomic(fake_auth, fake_secret, mode=0o600)
        import_line = "import NumStability" if condition == "L" else "import Mathlib"
        write_bytes_atomic(
            workspace / "Canary.lean",
            f"{import_line}\n#check Nat\n".encode("utf-8"),
            mode=0o600,
        )
        library_assertion = (
            "test -r /library/NumStability.lean"
            if condition == "L"
            else "test ! -e /library/NumStability.lean"
        )
        script = f"""set -eu
test -z "${{CODEX_HOME+x}}"
test "$HOME" = /home/bench
test "$(ulimit -f)" = 262144
test "$(ulimit -c)" = 0
printf 'workspace-ok\\n' > /workspace/write-ok
if cat /control/codex/auth.json >/dev/null 2>&1; then exit 41; fi
if : > /control/codex/auth.json 2>/dev/null; then exit 42; fi
if printf injected > /control/codex/config.toml 2>/dev/null; then exit 43; fi
if mv /control/codex/auth.json /workspace/moved-auth 2>/dev/null; then exit 44; fi
if ln /control/codex/auth.json /workspace/linked-auth 2>/dev/null; then exit 45; fi
if ln -s /control/codex/auth.json /workspace/control-link 2>/dev/null; then exit 46; fi
if mkfifo /workspace/generated-fifo 2>/dev/null; then exit 47; fi
if dd if=/proc/1/mem of=/dev/null bs=1 count=1 >/dev/null 2>&1; then exit 48; fi
if cat /proc/1/environ >/dev/null 2>&1; then exit 49; fi
if ls /proc/1/fd >/dev/null 2>&1; then exit 50; fi
if cat /proc/1/root/control/codex/auth.json >/dev/null 2>&1; then exit 51; fi
{library_assertion}
lean --root /workspace -o /workspace/Canary.olean /workspace/Canary.lean
python3 - <<'PY'
import ctypes
import errno
import fcntl
import os
libc = ctypes.CDLL(None, use_errno=True)
ctypes.set_errno(0)
result = libc.socket(2, 1, 0)
if result != -1 or ctypes.get_errno() != errno.EPERM:
    raise SystemExit(51)
open('/workspace/network-ok', 'w', encoding='utf-8').write('socket-denied\n')

result = libc.syscall(0x40000000 | 41, 2, 1, 0)
if result != -1 or ctypes.get_errno() != errno.EPERM:
    raise SystemExit(52)
open('/workspace/x32-ok', 'w', encoding='utf-8').write('x32-denied\n')

def require_denied(number, *arguments):
    ctypes.set_errno(0)
    result = libc.syscall(number, *arguments)
    if result != -1 or ctypes.get_errno() != errno.EPERM:
        raise SystemExit(53)

# x86-64 syscall numbers. The launcher itself rejects every other ABI.
require_denied(62, 2147483647, 0)  # kill(guessed-positive-pid, 0)
require_denied(109, 0, os.getsid(0))  # setpgid cannot rejoin supervisor group
require_denied(234, os.getpid(), os.getpid(), 0)  # tgkill
require_denied(434, os.getpid(), 0)  # pidfd_open
require_denied(424, -1, 0, 0, 0)  # pidfd_send_signal
read_fd, write_fd = os.pipe()
require_denied(72, read_fd, fcntl.F_SETOWN, os.getppid())
owner = ctypes.c_int(os.getppid())
require_denied(16, read_fd, 0x8901, ctypes.byref(owner))  # ioctl FIOSETOWN
require_denied(16, read_fd, 0x4008667C, ctypes.byref(owner))  # FIOSETOWN_EX
os.close(read_fd)
os.close(write_fd)
require_denied(302, 1, 7, 0, 0)  # prlimit64(PID 1, RLIMIT_NOFILE, ...)
require_denied(141, 0, 1, 0)  # setpriority(PRIO_PROCESS, PID 1, ...)
require_denied(203, 1, 0, 0)  # sched_setaffinity(PID 1, ...)
require_denied(142, 1, 0)  # sched_setparam(PID 1, ...)
require_denied(144, 1, 0, 0)  # sched_setscheduler(PID 1, ...)
require_denied(314, 1, 0, 0)  # sched_setattr(PID 1, ...)
require_denied(251, 1, 1, 0)  # ioprio_set(IOPRIO_WHO_PROCESS, PID 1, ...)
require_denied(256, 1, 0, 0, 0)  # migrate_pages(PID 1, ...)
require_denied(279, 1, 0, 0, 0, 0, 0)  # move_pages(PID 1, ...)
require_denied(90, b'/workspace/write-ok', 0o600)  # chmod
require_denied(188, b'/workspace/write-ok', b'user.highambench', b'x', 1, 0)
require_denied(280, -100, b'/workspace/write-ok', 0, 0)  # utimensat

ctypes.set_errno(0)
if libc.syscall(62, 0, 0) != 0:  # kill(0, 0) stays local to this process group.
    raise SystemExit(54)
open('/workspace/isolation-ok', 'w', encoding='utf-8').write(
    'signals-resources-scheduling-and-metadata-denied\n'
)
PY
if exec 9<>/dev/tcp/127.0.0.1/9; then exit 47; fi
"""
        command = [
            str(deployment.bwrap_binary),
            "--unshare-all",
            "--share-net",
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
                "--dir",
                "/control",
                "--bind",
                str(control),
                "/control/codex",
                "--bind",
                str(workspace),
                "/workspace",
                "--ro-bind",
                str(deployment.offline_shell),
                "/offline-bash",
                "--ro-bind",
                str(deployment.toolchain_root),
                "/lean",
                "--ro-bind",
                str(deployment.packages_root),
                "/packages",
            ]
        )
        lean_paths: list[str] = []
        if condition == "L":
            command.extend(
                [
                    "--dir",
                    "/library",
                    "--ro-bind",
                    str(deployment.library_source),
                    "/library/NumStability",
                    "--ro-bind",
                    str(deployment.library_source.parent / "NumStability.lean"),
                    "/library/NumStability.lean",
                    "--ro-bind",
                    str(deployment.library_olean),
                    "/library-olean",
                ]
            )
            lean_paths.append("/library-olean")
        for package in sorted(deployment.packages_root.iterdir(), key=lambda item: item.name):
            compiled = package / ".lake" / "build" / "lib" / "lean"
            if compiled.is_dir():
                lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
        lean_paths.extend(["/lean/lib/lean", "/workspace"])
        command.extend(
            [
                "--dir",
                "/run",
                "--dir",
                "/run/highambench",
                "--bind",
                str(marker),
                "/run/highambench/network-violations",
                "--setenv",
                "CODEX_HOME",
                "/control/codex",
                "--setenv",
                "HOME",
                "/home/bench",
                "--setenv",
                "PATH",
                "/lean/bin:/usr/bin",
                "--setenv",
                "LEAN_PATH",
                ":".join(lean_paths),
                "--setenv",
                "HIGHAMBENCH_NETWORK_VIOLATION_MARKER",
                "/run/highambench/network-violations",
                "--chdir",
                "/workspace",
                "/offline-bash",
                "-c",
                script,
            ]
        )
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=False,
        )
        checks = {
            "command_succeeded": completed.returncode == 0,
            "workspace_write_succeeded": (workspace / "write-ok").read_bytes()
            == b"workspace-ok\n",
            "lean_compile_succeeded": (workspace / "Canary.olean").is_file(),
            "x32_syscalls_denied": (workspace / "x32-ok").read_bytes()
            == b"x32-denied\n",
            "native_socket_syscall_denied": (
                workspace / "network-ok"
            ).read_bytes()
            == b"socket-denied\n",
            "signal_and_metadata_syscalls_denied": (
                workspace / "isolation-ok"
            ).read_bytes()
            == b"signals-resources-scheduling-and-metadata-denied\n",
            "control_auth_unchanged": fake_auth.read_bytes() == fake_secret,
            "control_config_absent": not (control / "config.toml").exists(),
            "special_workspace_nodes_denied": not os.path.lexists(
                workspace / "control-link"
            )
            and not os.path.lexists(workspace / "generated-fifo"),
            "network_attempt_marked": marker.stat().st_size > 0,
        }
        if not all(checks.values()):
            raise BenchmarkError(
                f"condition {condition} command sandbox canary failed: {checks}; "
                f"output={completed.stdout[-2000:]}"
            )
        return {
            "condition": condition,
            "checks": checks,
            "returncode": completed.returncode,
            "output_sha256": sha256_bytes(completed.stdout.encode("utf-8")),
            "network_marker_sha256": sha256_file(marker),
        }


def _install_once(
    args: argparse.Namespace,
    deployment_root: Path,
    owned_root_identity: tuple[int, int],
    published_root: Path,
) -> Path:
    os.umask(0o077)
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="installer entry"
    )
    manifest, config = verify_manifest()
    if sys.version_info < (3, 11):
        raise BenchmarkError("Titan requires Python 3.11 or newer")
    for name in (
        "git",
        "cc",
        "bwrap",
        "pdftotext",
        "elan",
        "lake",
        "systemd-run",
        "loginctl",
        "rg",
        "time",
    ):
        command_path(name)
    if command_path("rg") != Path("/usr/bin/rg"):
        raise BenchmarkError("Titan requires ripgrep at /usr/bin/rg for the L sandbox")
    if command_path("time") != Path("/usr/bin/time"):
        raise BenchmarkError("Titan requires GNU time at /usr/bin/time")
    if "GNU Time" not in run(["/usr/bin/time", "--version"]):
        raise BenchmarkError("/usr/bin/time is not GNU time")
    linger = run(
        ["loginctl", "show-user", str(os.getuid()), "--property=Linger", "--value"]
    )
    if linger != "yes":
        raise BenchmarkError("Titan requires user-manager lingering for long benchmark runs")
    codex = Path(args.codex_binary).expanduser().resolve() if args.codex_binary else command_path("codex")
    auth_file = Path(args.auth_file).expanduser().resolve()
    if not auth_file.is_file():
        raise BenchmarkError(f"Codex auth file is missing: {auth_file}")

    def published(path: Path) -> Path:
        return published_root / path.relative_to(deployment_root)
    release_commit = run(["git", "rev-parse", "HEAD"], cwd=REPOSITORY_ROOT)
    release_branch = run(["git", "branch", "--show-current"], cwd=REPOSITORY_ROOT)
    if release_branch != "formalization_benchmark":
        raise BenchmarkError(
            f"setup must run from formalization_benchmark, not {release_branch or 'detached HEAD'}"
        )
    if run(["git", "status", "--porcelain"], cwd=REPOSITORY_ROOT):
        raise BenchmarkError("setup refuses a dirty release checkout")
    base_commit = manifest.get("base_commit")
    if base_commit != EXPECTED_BASE_COMMIT:
        raise BenchmarkError("release manifest names an unexpected benchmark base")
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base_commit, release_commit],
        cwd=REPOSITORY_ROOT,
        check=False,
    )
    if ancestry.returncode != 0:
        raise BenchmarkError("release branch is not descended from the frozen benchmark base")

    release_root = deployment_root / "release"
    run(
        [
            "git",
            "clone",
            "--no-hardlinks",
            "--no-checkout",
            str(REPOSITORY_ROOT),
            str(release_root),
        ]
    )
    run(["git", "checkout", "--detach", release_commit], cwd=release_root)
    if run(["git", "rev-parse", "HEAD"], cwd=release_root) != release_commit:
        raise BenchmarkError("frozen release checkout resolved to the wrong commit")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=release_root):
        raise BenchmarkError("frozen release checkout is not clean")
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="release checkout"
    )
    shutil.rmtree(release_root / ".git")
    if any(release_root.rglob("*.pyc")) or any(
        path.name == "__pycache__" for path in release_root.rglob("*")
    ):
        raise BenchmarkError("frozen release unexpectedly contains Python bytecode")
    frozen_benchmark_root = release_root / "paper_bencmark" / "formalization_benchmark"
    frozen_runner = frozen_benchmark_root / "tools" / "titan_envelope.py"
    if not frozen_runner.is_file():
        raise BenchmarkError("frozen release is missing the benchmark runner")
    pdf_root = deployment_root / "private" / "pdfs"
    pdf_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    private_auth_file = deployment_root / "private" / "codex-auth.json"
    write_bytes_atomic(
        private_auth_file,
        stable_regular_bytes(auth_file, maximum_bytes=4 * 1024 * 1024),
        mode=0o600,
    )
    source_pdf_root = Path(args.pdf_source_dir).expanduser().resolve()
    for task_id in config["task_ids"]:
        paper = task_record(manifest, task_id)["source_pdf"]
        source = source_pdf_root / paper["path_basename"]
        if not source.is_file() or sha256_file(source) != paper["sha256"]:
            raise BenchmarkError(f"private PDF failed its frozen hash: {source}")
        destination = pdf_root / source.name
        shutil.copyfile(source, destination)
        destination.chmod(0o400)
        if sha256_file(destination) != paper["sha256"]:
            raise BenchmarkError(f"copied PDF failed verification: {destination}")

    common_project = deployment_root / "runtime" / "common-project"
    common_project.mkdir(parents=True, exist_ok=True)
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(release_root / name, common_project / name)
    run(["elan", "toolchain", "install", FROZEN_TOOLCHAIN])
    toolchain_root = find_toolchain_root(cwd=common_project)
    run(["lake", "update"], cwd=common_project)
    run(["lake", "exe", "cache", "get"], cwd=common_project)
    packages_root = common_project / ".lake" / "packages"
    if not (packages_root / "mathlib" / ".lake" / "build" / "lib" / "lean").is_dir():
        raise BenchmarkError("Mathlib compiled cache was not prepared")

    runtime_record = {
        "schema_version": "formalization-runtime-snapshot-1",
        "created_at_utc": utc_now(),
        "lean_toolchain": FROZEN_TOOLCHAIN,
        "mathlib_commit": config["mathlib_commit"],
        "toolchain": tree_manifest(toolchain_root),
        "packages": tree_manifest(packages_root),
        "condition_n_treatment_absence": treatment_free_runtime_manifest(
            {"packages": packages_root, "toolchain": toolchain_root}
        ),
    }
    runtime_record_path = deployment_root / "runtime" / "snapshot.json"
    write_json_atomic(runtime_record_path, runtime_record, mode=0o400)

    library_root = deployment_root / "runtime" / "library"
    with tempfile.TemporaryDirectory(prefix="highambench-library-") as temporary:
        checkout = Path(temporary) / "checkout"
        run(["git", "clone", "--no-checkout", str(REPOSITORY_ROOT), str(checkout)])
        run(["git", "checkout", "--detach", FROZEN_LIBRARY_COMMIT], cwd=checkout)
        actual_commit = run(["git", "rev-parse", "HEAD"], cwd=checkout)
        if actual_commit != FROZEN_LIBRARY_COMMIT:
            raise BenchmarkError("NumStability checkout resolved to the wrong commit")
        run(["lake", "update"], cwd=checkout)
        run(["lake", "exe", "cache", "get"], cwd=checkout)
        build_root = library_root / "build"
        build_runner = frozen_benchmark_root / "tools" / "measure_library_build.py"
        if not build_runner.is_file() or build_runner.is_symlink():
            raise BenchmarkError("frozen release is missing the library build measurer")
        build_service_environment = measured_build_service_environment(deployment_root)
        run(
            measured_build_command(
                systemd_run=command_path("systemd-run"),
                build_runner=build_runner,
                checkout=checkout,
                artifact_root=build_root,
                toolchain_root=toolchain_root,
                expected_commit=FROZEN_LIBRARY_COMMIT,
                mathlib_commit=str(config["mathlib_commit"]),
                lean_toolchain=FROZEN_TOOLCHAIN,
                service_environment=build_service_environment,
            ),
            cwd=checkout,
        )
        build_record_path = build_root / "build-record.json"
        if not build_record_path.is_file() or build_record_path.is_symlink():
            raise BenchmarkError("measured NumStability build record is missing")
        try:
            build_record = json.loads(
                stable_regular_bytes(build_record_path).decode("utf-8")
            )
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise BenchmarkError("measured NumStability build record is malformed") from error
        if not isinstance(build_record, dict):
            raise BenchmarkError("measured NumStability build record is not an object")
        validate_build_record(
            build_record,
            expected_source_commit=FROZEN_LIBRARY_COMMIT,
            expected_mathlib_commit=str(config["mathlib_commit"]),
            expected_toolchain=FROZEN_TOOLCHAIN,
            expected_tool_hashes={
                "lake_sha256": sha256_file(toolchain_root / "bin" / "lake"),
                "lean_sha256": sha256_file(toolchain_root / "bin" / "lean"),
                "gnu_time_sha256": sha256_file(Path("/usr/bin/time")),
            },
        )
        generated_root = checkout / ".lake" / "build" / "lib" / "lean"
        expected_generated_tree = {"present": True, **file_tree_fingerprint(generated_root)}
        if build_record.get("generated_output_tree") != expected_generated_tree:
            raise BenchmarkError("measured NumStability build output digest changed")
        expected_generated_olean = {
            "present": True,
            **file_tree_fingerprint(generated_root, suffix=".olean"),
        }
        if build_record.get("generated_olean") != expected_generated_olean:
            raise BenchmarkError("measured NumStability OLean inventory changed")
        source_root = library_root / "source"
        olean_root = library_root / "olean"
        copy_tree_read_only(checkout / "NumStability", source_root / "NumStability")
        shutil.copyfile(checkout / "NumStability.lean", source_root / "NumStability.lean")
        (source_root / "NumStability.lean").chmod(0o400)
        copy_tree_read_only(checkout / ".lake" / "build" / "lib" / "lean", olean_root)
        published_generated_tree = {"present": True, **file_tree_fingerprint(olean_root)}
        if build_record.get("generated_output_tree") != published_generated_tree:
            raise BenchmarkError("published NumStability build output changed during copy")
        published_generated_olean = {
            "present": True,
            **file_tree_fingerprint(olean_root, suffix=".olean"),
        }
        if build_record.get("generated_olean") != published_generated_olean:
            raise BenchmarkError("published NumStability OLean inventory changed during copy")

    make_tree_read_only(library_root / "build")

    library_record = {
        "schema_version": "numstability-formalization-snapshot-1",
        "commit": FROZEN_LIBRARY_COMMIT,
        "created_at_utc": utc_now(),
        "source": tree_manifest(library_root / "source"),
        "olean": tree_manifest(library_root / "olean"),
        "build": tree_manifest(library_root / "build"),
    }
    library_record_path = library_root / "snapshot.json"
    write_json_atomic(library_record_path, library_record, mode=0o400)

    offline_shell = deployment_root / "bin" / "offline-shell"
    offline_shell.parent.mkdir(parents=True, exist_ok=True)
    run(
        [
            str(command_path("cc")),
            "-std=c11",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-o",
            str(offline_shell),
            str(
                release_root
                / "paper_bencmark"
                / "highambench"
                / "tools"
                / "offline_shell.c"
            ),
        ]
    )
    offline_shell.chmod(0o500)

    visible_system_runtime_path = deployment_root / "runtime" / "visible-system.json"
    write_json_atomic(
        visible_system_runtime_path,
        visible_system_runtime_manifest(),
        mode=0o400,
    )

    deployment_record = deployment_root / "deployment.json"
    run_root = deployment_root / "runs"
    run_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    record = {
        "schema_version": "formalization-deployment-1",
        "created_at_utc": utc_now(),
        "release_commit": release_commit,
        "release_branch": release_branch,
        "release_root": str(published(release_root)),
        "release_manifest_sha256": sha256_file(frozen_benchmark_root / "manifest.json"),
        "run_root": str(published(run_root)),
        "pdf_root": str(published(pdf_root)),
        "codex_binary": str(codex),
        "codex_binary_sha256": sha256_file(codex),
        "codex_version": run([str(codex), "--version"]),
        "auth_file": str(published(private_auth_file)),
        "bwrap_binary": str(command_path("bwrap")),
        "offline_shell": str(published(offline_shell)),
        "toolchain_root": str(toolchain_root),
        "packages_root": str(published(packages_root)),
        "library_source": str(published(library_root / "source" / "NumStability")),
        "library_olean": str(published(library_root / "olean")),
        "library_snapshot_record": str(published(library_record_path)),
        "library_snapshot_record_sha256": sha256_file(library_record_path),
        "library_build_record": str(published(library_root / "build" / "build-record.json")),
        "library_build_record_sha256": sha256_file(
            library_root / "build" / "build-record.json"
        ),
        "runtime_snapshot_record": str(published(runtime_record_path)),
        "runtime_snapshot_record_sha256": sha256_file(runtime_record_path),
        "visible_system_runtime_record": str(published(visible_system_runtime_path)),
        "visible_system_runtime_record_sha256": sha256_file(
            visible_system_runtime_path
        ),
        "bwrap_binary_sha256": sha256_file(command_path("bwrap")),
        "offline_shell_sha256": sha256_file(offline_shell),
        "hardware_identity": frozen_hardware_identity(
            snapshot_hardware(strict=False), affinity_cpus=host_cpu_selection()
        ),
        "strict_hardware": True,
    }
    deployed = Deployment(
        path=deployment_record,
        run_root=run_root,
        pdf_root=pdf_root,
        codex_binary=codex,
        auth_file=private_auth_file,
        bwrap_binary=command_path("bwrap"),
        offline_shell=offline_shell,
        toolchain_root=toolchain_root,
        packages_root=packages_root,
        library_source=library_root / "source" / "NumStability",
        library_olean=library_root / "olean",
        library_snapshot_record=library_record_path,
        runtime_snapshot_record=runtime_record_path,
        strict_hardware=True,
    )
    command_canary = {
        "schema_version": "formalization-command-sandbox-canary-1",
        "provider_calls": 0,
        "conditions": [
            run_command_sandbox_canary(deployed, "N"),
            run_command_sandbox_canary(deployed, "L"),
        ],
    }
    command_canary_path = deployment_root / "command-sandbox-canary.json"
    write_json_atomic(command_canary_path, command_canary, mode=0o400)
    canary = run_runtime_canaries(deployed)
    canary_path = deployment_root / "runtime-canary.json"
    write_json_atomic(canary_path, canary, mode=0o400)
    codex_preflight: dict[str, Any] = {
        "schema_version": "formalization-codex-model-preflights-1",
        "provider_calls": 0,
        "roles": {},
    }
    for role, model_key, effort_key, writable in (
        (
            "formalizer",
            "formalizer_model",
            "formalizer_reasoning_effort",
            True,
        ),
        ("auditor", "audit_model", "audit_reasoning_effort", False),
    ):
        with tempfile.TemporaryDirectory(
            prefix=f"formalization-codex-{role}-preflight-", dir=deployment_root
        ) as temporary:
            preflight_root = Path(temporary)
            preflight_workspace = preflight_root / "workspace"
            preflight_workspace.mkdir()
            preflight_driver = CodexDriver(
                codex_binary=codex,
                model=str(config[model_key]),
                reasoning_effort=str(config[effort_key]),
                state_root=None,
                auth_file=private_auth_file,
                bwrap_binary=deployed.bwrap_binary,
                offline_shell=offline_shell,
                toolchain_root=toolchain_root,
                packages_root=packages_root,
                workspace_writable=writable,
            )
            try:
                role_record = preflight_driver.preflight(
                    workspace=preflight_workspace,
                    artifact_dir=preflight_root / "artifacts",
                    timeout_seconds=60,
                )
            finally:
                preflight_driver.close()
            if role_record.get("provider_call_permitted") is not False:
                raise BenchmarkError(f"{role} compatibility preflight was not provider-free")
            codex_preflight["roles"][role] = role_record
    codex_preflight_path = deployment_root / "codex-preflight.json"
    write_json_atomic(codex_preflight_path, codex_preflight, mode=0o400)
    record.update(
        {
            "runtime_canary_record": str(published(canary_path)),
            "runtime_canary_record_sha256": sha256_file(canary_path),
            "command_sandbox_canary_record": str(published(command_canary_path)),
            "command_sandbox_canary_record_sha256": sha256_file(
                command_canary_path
            ),
            "codex_preflight_record": str(published(codex_preflight_path)),
            "codex_preflight_record_sha256": sha256_file(codex_preflight_path),
        }
    )
    write_json_atomic(deployment_record, record, mode=0o600)
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="deployment record publication"
    )
    deployment_record.chmod(0o400)
    deployment_record_sha256 = sha256_file(deployment_record)
    make_tree_read_only(release_root)
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="staged deployment completion"
    )
    if deployment_record_sha256 != sha256_file(deployment_record):
        raise BenchmarkError("staged deployment record changed before publication")
    return deployment_record


INSTALL_TRANSACTION = "install-transaction.json"
INSTALL_TRANSACTION_SCHEMA = "formalization-install-transaction-1"


def _transaction_record(
    *,
    status: str,
    deployment_root: Path,
    launcher: Path,
    deployment_record_sha256: str | None = None,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "schema_version": INSTALL_TRANSACTION_SCHEMA,
        "status": status,
        "deployment_root": str(deployment_root),
        "launcher": str(launcher),
        "release_manifest_sha256": sha256_file(ROOT / "manifest.json"),
        "updated_at_utc": utc_now(),
    }
    if deployment_record_sha256 is not None:
        record["deployment_record_sha256"] = deployment_record_sha256
    return record


def _load_transaction(
    root: Path, *, deployment_root: Path, launcher: Path
) -> dict[str, Any]:
    path = root / INSTALL_TRANSACTION
    if not path.is_file() or path.is_symlink():
        raise BenchmarkError("deployment has no safe installation transaction record")
    try:
        record = json.loads(stable_regular_bytes(path).decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkError("deployment installation transaction is malformed") from error
    if (
        not isinstance(record, dict)
        or record.get("schema_version") != INSTALL_TRANSACTION_SCHEMA
        or Path(str(record.get("deployment_root", ""))).resolve() != deployment_root
        or Path(str(record.get("launcher", ""))).resolve() != launcher
        or record.get("release_manifest_sha256")
        != sha256_file(ROOT / "manifest.json")
        or record.get("status")
        not in {"BUILDING", "READY_TO_PUBLISH", "FINALIZING", "COMPLETE"}
    ):
        raise BenchmarkError("deployment installation transaction is malformed")
    return record


def _finalize_install(
    args: argparse.Namespace, deployment_root: Path, launcher: Path
) -> Path:
    transaction_path = deployment_root / INSTALL_TRANSACTION
    transaction = _load_transaction(
        deployment_root, deployment_root=deployment_root, launcher=launcher
    )
    if transaction["status"] == "COMPLETE":
        raise BenchmarkError("formalization benchmark is already installed")
    if transaction["status"] not in {"READY_TO_PUBLISH", "FINALIZING"}:
        raise BenchmarkError("deployment is not ready for installation finalization")
    deployment_record = deployment_root / "deployment.json"
    expected_deployment_hash = transaction.get("deployment_record_sha256")
    if (
        not isinstance(expected_deployment_hash, str)
        or len(expected_deployment_hash) != 64
        or not deployment_record.is_file()
        or deployment_record.is_symlink()
        or sha256_file(deployment_record) != expected_deployment_hash
    ):
        raise BenchmarkError("published deployment record failed authentication")
    transaction["status"] = "FINALIZING"
    transaction["updated_at_utc"] = utc_now()
    write_json_atomic(transaction_path, transaction, mode=0o600)

    frozen_runner = (
        deployment_root
        / "release"
        / "paper_bencmark"
        / "formalization_benchmark"
        / "tools"
        / "titan_envelope.py"
    )
    if not frozen_runner.is_file() or frozen_runner.is_symlink():
        raise BenchmarkError("published deployment is missing its frozen runner")
    environment = os.environ.copy()
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"] = str(deployment_record)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"] = (
        expected_deployment_hash
    )
    completed = run_bounded_command(
        isolated_runner_command(
            frozen_runner,
            "doctor",
            "--task-id",
            "P01-T2",
        ),
        cwd=deployment_root,
        environment=environment,
        timeout_seconds=1800,
        maximum_output_bytes=8 * 1024 * 1024,
    )
    doctor_output = completed["output"].encode("utf-8")
    if completed["timed_out"]:
        raise BenchmarkError("post-install doctor exceeded 1800 seconds")
    if completed["output_limit_exceeded"]:
        raise BenchmarkError("post-install doctor output exceeded 8 MiB")
    if completed["returncode"] != 0:
        rendered = doctor_output[-8000:].decode("utf-8", errors="replace")
        raise BenchmarkError(f"post-install doctor failed:\n{rendered}")
    write_bytes_atomic(
        deployment_root / "last-doctor.json", doctor_output, mode=0o400
    )

    expected_launcher = launcher_bytes(
        deployment_record, expected_deployment_hash, frozen_runner
    )
    if launcher.exists() or launcher.is_symlink():
        if (
            launcher.is_symlink()
            or not launcher.is_file()
            or stable_regular_bytes(launcher) != expected_launcher
        ):
            raise BenchmarkError("existing launcher does not match pending deployment")
    else:
        write_launcher(
            launcher, deployment_record, expected_deployment_hash, frozen_runner
        )

    skill_source = (
        deployment_root
        / "release"
        / ".codex"
        / "skills"
        / "run-highambench-experiments"
    )
    skill_destination = (
        Path.home() / ".codex" / "skills" / "run-highambench-experiments"
    )
    install_skill_atomically(skill_source, skill_destination)
    transaction["status"] = "COMPLETE"
    transaction["completed_at_utc"] = utc_now()
    transaction["updated_at_utc"] = transaction["completed_at_utc"]
    write_json_atomic(transaction_path, transaction, mode=0o400)
    return deployment_record


def install(args: argparse.Namespace) -> Path:
    """Build beside the canonical root, atomically publish, and resume safely."""

    requested_root = Path(args.deployment_root).expanduser()
    if requested_root.is_symlink():
        raise BenchmarkError("deployment root may not be a symlink")
    deployment_root = requested_root.resolve()
    launcher = Path(args.launcher).expanduser().resolve()
    deployment_root.parent.mkdir(parents=True, exist_ok=True, mode=0o700)

    if os.path.lexists(deployment_root):
        if deployment_root.is_symlink() or not deployment_root.is_dir():
            raise BenchmarkError("deployment root exists and is unsafe")
        return _finalize_install(args, deployment_root, launcher)

    staging_prefix = f".{deployment_root.name}.install-"
    ready_staging: Path | None = None
    for candidate in sorted(deployment_root.parent.glob(staging_prefix + "*")):
        if candidate.is_symlink() or not candidate.is_dir():
            raise BenchmarkError(f"unsafe abandoned deployment transaction: {candidate}")
        try:
            transaction = _load_transaction(
                candidate, deployment_root=deployment_root, launcher=launcher
            )
        except (BenchmarkError, OSError, json.JSONDecodeError):
            abandoned = deployment_root.parent / (
                f".{deployment_root.name}.abandoned-{os.urandom(8).hex()}"
            )
            os.rename(candidate, abandoned)
            fsync_directory(deployment_root.parent)
            continue
        if transaction["status"] == "READY_TO_PUBLISH":
            if ready_staging is not None:
                raise BenchmarkError("multiple ready deployment transactions exist")
            ready_staging = candidate
        else:
            abandoned = deployment_root.parent / (
                f".{deployment_root.name}.abandoned-{os.urandom(8).hex()}"
            )
            os.rename(candidate, abandoned)
            fsync_directory(deployment_root.parent)
    if ready_staging is not None:
        os.rename(ready_staging, deployment_root)
        fsync_directory(deployment_root.parent)
        return _finalize_install(args, deployment_root, launcher)

    if launcher.exists() or launcher.is_symlink():
        raise BenchmarkError(
            "launcher exists without a resumable deployment; refusing to overwrite it"
        )
    staging_root = Path(
        tempfile.mkdtemp(prefix=staging_prefix, dir=str(deployment_root.parent))
    )
    os.chmod(staging_root, 0o700)
    owned_root_identity = directory_identity(staging_root)
    write_json_atomic(
        staging_root / INSTALL_TRANSACTION,
        _transaction_record(
            status="BUILDING",
            deployment_root=deployment_root,
            launcher=launcher,
        ),
        mode=0o600,
    )
    try:
        staged_record = _install_once(
            args,
            staging_root,
            owned_root_identity,
            deployment_root,
        )
        deployment_hash = sha256_file(staged_record)
        write_json_atomic(
            staging_root / INSTALL_TRANSACTION,
            _transaction_record(
                status="READY_TO_PUBLISH",
                deployment_root=deployment_root,
                launcher=launcher,
                deployment_record_sha256=deployment_hash,
            ),
            mode=0o600,
        )
        assert_directory_identity(
            staging_root, owned_root_identity, phase="atomic publication"
        )
        os.rename(staging_root, deployment_root)
        fsync_directory(deployment_root.parent)
        return _finalize_install(args, deployment_root, launcher)
    except BaseException as install_error:
        # Before publication, remove only the inode created by this invocation.
        # After publication, retain the authenticated FINALIZING transaction so
        # the next invocation can complete it without rebuilding.
        if os.path.lexists(staging_root):
            try:
                remove_owned_deployment_root(staging_root, owned_root_identity)
            except BaseException as cleanup_error:
                raise BenchmarkError(
                    "setup failed and staging cleanup could not be authenticated: "
                    f"{cleanup_error}"
                ) from install_error
        raise


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf-source-dir", required=True)
    parser.add_argument(
        "--deployment-root",
        default=str(Path.home() / ".local" / "share" / "highambench-formalization"),
    )
    parser.add_argument("--auth-file", default=str(Path.home() / ".codex" / "auth.json"))
    parser.add_argument("--codex-binary")
    parser.add_argument(
        "--launcher", default=str(Path.home() / ".local" / "bin" / "run-highambench-formalization")
    )
    return parser


if __name__ == "__main__":
    try:
        output = install(make_parser().parse_args())
    except (BenchmarkError, OSError, subprocess.SubprocessError) as error:
        print(f"Titan setup error: {error}", file=sys.stderr)
        raise SystemExit(2)
    print(output)
