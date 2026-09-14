from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

from common import BenchmarkError
from hardware import EXPECTED_MEMORY_BYTES, EXPECTED_TASKS_MAX, host_cpu_allowlist


MARKER = "HIGHAMBENCH_TITAN_ENVELOPE"
COMMAND_CGROUP_VARIABLE = "HIGHAMBENCH_COMMAND_CGROUP_PROCS"
DEPLOYMENT_VARIABLE = "HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"
DEPLOYMENT_DIGEST_VARIABLE = "HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"
COMMAND_MEMORY_BYTES = 24 * 1024 * 1024 * 1024
COMMAND_TASKS_MAX = 384
CONTROL_MEMORY_LOW_BYTES = 8 * 1024 * 1024 * 1024
CONTROL_CPU_WEIGHT = 10_000
COMMAND_CPU_WEIGHT = 100


def _write_cgroup_value(path: Path, value: str) -> None:
    try:
        path.write_text(value, encoding="ascii")
    except OSError as error:
        raise BenchmarkError(f"cannot configure delegated command cgroup {path.name}") from error


def prepare_command_cgroup(
    *, proc_cgroup: Path = Path("/proc/self/cgroup"), cgroup_root: Path = Path("/sys/fs/cgroup")
) -> Path:
    """Reserve the trusted control plane and bound every generated command tree."""

    try:
        unified = [
            line.split("::", 1)[1]
            for line in proc_cgroup.read_text(encoding="ascii").splitlines()
            if "::" in line
        ]
    except OSError as error:
        raise BenchmarkError("cannot read the current cgroup-v2 identity") from error
    if len(unified) != 1:
        raise BenchmarkError("a unique unified cgroup-v2 identity is required")
    relative = Path(unified[0].lstrip("/"))
    if ".." in relative.parts:
        raise BenchmarkError("current cgroup path is unsafe")
    scope = (cgroup_root / relative).resolve()
    try:
        scope.relative_to(cgroup_root.resolve())
    except ValueError as error:
        raise BenchmarkError("current cgroup escapes cgroup-v2 root") from error
    controllers = set((scope / "cgroup.controllers").read_text(encoding="ascii").split())
    if not {"cpu", "memory", "pids"}.issubset(controllers):
        raise BenchmarkError("systemd did not delegate cpu, memory, and pids controllers")
    control = scope / "highambench-control"
    commands = scope / "highambench-commands"
    control.mkdir(exist_ok=False)
    commands.mkdir(exist_ok=False)
    _write_cgroup_value(control / "cgroup.procs", str(os.getpid()))
    _write_cgroup_value(scope / "cgroup.subtree_control", "+cpu +memory +pids")
    _write_cgroup_value(control / "memory.max", str(EXPECTED_MEMORY_BYTES))
    _write_cgroup_value(control / "memory.swap.max", "0")
    _write_cgroup_value(control / "pids.max", str(EXPECTED_TASKS_MAX))
    _write_cgroup_value(control / "memory.low", str(CONTROL_MEMORY_LOW_BYTES))
    _write_cgroup_value(control / "cpu.weight", str(CONTROL_CPU_WEIGHT))
    _write_cgroup_value(commands / "memory.max", str(COMMAND_MEMORY_BYTES))
    _write_cgroup_value(commands / "memory.swap.max", "0")
    _write_cgroup_value(commands / "pids.max", str(COMMAND_TASKS_MAX))
    _write_cgroup_value(commands / "cpu.weight", str(COMMAND_CPU_WEIGHT))
    return commands / "cgroup.procs"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Enter the fixed Titan cgroup and invoke the benchmark controller."
    )
    parser.add_argument("controller_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.controller_args:
        parser.error("a run_benchmark.py command is required")
    controller = Path(__file__).with_name("run_benchmark.py")
    if os.environ.get(MARKER) == "1":
        command_cgroup = prepare_command_cgroup()
        os.environ[COMMAND_CGROUP_VARIABLE] = str(command_cgroup)
        os.execv(sys.executable, [sys.executable, str(controller), *args.controller_args])
    systemd_run = shutil.which("systemd-run")
    if systemd_run is None:
        raise BenchmarkError("systemd-run is required to enforce the Titan envelope")
    cpus = host_cpu_allowlist()
    deployment = os.environ.get(DEPLOYMENT_VARIABLE)
    deployment_digest = os.environ.get(DEPLOYMENT_DIGEST_VARIABLE)
    if not deployment or not deployment_digest:
        raise BenchmarkError(
            "the deployment path and digest are required by the installed Titan launcher"
        )
    command = [
        systemd_run,
        "--user",
        "--scope",
        "--quiet",
        "--wait",
        "--collect",
        "--property",
        f"AllowedCPUs={cpus}",
        "--property",
        f"MemoryMax={EXPECTED_MEMORY_BYTES}",
        "--property",
        "MemorySwapMax=0",
        "--property",
        f"TasksMax={EXPECTED_TASKS_MAX}",
        "--property",
        "Delegate=yes",
        "--setenv",
        f"{MARKER}=1",
        "--setenv",
        f"{DEPLOYMENT_VARIABLE}={deployment}",
        "--setenv",
        f"{DEPLOYMENT_DIGEST_VARIABLE}={deployment_digest}",
        sys.executable,
        str(Path(__file__).resolve()),
        *args.controller_args,
    ]
    return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BenchmarkError as error:
        print(f"Titan envelope error: {error}", file=sys.stderr)
        raise SystemExit(2)
