"""Prospective isolated 8-CPU/24-GiB Titan service for one Pilot-20 lane.

This only supplies the resource boundary. Admission of a corpus, a frozen
campaign, and concurrent benchmark dispatch are separate gates.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys

from common import BenchmarkError
from design20_lanes import LANE_CPUS, LANE_MEMORY_BYTES
from hardware import (
    HARDWARE_PROFILE_ENV,
    snapshot_hardware,
    systemd_service_envelope_prefix,
)
from titan_envelope import COMMAND_CGROUP_VARIABLE, MARKER, prepare_command_cgroup


COMMAND_MEMORY_BYTES = 18 * 1024 ** 3
CONTROL_MEMORY_LOW_BYTES = 4 * 1024 ** 3


def _cpu_list(cpus: tuple[int, ...]) -> str:
    ranges: list[str] = []
    start = previous = cpus[0]
    for cpu in cpus[1:]:
        if cpu == previous + 1:
            previous = cpu
            continue
        ranges.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = cpu
    ranges.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(ranges)


def launch_or_activate(script: Path, *, lane: str) -> int | None:
    if lane not in LANE_CPUS:
        raise BenchmarkError("unknown Pilot 20 lane")
    profile = f"pilot20-lane-{lane}"
    if os.environ.get(MARKER) != "1":
        systemd_run = shutil.which("systemd-run")
        if systemd_run is None:
            raise BenchmarkError("systemd-run is required for Pilot 20 Titan lanes")
        command = [
            *systemd_service_envelope_prefix(
                systemd_run,
                cpus=_cpu_list(LANE_CPUS[lane]),
                memory_bytes=LANE_MEMORY_BYTES,
            ),
            "--working-directory", str(Path.cwd().resolve()),
            "--setenv", f"{MARKER}=1",
            "--setenv", f"{HARDWARE_PROFILE_ENV}={profile}",
            sys.executable, str(script.resolve()), *sys.argv[1:],
        ]
        return subprocess.run(command, check=False).returncode
    if os.environ.get(HARDWARE_PROFILE_ENV) != profile:
        raise BenchmarkError("Pilot 20 lane marker/profile mismatch")
    if os.environ.get(COMMAND_CGROUP_VARIABLE):
        raise BenchmarkError("Pilot 20 command cgroup already set")
    os.environ[COMMAND_CGROUP_VARIABLE] = str(prepare_command_cgroup(
        outer_memory_bytes=LANE_MEMORY_BYTES,
        command_memory_bytes=COMMAND_MEMORY_BYTES,
        control_memory_low_bytes=CONTROL_MEMORY_LOW_BYTES,
    ))
    snapshot_hardware(strict=True)
    return None
