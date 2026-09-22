"""Enter Titan's existing fixed resource envelope for Pilot-18 model calls."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys

from common import BenchmarkError
from hardware import snapshot_hardware, systemd_service_envelope_prefix
from titan_envelope import COMMAND_CGROUP_VARIABLE, MARKER, prepare_command_cgroup


def launch_or_activate(script: Path) -> int | None:
    """Return child exit code when launching; otherwise activate this service."""
    if os.environ.get(MARKER) != "1":
        systemd_run = shutil.which("systemd-run")
        if systemd_run is None:
            raise BenchmarkError("systemd-run is required for Pilot 18 Titan calls")
        command = [
            *systemd_service_envelope_prefix(systemd_run),
            "--working-directory", str(Path.cwd().resolve()),
            "--setenv", f"{MARKER}=1",
            sys.executable, str(script.resolve()), *sys.argv[1:],
        ]
        return subprocess.run(command, check=False).returncode
    if os.environ.get(COMMAND_CGROUP_VARIABLE):
        raise BenchmarkError("Pilot 18 command cgroup was already set before activation")
    os.environ[COMMAND_CGROUP_VARIABLE] = str(prepare_command_cgroup())
    snapshot_hardware(strict=True)
    return None
