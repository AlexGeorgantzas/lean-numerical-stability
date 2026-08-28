#!/usr/bin/env python3
"""Print a zero-provider HighamBench host inventory for an allocated node."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys


PROJECT_ROOT = Path("/u501/m2fetrat/MyCodes/lean-fp-analysis-main")
BENCHMARK_ROOT = PROJECT_ROOT / "paper_bencmark" / "highambench"
sys.path.insert(0, str(BENCHMARK_ROOT / "tools"))

import run_matrix  # type: ignore  # noqa: E402
from common import read_json  # type: ignore  # noqa: E402


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    environment = read_json(BENCHMARK_ROOT / "metadata" / "environment.json")
    frozen_provider = environment["provider_token_gate"]
    actual_provider = run_matrix.provider_token_gate_environment_record(BENCHMARK_ROOT)
    python_path = Path(sys.executable).resolve()
    bwrap_path = Path("/usr/bin/bwrap").resolve()
    actual_host = {
        "kernel": f"{platform.system()} {platform.release()} {platform.machine()}",
        "virtualization": subprocess.check_output(
            ["systemd-detect-virt", "--container"], text=True
        ).strip().splitlines()[-1].upper(),
        **run_matrix._cpu_identity(),
        **run_matrix._allocated_cpu_topology(),
        "visible_memory_bytes": run_matrix._visible_memory_bytes(),
        "allocation_memory_limit_bytes": run_matrix._cgroup_memory_limit_bytes(),
        **run_matrix._slurm_allocation_shape(),
    }
    payload = {
        "job_id": os.environ.get("SLURM_JOB_ID"),
        "node_list": os.environ.get("SLURM_JOB_NODELIST"),
        "partition": os.environ.get("SLURM_JOB_PARTITION"),
        "python": {
            "path": str(python_path),
            "version": platform.python_version(),
            "sha256": sha256(python_path),
        },
        "bubblewrap": {
            "path": str(bwrap_path),
            "sha256": sha256(bwrap_path),
        },
        "actual_host_class": actual_host,
        "frozen_host_class": environment["host_class"],
        "host_class_matches": actual_host == environment["host_class"],
        "actual_provider_token_gate": actual_provider,
        "frozen_provider_token_gate": frozen_provider,
        "provider_token_gate_matches": actual_provider == frozen_provider,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
