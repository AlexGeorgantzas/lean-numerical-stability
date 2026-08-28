#!/usr/bin/env bash
# Read-only HighamBench pair-node compatibility probe. No provider calls.
#SBATCH --job-name=highambench-node-probe
#SBATCH --account=kfountou_group
#SBATCH --partition=ALL
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --sockets-per-node=1
#SBATCH --cores-per-socket=2
#SBATCH --threads-per-core=2
#SBATCH --mem=32G
#SBATCH --gres=gpu:0
#SBATCH --time=00:05:00
#SBATCH --chdir=/u501/m2fetrat/MyCodes/lean-fp-analysis-main
#SBATCH --output=/u501/m2fetrat/MyCodes/lean-fp-analysis-main/paper_bencmark/scratch_pad/slurm-%x-%N-%j.log

set -Eeuo pipefail
umask 077
export PYTHONNOUSERSITE=1
export TZ=UTC

readonly PROJECT_ROOT=/u501/m2fetrat/MyCodes/lean-fp-analysis-main
readonly SCRATCH_ROOT="${PROJECT_ROOT}/paper_bencmark/scratch_pad"
readonly PYTHON=/usr/bin/python3.10

"$PYTHON" - "$PROJECT_ROOT" "$SCRATCH_ROOT" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

project = Path(sys.argv[1]).resolve()
scratch = Path(sys.argv[2]).resolve()

def sha(path_text: str):
    path = Path(path_text)
    if path.is_symlink() or not path.is_file():
        return None
    return {
        "path": path_text,
        "bytes": path.stat().st_size,
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }

def command(*argv: str):
    completed = subprocess.run(
        argv,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env={**os.environ, "LC_ALL": "C"},
    )
    return completed.stdout.strip()

paths = [
    "/usr/bin/python3.10",
    "/usr/bin/bwrap",
    "/usr/bin/curl",
    "/usr/lib/ssl/cert.pem",
    "/etc/ssl/certs/ca-certificates.crt",
    "/etc/hosts",
    "/etc/resolv.conf",
    str(scratch / "highambench_environment/codex-0.146.0-alpha.9.2"),
    str(scratch / "highambench_environment/offline-shell"),
]

payload = {
    "kind": "highambench_pair_node_probe_v1",
    "hostname": platform.node(),
    "platform": platform.platform(),
    "uname": list(platform.uname()),
    "python_version": platform.python_version(),
    "python_executable": str(Path(sys.executable).resolve()),
    "slurm": {
        key: os.environ.get(key)
        for key in (
            "SLURM_JOB_ID",
            "SLURM_JOB_NODELIST",
            "SLURM_CPUS_PER_TASK",
            "SLURM_MEM_PER_NODE",
            "SLURM_JOB_CPUS_PER_NODE",
            "SLURM_JOB_PARTITION",
        )
    },
    "affinity": sorted(os.sched_getaffinity(0)),
    "lscpu_json": json.loads(command("/usr/bin/lscpu", "--json", "--bytes")),
    "files": [item for item in (sha(path) for path in paths) if item is not None],
    "python_ldd": command("/usr/bin/ldd", "/usr/bin/python3.10"),
    "mount_namespace": command("/usr/bin/readlink", "/proc/self/ns/mnt"),
}
print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
PY
