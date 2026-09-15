from __future__ import annotations

import errno
import os
import platform
import re
from pathlib import Path
from typing import Any, Mapping

from common import BenchmarkError, sha256_bytes, utc_now


EXPECTED_LOGICAL_CPUS = 8
EXPECTED_MEMORY_BYTES = 32 * 1024 * 1024 * 1024
EXPECTED_TASKS_MAX = 512


def _expand_cpu_list(value: str) -> list[int]:
    result: list[int] = []
    for raw_part in value.strip().split(","):
        part = raw_part.strip()
        if not part:
            continue
        if "-" in part:
            left, right = part.split("-", 1)
            start, stop = int(left), int(right)
            if stop < start:
                raise BenchmarkError(f"invalid CPU range: {part}")
            result.extend(range(start, stop + 1))
        else:
            result.append(int(part))
    return sorted(set(result))


def _cgroup_v2_path() -> Path | None:
    membership = Path("/proc/self/cgroup")
    if not membership.is_file():
        return None
    for line in membership.read_text(encoding="utf-8", errors="replace").splitlines():
        fields = line.split(":", 2)
        if len(fields) == 3 and fields[0] == "0" and fields[1] == "":
            relative = fields[2].lstrip("/")
            return Path("/sys/fs/cgroup") / relative
    return None


def _read_optional(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return None


def _finite_ancestor_limits(cgroup: Path | None, filename: str) -> list[int]:
    if cgroup is None:
        return []
    root = Path("/sys/fs/cgroup").resolve()
    current = cgroup.resolve()
    values: list[int] = []
    while True:
        raw = _read_optional(current / filename)
        if raw is not None and raw.isdigit():
            values.append(int(raw))
        if current == root:
            break
        if root not in current.parents:
            raise BenchmarkError("cgroup path escapes the cgroup v2 root")
        current = current.parent
    return values


def host_cpu_selection() -> list[int]:
    """Return the exact eight CPUs selected for every Titan envelope."""

    if not hasattr(os, "sched_getaffinity"):
        raise BenchmarkError("CPU affinity is unavailable on this host")
    available = sorted(os.sched_getaffinity(0))
    if len(available) < EXPECTED_LOGICAL_CPUS:
        raise BenchmarkError("fewer than eight logical CPUs are available")
    return available[:EXPECTED_LOGICAL_CPUS]


def affinity_mutation_canary(affinity: list[int]) -> dict[str, Any]:
    """Prove that the outer service denies affinity changes for descendants."""

    if not hasattr(os, "sched_setaffinity"):
        return {"attempted": False, "denied": False, "errno": None}
    try:
        # Setting even the unchanged mask invokes sched_setaffinity without
        # perturbing the process if a filter was accidentally omitted.
        os.sched_setaffinity(0, set(affinity))
    except OSError as error:
        return {
            "attempted": True,
            "denied": error.errno in {errno.EPERM, errno.EACCES},
            "errno": error.errno,
        }
    return {"attempted": True, "denied": False, "errno": None}


def frozen_hardware_identity(
    snapshot: Mapping[str, Any], *, affinity_cpus: list[int] | None = None
) -> dict[str, Any]:
    """Select stable host/CPU fields used to admit later benchmark attempts."""

    selected = snapshot.get("affinity_cpus") if affinity_cpus is None else affinity_cpus
    if not isinstance(selected, list) or any(
        isinstance(value, bool) or not isinstance(value, int) for value in selected
    ):
        raise BenchmarkError("hardware identity has an invalid CPU selection")
    model_names = snapshot.get("cpu_model_names")
    if not isinstance(model_names, list) or not model_names or any(
        not isinstance(value, str) or not value for value in model_names
    ):
        raise BenchmarkError("hardware identity has no stable CPU model")
    identity = {
        "schema_version": "formalization-hardware-identity-1",
        "platform": snapshot.get("platform"),
        "machine": snapshot.get("machine"),
        "hostname": snapshot.get("hostname"),
        "affinity_cpus": sorted(selected),
        "cpu_model_names": sorted(model_names),
    }
    for key in ("platform", "machine", "hostname"):
        if not isinstance(identity[key], str) or not identity[key]:
            raise BenchmarkError(f"hardware identity field {key} is missing")
    if len(identity["affinity_cpus"]) != EXPECTED_LOGICAL_CPUS:
        raise BenchmarkError("hardware identity must freeze exactly eight CPUs")
    return identity


def verify_frozen_hardware_identity(
    snapshot: Mapping[str, Any], expected: Any
) -> None:
    """Fail closed when a run no longer uses the setup host and CPU set."""

    if not isinstance(expected, Mapping):
        raise BenchmarkError("deployment has no frozen hardware identity")
    actual = frozen_hardware_identity(snapshot)
    if dict(expected) != actual:
        mismatches = sorted(
            key
            for key in set(actual) | set(expected)
            if actual.get(key) != expected.get(key)
        )
        raise BenchmarkError(
            "hardware identity changed after deployment: " + ", ".join(mismatches)
        )


def snapshot_hardware(*, strict: bool) -> dict[str, Any]:
    affinity = (
        sorted(os.sched_getaffinity(0))
        if hasattr(os, "sched_getaffinity")
        else list(range(os.cpu_count() or 0))
    )
    cgroup = _cgroup_v2_path()
    memory_max_raw = _read_optional(cgroup / "memory.max") if cgroup else None
    cpuset_raw = _read_optional(cgroup / "cpuset.cpus.effective") if cgroup else None
    swap_max_raw = _read_optional(cgroup / "memory.swap.max") if cgroup else None
    pids_max_raw = _read_optional(cgroup / "pids.max") if cgroup else None
    cpuset = _expand_cpu_list(cpuset_raw) if cpuset_raw else []
    memory_max = int(memory_max_raw) if memory_max_raw and memory_max_raw.isdigit() else None
    ancestor_memory_limits = _finite_ancestor_limits(cgroup, "memory.max")
    effective_memory_max = min(ancestor_memory_limits) if ancestor_memory_limits else None
    ancestor_pids_limits = _finite_ancestor_limits(cgroup, "pids.max")
    effective_pids_max = min(ancestor_pids_limits) if ancestor_pids_limits else None
    cpuinfo = _read_optional(Path("/proc/cpuinfo")) or ""
    model_names = sorted(
        {
            line.split(":", 1)[1].strip()
            for line in cpuinfo.splitlines()
            if line.lower().startswith("model name") and ":" in line
        }
    )
    mutation_canary = (
        affinity_mutation_canary(affinity)
        if strict
        else {"attempted": False, "denied": None, "errno": None}
    )
    record = {
        "recorded_at_utc": utc_now(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "hostname": platform.node(),
        "affinity_cpus": affinity,
        "affinity_cpu_count": len(affinity),
        "cgroup_v2_path": str(cgroup) if cgroup else None,
        "cgroup_cpuset_effective": cpuset,
        "cgroup_cpuset_cpu_count": len(cpuset),
        "cgroup_memory_max_bytes": memory_max,
        "cgroup_ancestor_memory_limits_bytes": ancestor_memory_limits,
        "effective_memory_max_bytes": effective_memory_max,
        "cgroup_memory_swap_max": swap_max_raw,
        "cgroup_pids_max": (
            int(pids_max_raw) if pids_max_raw and pids_max_raw.isdigit() else None
        ),
        "cgroup_ancestor_pids_limits": ancestor_pids_limits,
        "effective_pids_max": effective_pids_max,
        "cpu_model_names": model_names,
        "cpuinfo_sha256": sha256_bytes(cpuinfo.encode("utf-8")) if cpuinfo else None,
        "required_logical_cpus": EXPECTED_LOGICAL_CPUS,
        "required_memory_bytes": EXPECTED_MEMORY_BYTES,
        "required_tasks_max": EXPECTED_TASKS_MAX,
        "affinity_mutation_canary": mutation_canary,
        "strict": strict,
    }
    checks = {
        "linux_x86_64": platform.system() == "Linux" and platform.machine() == "x86_64",
        "affinity_exactly_8": len(affinity) == EXPECTED_LOGICAL_CPUS,
        "affinity_mutation_denied": mutation_canary.get("denied") is True,
        "cgroup_v2_present": cgroup is not None,
        "cgroup_cpuset_exactly_8_if_exposed": (
            not cpuset or len(cpuset) == EXPECTED_LOGICAL_CPUS
        ),
        "affinity_matches_cgroup_if_exposed": (
            not cpuset or set(affinity) == set(cpuset)
        ),
        "memory_max_exactly_32_gib": memory_max == EXPECTED_MEMORY_BYTES,
        "effective_memory_exactly_32_gib": effective_memory_max == EXPECTED_MEMORY_BYTES,
        "memory_swap_disabled": swap_max_raw == "0",
        "tasks_max_exactly_512": pids_max_raw == str(EXPECTED_TASKS_MAX),
        "effective_tasks_max_exactly_512": effective_pids_max == EXPECTED_TASKS_MAX,
    }
    record["checks"] = checks
    record["admitted"] = all(checks.values()) if strict else True
    if strict and not record["admitted"]:
        failed = ", ".join(key for key, value in checks.items() if not value)
        raise BenchmarkError(f"hardware envelope is not enforced: {failed}")
    return record


def host_cpu_allowlist() -> str:
    """Return the first eight currently permitted CPUs for the Titan launcher."""

    chosen = host_cpu_selection()
    runs: list[str] = []
    start = previous = chosen[0]
    for value in chosen[1:]:
        if value == previous + 1:
            previous = value
            continue
        runs.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = value
    runs.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(runs)


def systemd_service_envelope_prefix(systemd_run: str) -> list[str]:
    """Build the synchronous delegated user-service prefix used on Titan.

    Ubuntu's systemd 252 rejects ``--wait`` together with ``--scope``.  A
    transient ``Type=exec`` user service supports synchronous exit propagation,
    direct stdio, controller delegation, and the same resource properties.
    ``CPUAffinity`` is the portable systemd-252 enforcement on Titan, while
    ``AllowedCPUs`` additionally activates cgroup cpuset containment when that
    controller is delegated.  The service-wide syscall filter prevents the
    controller, Codex, auditors, build tools, and all descendants from widening
    inherited affinity; the generated-command wrapper adds a second boundary.
    """

    cpus = host_cpu_allowlist()
    return [
        systemd_run,
        "--user",
        "--service-type=exec",
        "--quiet",
        "--wait",
        "--collect",
        "--pipe",
        "--property",
        f"AllowedCPUs={cpus}",
        "--property",
        f"CPUAffinity={cpus}",
        "--property",
        "SystemCallFilter=~sched_setaffinity",
        "--property",
        "SystemCallErrorNumber=EPERM",
        "--property",
        "SystemCallArchitectures=native",
        "--property",
        f"MemoryMax={EXPECTED_MEMORY_BYTES}",
        "--property",
        "MemorySwapMax=0",
        "--property",
        f"TasksMax={EXPECTED_TASKS_MAX}",
        "--property",
        "Delegate=yes",
    ]
