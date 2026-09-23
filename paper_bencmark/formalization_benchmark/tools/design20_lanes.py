"""Prospective, topology-balanced three-lane Titan resource plan.

The plan is validated against the live host before any Pilot 20 resource
envelope is admitted.  It is not an instruction to start three tasks before
the corpus and contention gates pass.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Iterable

from common import BenchmarkError


GIB = 1024 ** 3
LANE_MEMORY_BYTES = 24 * GIB
HOST_HEADROOM_BYTES = 16 * GIB
LANE_CPUS: dict[str, tuple[int, ...]] = {
    "A": (0, 1, 2, 3, 16, 17, 18, 19),
    "B": (4, 5, 6, 7, 20, 21, 22, 23),
    "C": (8, 9, 10, 11, 24, 25, 26, 27),
}


@dataclass(frozen=True)
class Cpu:
    logical: int
    core: int
    socket: int
    online: bool


def parse_lscpu_csv(lines: Iterable[str]) -> dict[int, Cpu]:
    records: dict[int, Cpu] = {}
    for line in lines:
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.strip().split(",")
        if len(fields) != 4 or fields[3] not in {"Y", "N"}:
            raise BenchmarkError("unexpected lscpu -p=CPU,CORE,SOCKET,ONLINE format")
        try:
            logical, core, socket = map(int, fields[:3])
        except ValueError as error:
            raise BenchmarkError("noninteger CPU topology field") from error
        if logical in records:
            raise BenchmarkError("duplicate logical CPU in topology")
        records[logical] = Cpu(logical, core, socket, fields[3] == "Y")
    if not records:
        raise BenchmarkError("empty CPU topology")
    return records


def validate_lane_plan(topology: dict[int, Cpu], *, mem_available_bytes: int,
                       affinity_cpus: set[int]) -> dict:
    used: set[int] = set()
    core_sets: dict[str, set[tuple[int, int]]] = {}
    for lane, chosen in LANE_CPUS.items():
        if len(chosen) != 8 or len(set(chosen)) != 8:
            raise BenchmarkError(f"lane {lane} does not have eight unique CPUs")
        if used.intersection(chosen):
            raise BenchmarkError("lane CPU sets overlap")
        if any(cpu not in topology or not topology[cpu].online
               or cpu not in affinity_cpus for cpu in chosen):
            raise BenchmarkError(f"lane {lane} contains unavailable CPUs")
        used.update(chosen)
        core_counts = Counter((topology[cpu].socket, topology[cpu].core)
                              for cpu in chosen)
        if sorted(core_counts.values()) != [1, 1, 1, 1, 2, 2]:
            raise BenchmarkError(f"lane {lane} has an unbalanced SMT composition")
        core_sets[lane] = set(core_counts)
    if any(core_sets[left] & core_sets[right]
           for left in LANE_CPUS for right in LANE_CPUS if left < right):
        raise BenchmarkError("lanes share physical cores")
    required = len(LANE_CPUS) * LANE_MEMORY_BYTES + HOST_HEADROOM_BYTES
    if mem_available_bytes < required:
        raise BenchmarkError("insufficient available host RAM for three lanes and headroom")
    return {
        "schema_version": "pilot-20-lane-plan-1",
        "lane_memory_limit_bytes": LANE_MEMORY_BYTES,
        "host_headroom_required_bytes": HOST_HEADROOM_BYTES,
        "host_mem_available_bytes_at_check": mem_available_bytes,
        "lanes": {
            lane: {"logical_cpus": list(chosen),
                   "physical_core_count": len(core_sets[lane])}
            for lane, chosen in LANE_CPUS.items()
        },
        "reserved_host_logical_cpus": sorted(affinity_cpus - used),
    }
