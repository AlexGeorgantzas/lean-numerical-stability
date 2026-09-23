"""Cgroup-v2 resource telemetry for a prospective, isolated Pilot 20 lane.

This module does not change the timed contestant clock.  A controller can run
one sampler around each condition and keep the resulting trace/summary beside
the immutable condition artifact.  The sampled peak is condition-local;
``memory.peak`` is reported separately because it may predate that condition
when a lane service hosts several tasks.
"""

from __future__ import annotations

import json
from pathlib import Path
import threading
import time
from typing import Any

from common import BenchmarkError, sha256_file, utc_now, write_bytes_atomic, write_json_atomic


def lane_service_cgroup(control_cgroup: Path, command_cgroup_procs: Path) -> Path:
    """Resolve the bounded parent that contains both model/control and tools."""
    if control_cgroup.name != "highambench-control":
        raise BenchmarkError("unexpected benchmark control cgroup")
    parent = control_cgroup.parent
    expected_command = parent / "highambench-commands" / "cgroup.procs"
    if (command_cgroup_procs != expected_command
            or command_cgroup_procs.is_symlink()
            or not command_cgroup_procs.is_file()):
        raise BenchmarkError("benchmark command cgroup is not a sibling")
    if not (parent / "memory.max").is_file() or not (parent / "cpu.stat").is_file():
        raise BenchmarkError("benchmark lane service counters are unavailable")
    return parent


def _integer_field(path: Path) -> int:
    raw = path.read_text(encoding="ascii").strip()
    if not raw.isdecimal():
        raise BenchmarkError(f"invalid cgroup counter: {path}")
    return int(raw)


def _keyed_counters(path: Path) -> dict[str, int]:
    counters: dict[str, int] = {}
    for line in path.read_text(encoding="ascii").splitlines():
        fields = line.split()
        if len(fields) != 2 or not fields[1].isdecimal():
            raise BenchmarkError(f"invalid cgroup counter line: {path}")
        counters[fields[0]] = int(fields[1])
    return counters


def read_cgroup_sample(cgroup: Path, *, when: float | None = None) -> dict[str, Any]:
    """Read usage from the exact lane cgroup, never aggregate host counters."""
    if not cgroup.is_dir():
        raise BenchmarkError(f"missing cgroup directory: {cgroup}")
    cpu = _keyed_counters(cgroup / "cpu.stat")
    if "usage_usec" not in cpu:
        raise BenchmarkError("cgroup cpu.stat lacks usage_usec")
    return {
        "monotonic_seconds": time.monotonic() if when is None else when,
        "memory_current_bytes": _integer_field(cgroup / "memory.current"),
        "memory_peak_cgroup_lifetime_bytes": _integer_field(cgroup / "memory.peak"),
        "cpu_usage_usec": cpu["usage_usec"],
        "cpu_user_usec": cpu.get("user_usec"),
        "cpu_system_usec": cpu.get("system_usec"),
        "memory_events": _keyed_counters(cgroup / "memory.events"),
    }


def summarize_samples(samples: list[dict[str, Any]], *, lane_cpus: int) -> dict[str, Any]:
    if lane_cpus <= 0 or not samples:
        raise BenchmarkError("resource summary requires samples and positive lane size")
    peak_cores = 0.0
    for before, after in zip(samples, samples[1:]):
        elapsed = after["monotonic_seconds"] - before["monotonic_seconds"]
        cpu_delta = after["cpu_usage_usec"] - before["cpu_usage_usec"]
        if elapsed <= 0 or cpu_delta < 0:
            raise BenchmarkError("cgroup CPU samples are not monotone")
        peak_cores = max(peak_cores, cpu_delta / (elapsed * 1_000_000))
    first, last = samples[0], samples[-1]
    events_before, events_after = first["memory_events"], last["memory_events"]
    return {
        "schema_version": "pilot-20-condition-resources-1",
        "sample_count": len(samples),
        "sampled_wall_seconds": last["monotonic_seconds"] - first["monotonic_seconds"],
        "lane_logical_cpus": lane_cpus,
        "peak_cpu_cores_sampled": peak_cores,
        "peak_cpu_percent_of_lane_sampled": 100 * peak_cores / lane_cpus,
        "cpu_usage_seconds": (last["cpu_usage_usec"] - first["cpu_usage_usec"]) / 1_000_000,
        "peak_memory_current_bytes_sampled": max(s["memory_current_bytes"] for s in samples),
        "cgroup_lifetime_memory_peak_bytes_at_end": last["memory_peak_cgroup_lifetime_bytes"],
        "memory_events_delta": {
            key: events_after[key] - events_before.get(key, 0)
            for key in events_after
        },
        "note": (
            "CPU peak is the largest sample-interval mean, not an instantaneous peak. "
            "The cgroup-lifetime memory peak may include earlier conditions in this lane."
        ),
    }


class CgroupSampler:
    """Sample one cgroup for the duration of one condition."""

    def __init__(self, cgroup: Path, *, lane_cpus: int = 8,
                 interval_seconds: float = 1.0) -> None:
        if interval_seconds <= 0:
            raise BenchmarkError("resource sample interval must be positive")
        self.cgroup = cgroup
        self.lane_cpus = lane_cpus
        self.interval_seconds = interval_seconds
        self.samples: list[dict[str, Any]] = []
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._error: Exception | None = None
        self.started_at_utc: str | None = None
        self.ended_at_utc: str | None = None

    def _poll(self) -> None:
        try:
            while not self._stop.wait(self.interval_seconds):
                self.samples.append(read_cgroup_sample(self.cgroup))
        except Exception as error:
            self._error = error
            self._stop.set()

    def __enter__(self) -> "CgroupSampler":
        self.started_at_utc = utc_now()
        self.samples.append(read_cgroup_sample(self.cgroup))
        self._thread = threading.Thread(target=self._poll, daemon=True)
        self._thread.start()
        return self

    def __exit__(self, _type: object, _value: object, _traceback: object) -> None:
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=self.interval_seconds + 5)
            if self._thread.is_alive():
                raise BenchmarkError("resource sampler failed to stop")
        self.samples.append(read_cgroup_sample(self.cgroup))
        self.ended_at_utc = utc_now()
        if self._error is not None:
            raise BenchmarkError(f"resource sampling failed: {self._error}")

    def write(self, trace_path: Path, summary_path: Path) -> dict[str, Any]:
        if self.ended_at_utc is None:
            raise BenchmarkError("resource sampler has not finished")
        if trace_path.exists() or summary_path.exists():
            raise BenchmarkError("resource output exists; refusing overwrite")
        summary = summarize_samples(self.samples, lane_cpus=self.lane_cpus)
        summary["started_at_utc"] = self.started_at_utc
        summary["ended_at_utc"] = self.ended_at_utc
        summary["cgroup_path"] = str(self.cgroup)
        summary["sample_interval_seconds"] = self.interval_seconds
        write_bytes_atomic(
            trace_path,
            "".join(json.dumps(sample, sort_keys=True) + "\n" for sample in self.samples)
            .encode("utf-8"),
            mode=0o400,
        )
        summary["trace_sha256"] = sha256_file(trace_path)
        write_json_atomic(summary_path, summary, mode=0o400)
        return summary
