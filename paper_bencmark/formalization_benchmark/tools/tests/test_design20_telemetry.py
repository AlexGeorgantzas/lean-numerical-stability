from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from common import BenchmarkError
from design20_telemetry import lane_service_cgroup, read_cgroup_sample, summarize_samples


class CgroupTelemetryTests(unittest.TestCase):
    def test_resolves_parent_containing_control_and_commands(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            control = root / "highambench-control"
            commands = root / "highambench-commands"
            control.mkdir()
            commands.mkdir()
            (commands / "cgroup.procs").write_text("", encoding="ascii")
            (root / "memory.max").write_text("123\n", encoding="ascii")
            (root / "cpu.stat").write_text("usage_usec 0\n", encoding="ascii")
            self.assertEqual(
                lane_service_cgroup(control, commands / "cgroup.procs"), root
            )
            with self.assertRaisesRegex(BenchmarkError, "not a sibling"):
                lane_service_cgroup(control, control / "cgroup.procs")

    def test_reads_exact_cgroup_counters(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "memory.current").write_text("1048576\n", encoding="ascii")
            (root / "memory.peak").write_text("2097152\n", encoding="ascii")
            (root / "cpu.stat").write_text(
                "usage_usec 500000\nuser_usec 400000\nsystem_usec 100000\n",
                encoding="ascii",
            )
            (root / "memory.events").write_text(
                "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n", encoding="ascii"
            )
            sample = read_cgroup_sample(root, when=2.0)
            self.assertEqual(sample["memory_current_bytes"], 1048576)
            self.assertEqual(sample["cpu_usage_usec"], 500000)
            self.assertEqual(sample["memory_events"]["oom_kill"], 0)

    def test_condition_local_peak_and_cpu_rate(self) -> None:
        samples = [
            {"monotonic_seconds": 1.0, "memory_current_bytes": 2,
             "memory_peak_cgroup_lifetime_bytes": 50, "cpu_usage_usec": 0,
             "memory_events": {"oom": 0}},
            {"monotonic_seconds": 2.0, "memory_current_bytes": 9,
             "memory_peak_cgroup_lifetime_bytes": 50, "cpu_usage_usec": 4_000_000,
             "memory_events": {"oom": 0}},
            {"monotonic_seconds": 3.0, "memory_current_bytes": 5,
             "memory_peak_cgroup_lifetime_bytes": 50, "cpu_usage_usec": 5_000_000,
             "memory_events": {"oom": 1}},
        ]
        summary = summarize_samples(samples, lane_cpus=8)
        self.assertEqual(summary["peak_memory_current_bytes_sampled"], 9)
        self.assertEqual(summary["cgroup_lifetime_memory_peak_bytes_at_end"], 50)
        self.assertEqual(summary["peak_cpu_cores_sampled"], 4)
        self.assertEqual(summary["peak_cpu_percent_of_lane_sampled"], 50)
        self.assertEqual(summary["memory_events_delta"]["oom"], 1)

    def test_rejects_counter_reset(self) -> None:
        samples = [
            {"monotonic_seconds": 1.0, "memory_current_bytes": 1,
             "memory_peak_cgroup_lifetime_bytes": 1, "cpu_usage_usec": 10,
             "memory_events": {}},
            {"monotonic_seconds": 2.0, "memory_current_bytes": 1,
             "memory_peak_cgroup_lifetime_bytes": 1, "cpu_usage_usec": 9,
             "memory_events": {}},
        ]
        with self.assertRaises(BenchmarkError):
            summarize_samples(samples, lane_cpus=8)


if __name__ == "__main__":
    unittest.main()
