from __future__ import annotations

import unittest

from common import BenchmarkError
from design20_lanes import GIB, parse_lscpu_csv, validate_lane_plan


def titan_topology() -> dict:
    rows = ["# CPU,Core,Socket,Online"]
    for cpu in range(32):
        core = cpu // 2 if cpu < 16 else cpu - 8
        rows.append(f"{cpu},{core},0,Y")
    return parse_lscpu_csv(rows)


class LanePlanTests(unittest.TestCase):
    def test_titan_plan_is_balanced(self) -> None:
        plan = validate_lane_plan(
            titan_topology(), mem_available_bytes=90 * GIB,
            affinity_cpus=set(range(32)),
        )
        self.assertEqual([plan["lanes"][lane]["physical_core_count"]
                          for lane in ("A", "B", "C")], [6, 6, 6])
        self.assertEqual(len(plan["reserved_host_logical_cpus"]), 8)

    def test_rejects_insufficient_headroom(self) -> None:
        with self.assertRaises(BenchmarkError):
            validate_lane_plan(
                titan_topology(), mem_available_bytes=80 * GIB,
                affinity_cpus=set(range(32)),
            )

    def test_rejects_topology_change(self) -> None:
        topology = titan_topology()
        topology[19] = topology[18]
        with self.assertRaises(BenchmarkError):
            validate_lane_plan(
                topology, mem_available_bytes=90 * GIB,
                affinity_cpus=set(range(32)),
            )


if __name__ == "__main__":
    unittest.main()
