from __future__ import annotations

import argparse
from pathlib import Path
import unittest
from unittest import mock

from design22_campaign import _pair_command, _pair_env


class Pilot22CampaignTests(unittest.TestCase):
    def test_pair_command_freezes_alternating_order_and_independent_lane(self) -> None:
        args = argparse.Namespace(
            deployment=Path("/tmp/deployment.json"),
            mathlib_atlas=Path("/tmp/mathlib"),
            numstability_atlas=Path("/tmp/numstability"),
            model_qualification=Path("/tmp/qualification.json"),
            warm_root=Path("/tmp/warm"), output_root=Path("/tmp/campaign"),
        )
        first = _pair_command(args, "FAB19-EQ3.5", 0, "A")
        second = _pair_command(args, "FAB19-EQ3.7", 1, "B")
        third = _pair_command(args, "H20-8", 2, "C")
        self.assertEqual(first[first.index("--condition-order") + 1], "R0,R1")
        self.assertEqual(second[second.index("--condition-order") + 1], "R1,R0")
        self.assertEqual(third[third.index("--condition-order") + 1], "R0,R1")
        self.assertEqual(second[second.index("--lane") + 1], "B")
        self.assertEqual(third[third.index("--lane") + 1], "C")

    def test_child_starts_outside_parent_envelope(self) -> None:
        with mock.patch.dict("os.environ", {
            "HIGHAMBENCH_TITAN_ENVELOPE": "1",
            "HIGHAMBENCH_HARDWARE_PROFILE": "pilot20-lane-A",
            "HIGHAMBENCH_COMMAND_CGROUP_PROCS": "/parent/procs",
            "KEEP": "yes",
        }):
            env = _pair_env()
        self.assertEqual(env["KEEP"], "yes")
        self.assertNotIn("HIGHAMBENCH_TITAN_ENVELOPE", env)
        self.assertNotIn("HIGHAMBENCH_HARDWARE_PROFILE", env)
        self.assertNotIn("HIGHAMBENCH_COMMAND_CGROUP_PROCS", env)


if __name__ == "__main__":
    unittest.main()
