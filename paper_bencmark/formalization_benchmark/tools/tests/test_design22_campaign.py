from __future__ import annotations

import argparse
from pathlib import Path
import unittest
from unittest import mock

from design22_campaign import ROOT, _pair_command, _pair_env, _run_refilled_lanes
from pair_controller import _environment_note


class Pilot22CampaignTests(unittest.TestCase):
    def test_shared_prompt_and_environment_explain_safe_exploration(self) -> None:
        common = (ROOT / "prompts" / "common.md").read_text()
        environment = _environment_note()
        for text in (common, environment):
            self.assertIn("printenv LEAN_PATH", text)
            self.assertIn("find /", text)
            self.assertIn("condition", text)

    def test_pair_command_freezes_alternating_order_and_independent_lane(self) -> None:
        args = argparse.Namespace(
            deployment=Path("/tmp/deployment.json"),
            mathlib_atlas=Path("/tmp/mathlib"),
            numstability_atlas=Path("/tmp/numstability"),
            model_qualification=Path("/tmp/qualification.json"),
            warm_root=Path("/tmp/warm"), output_root=Path("/tmp/campaign"),
            pilot_id="pilot23-empty-control-mount",
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

    def test_expansion_pair_carries_frozen_corpus_and_admission(self) -> None:
        args = argparse.Namespace(
            deployment=Path("/tmp/deployment.json"),
            mathlib_atlas=Path("/tmp/mathlib"),
            numstability_atlas=Path("/tmp/numstability"),
            model_qualification=Path("/tmp/qualification.json"),
            warm_root=Path("/tmp/warm"), output_root=Path("/tmp/campaign"),
            corpus=Path("/tmp/corpus12.json"), admission=Path("/tmp/admission12.json"),
        )
        command = _pair_command(args, "RUMP12-THM3.4", 3, "A")
        self.assertEqual(command[command.index("--corpus") + 1], "/tmp/corpus12.json")
        self.assertEqual(command[command.index("--admission") + 1], "/tmp/admission12.json")
        self.assertEqual(command[command.index("--condition-order") + 1], "R1,R0")

    def test_refills_a_freed_lane_without_waiting_for_slow_sibling(self) -> None:
        args = argparse.Namespace(
            deployment=Path("/tmp/deployment.json"),
            mathlib_atlas=Path("/tmp/mathlib"),
            numstability_atlas=Path("/tmp/numstability"),
            model_qualification=Path("/tmp/qualification.json"),
            warm_root=Path("/tmp/warm"), output_root=Path("/tmp/campaign"),
        )
        events: list[tuple[str, str, str]] = []
        companions: dict[str, list[str]] = {}

        class FakeProcess:
            returncode = 0

            def __init__(self, task: str):
                self.task = task
                self.polls = 0

            def poll(self):
                self.polls += 1
                threshold = 12 if self.task == "a" else 5 if self.task == "c" else 2
                return 0 if self.polls >= threshold else None

            def communicate(self):
                return b"", b""

        def fake_popen(command, **_kwargs):
            task = command[command.index("--task-id") + 1]
            lane = command[command.index("--lane") + 1]
            events.append(("start", task, lane))
            return FakeProcess(task)

        def fake_record(_args, _journal, task, _index, lane, _code,
                        _stdout, _stderr, co_scheduled):
            events.append(("finish", task, lane))
            companions[task] = co_scheduled
            return {"pair_status": "AUDITED_FAITHFUL_PAIR"}

        with (mock.patch("design22_campaign.subprocess.Popen", side_effect=fake_popen),
              mock.patch("design22_campaign._record_pair", side_effect=fake_record),
              mock.patch("design22_campaign.write_json_atomic"),
              mock.patch("design22_campaign.time.sleep")):
            incident = _run_refilled_lanes(args, {"pairs": []},
                                           ["first", "a", "b", "c", "d"])
        self.assertFalse(incident)
        self.assertLess(events.index(("start", "d", "B")),
                        events.index(("finish", "a", "A")))
        self.assertEqual(companions["d"], ["a", "c"])
        occupied: set[str] = set()
        for action, _task, lane in events:
            if action == "start":
                self.assertNotIn(lane, occupied)
                occupied.add(lane)
                self.assertLessEqual(len(occupied), 3)
            else:
                occupied.remove(lane)
        self.assertFalse(occupied)

    def test_incident_stops_refilling_but_seals_active_siblings(self) -> None:
        args = argparse.Namespace(
            deployment=Path("/tmp/deployment.json"),
            mathlib_atlas=Path("/tmp/mathlib"),
            numstability_atlas=Path("/tmp/numstability"),
            model_qualification=Path("/tmp/qualification.json"),
            warm_root=Path("/tmp/warm"), output_root=Path("/tmp/campaign"),
        )
        started: list[str] = []
        finished: list[str] = []

        class FakeProcess:
            returncode = 0

            def __init__(self, task: str):
                self.task = task
                self.polls = 0

            def poll(self):
                self.polls += 1
                return 0 if self.polls >= (5 if self.task == "a" else 2) else None

            def communicate(self):
                return b"", b""

        def fake_popen(command, **_kwargs):
            task = command[command.index("--task-id") + 1]
            started.append(task)
            return FakeProcess(task)

        def fake_record(_args, _journal, task, *_args2):
            finished.append(task)
            return {"pair_status": "PAIR_INCIDENT" if task == "b"
                    else "AUDITED_FAITHFUL_PAIR"}

        with (mock.patch("design22_campaign.subprocess.Popen", side_effect=fake_popen),
              mock.patch("design22_campaign._record_pair", side_effect=fake_record),
              mock.patch("design22_campaign.write_json_atomic"),
              mock.patch("design22_campaign.time.sleep")):
            incident = _run_refilled_lanes(args, {"pairs": []},
                                           ["first", "a", "b", "c", "d"])
        self.assertTrue(incident)
        self.assertEqual(started, ["a", "b", "c"])
        self.assertEqual(set(finished), {"a", "b", "c"})


if __name__ == "__main__":
    unittest.main()
