from __future__ import annotations

from pathlib import Path
import sys
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
import design20_envelope as envelope  # noqa: E402
from hardware import HARDWARE_PROFILE_ENV  # noqa: E402
from titan_envelope import COMMAND_CGROUP_VARIABLE, MARKER  # noqa: E402


class Pilot20EnvelopeTests(unittest.TestCase):
    def test_launch_has_exact_lane_cpus_and_24_gib(self) -> None:
        environment = {MARKER: "0"}
        with mock.patch.dict(envelope.os.environ, environment, clear=True), mock.patch.object(
            envelope.shutil, "which", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            envelope.subprocess, "run", return_value=mock.Mock(returncode=0)
        ) as launched, mock.patch.object(
            envelope.sys, "argv", ["canary.py"]
        ):
            self.assertEqual(envelope.launch_or_activate(Path("/tmp/canary.py"), lane="B"), 0)
        command = launched.call_args.args[0]
        self.assertIn("AllowedCPUs=4-7,20-23", command)
        self.assertIn("CPUAffinity=4-7,20-23", command)
        self.assertIn("MemoryMax=25769803776", command)
        self.assertIn(f"{HARDWARE_PROFILE_ENV}=pilot20-lane-B", command)

    def test_activation_partitions_cgroup_and_checks_hardware(self) -> None:
        environment = {MARKER: "1", HARDWARE_PROFILE_ENV: "pilot20-lane-C"}
        with mock.patch.dict(envelope.os.environ, environment, clear=True), mock.patch.object(
            envelope, "prepare_command_cgroup",
            return_value=Path("/cgroup/commands/cgroup.procs"),
        ) as cgroup, mock.patch.object(
            envelope, "snapshot_hardware", return_value={"admitted": True}
        ) as hardware:
            self.assertIsNone(envelope.launch_or_activate(Path("/tmp/canary.py"), lane="C"))
            self.assertEqual(
                envelope.os.environ[COMMAND_CGROUP_VARIABLE],
                "/cgroup/commands/cgroup.procs",
            )
        self.assertEqual(cgroup.call_args.kwargs["outer_memory_bytes"], 24 * 1024 ** 3)
        self.assertEqual(cgroup.call_args.kwargs["command_memory_bytes"], 18 * 1024 ** 3)
        hardware.assert_called_once_with(strict=True)

    def test_wrong_lane_marker_fails_closed(self) -> None:
        with mock.patch.dict(envelope.os.environ, {
            MARKER: "1", HARDWARE_PROFILE_ENV: "pilot20-lane-A",
        }, clear=True):
            with self.assertRaisesRegex(BenchmarkError, "marker/profile mismatch"):
                envelope.launch_or_activate(Path("/tmp/canary.py"), lane="B")


if __name__ == "__main__":
    unittest.main()
