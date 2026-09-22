from __future__ import annotations

import os
from pathlib import Path
import sys
import types
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import design18_envelope  # noqa: E402
from titan_envelope import COMMAND_CGROUP_VARIABLE, MARKER  # noqa: E402


class Pilot18EnvelopeTests(unittest.TestCase):
    def test_launcher_uses_fixed_systemd_prefix(self) -> None:
        with (
            mock.patch.dict(os.environ, {MARKER: ""}, clear=False),
            mock.patch.object(design18_envelope.shutil, "which", return_value="/usr/bin/systemd-run"),
            mock.patch.object(design18_envelope, "systemd_service_envelope_prefix",
                              return_value=["/usr/bin/systemd-run", "--fixed"]),
            mock.patch.object(design18_envelope.subprocess, "run",
                              return_value=types.SimpleNamespace(returncode=7)) as runner,
            mock.patch.object(sys, "argv", ["program.py", "--task-id", "T0"]),
        ):
            self.assertEqual(design18_envelope.launch_or_activate(Path("/tmp/program.py")), 7)
        command = runner.call_args.args[0]
        self.assertEqual(command[:2], ["/usr/bin/systemd-run", "--fixed"])
        self.assertIn(f"{MARKER}=1", command)
        self.assertEqual(command[-2:], ["--task-id", "T0"])

    def test_child_activates_command_cgroup_and_strict_hardware(self) -> None:
        with (
            mock.patch.dict(os.environ, {MARKER: "1"}, clear=False),
            mock.patch.object(design18_envelope, "prepare_command_cgroup",
                              return_value=Path("/synthetic/cgroup.procs")),
            mock.patch.object(design18_envelope, "snapshot_hardware") as snapshot,
        ):
            os.environ.pop(COMMAND_CGROUP_VARIABLE, None)
            self.assertIsNone(design18_envelope.launch_or_activate(Path("/tmp/program.py")))
            self.assertEqual(os.environ[COMMAND_CGROUP_VARIABLE], "/synthetic/cgroup.procs")
            snapshot.assert_called_once_with(strict=True)
            os.environ.pop(COMMAND_CGROUP_VARIABLE, None)


if __name__ == "__main__":
    unittest.main()
