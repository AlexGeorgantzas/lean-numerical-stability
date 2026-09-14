from __future__ import annotations

import os
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from titan_envelope import (  # noqa: E402
    COMMAND_CPU_WEIGHT,
    COMMAND_MEMORY_BYTES,
    COMMAND_TASKS_MAX,
    CONTROL_CPU_WEIGHT,
    CONTROL_MEMORY_LOW_BYTES,
    prepare_command_cgroup,
)


class TitanEnvelopeTests(unittest.TestCase):
    def test_prepares_separate_control_and_command_cgroups(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cgroup_root = root / "cgroup"
            scope = cgroup_root / "user.slice" / "scope"
            scope.mkdir(parents=True)
            (scope / "cgroup.controllers").write_text(
                "cpu memory pids\n", encoding="ascii"
            )
            proc_cgroup = root / "proc-cgroup"
            proc_cgroup.write_text("0::/user.slice/scope\n", encoding="ascii")

            endpoint = prepare_command_cgroup(
                proc_cgroup=proc_cgroup, cgroup_root=cgroup_root
            )

            control = scope / "highambench-control"
            commands = scope / "highambench-commands"
            # macOS exposes /var through the /private/var symlink; compare the
            # canonical paths so this Linux-oriented test remains portable.
            self.assertEqual(endpoint.resolve(), (commands / "cgroup.procs").resolve())
            self.assertEqual(
                (scope / "cgroup.subtree_control").read_text(encoding="ascii"),
                "+cpu +memory +pids",
            )
            self.assertEqual(
                (control / "cgroup.procs").read_text(encoding="ascii"), str(os.getpid())
            )
            self.assertEqual(
                (control / "memory.low").read_text(encoding="ascii"),
                str(CONTROL_MEMORY_LOW_BYTES),
            )
            self.assertEqual(
                (control / "cpu.weight").read_text(encoding="ascii"),
                str(CONTROL_CPU_WEIGHT),
            )
            self.assertEqual(
                (commands / "memory.max").read_text(encoding="ascii"),
                str(COMMAND_MEMORY_BYTES),
            )
            self.assertEqual(
                (commands / "pids.max").read_text(encoding="ascii"),
                str(COMMAND_TASKS_MAX),
            )
            self.assertEqual(
                (commands / "cpu.weight").read_text(encoding="ascii"),
                str(COMMAND_CPU_WEIGHT),
            )

    def test_requires_all_delegated_controllers(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cgroup_root = root / "cgroup"
            scope = cgroup_root / "scope"
            scope.mkdir(parents=True)
            (scope / "cgroup.controllers").write_text(
                "memory pids\n", encoding="ascii"
            )
            proc_cgroup = root / "proc-cgroup"
            proc_cgroup.write_text("0::/scope\n", encoding="ascii")
            with self.assertRaisesRegex(Exception, "cpu, memory, and pids"):
                prepare_command_cgroup(
                    proc_cgroup=proc_cgroup, cgroup_root=cgroup_root
                )


if __name__ == "__main__":
    unittest.main()
