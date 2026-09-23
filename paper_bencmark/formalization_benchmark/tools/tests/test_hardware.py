from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from hardware import (  # noqa: E402
    EXPECTED_MEMORY_BYTES,
    EXPECTED_TASKS_MAX,
    affinity_mutation_canary,
    frozen_hardware_identity,
    snapshot_hardware,
    systemd_service_envelope_prefix,
    verify_frozen_hardware_identity,
)


def fixture() -> dict:
    return {
        "platform": "Linux-test",
        "machine": "x86_64",
        "hostname": "titan",
        "affinity_cpus": list(range(8)),
        "cpu_model_names": ["Test CPU"],
    }


class HardwareIdentityTests(unittest.TestCase):
    def test_affinity_mutation_canary_requires_kernel_denial(self) -> None:
        denied = PermissionError(1, "denied")
        with mock.patch("hardware.os.sched_setaffinity", side_effect=denied, create=True):
            self.assertTrue(affinity_mutation_canary(list(range(8)))["denied"])
        with mock.patch("hardware.os.sched_setaffinity", return_value=None, create=True):
            self.assertFalse(affinity_mutation_canary(list(range(8)))["denied"])

    def test_exact_identity_is_admitted(self) -> None:
        snapshot = fixture()
        expected = frozen_hardware_identity(snapshot)
        verify_frozen_hardware_identity(snapshot, expected)

    def test_cpu_set_change_is_rejected(self) -> None:
        expected = frozen_hardware_identity(fixture())
        changed = fixture()
        changed["affinity_cpus"] = list(range(1, 9))
        with self.assertRaisesRegex(BenchmarkError, "affinity_cpus"):
            verify_frozen_hardware_identity(changed, expected)

    def test_host_change_is_rejected(self) -> None:
        expected = frozen_hardware_identity(fixture())
        changed = fixture()
        changed["hostname"] = "other-host"
        with self.assertRaisesRegex(BenchmarkError, "hostname"):
            verify_frozen_hardware_identity(changed, expected)

    def test_systemd_envelope_is_a_waited_piped_service_not_a_scope(self) -> None:
        with mock.patch("hardware.host_cpu_allowlist", return_value="2-9"):
            command = systemd_service_envelope_prefix("/usr/bin/systemd-run")
        self.assertNotIn("--scope", command)
        self.assertIn("--service-type=exec", command)
        self.assertIn("--wait", command)
        self.assertIn("--pipe", command)
        self.assertIn("AllowedCPUs=2-9", command)
        self.assertIn("CPUAffinity=2-9", command)
        self.assertIn("SystemCallFilter=~sched_setaffinity", command)
        self.assertIn("SystemCallErrorNumber=EPERM", command)
        self.assertIn("SystemCallArchitectures=native", command)
        self.assertIn("MemoryMax=34359738368", command)
        self.assertIn("MemorySwapMax=0", command)
        self.assertIn("TasksMax=512", command)

    def test_strict_snapshot_accepts_systemd_affinity_without_optional_cpuset(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            cgroup = Path(temporary)
            (cgroup / "memory.max").write_text(
                str(EXPECTED_MEMORY_BYTES), encoding="ascii"
            )
            (cgroup / "memory.swap.max").write_text("0", encoding="ascii")
            (cgroup / "pids.max").write_text(str(EXPECTED_TASKS_MAX), encoding="ascii")

            def limits(_root: Path, filename: str) -> list[int]:
                if filename == "memory.max":
                    return [EXPECTED_MEMORY_BYTES]
                if filename == "pids.max":
                    return [EXPECTED_TASKS_MAX]
                return []

            with mock.patch("hardware._cgroup_v2_path", return_value=cgroup), mock.patch(
                "hardware._finite_ancestor_limits", side_effect=limits
            ), mock.patch(
                "hardware.os.sched_getaffinity", return_value=set(range(8)), create=True
            ), mock.patch(
                "hardware.platform.system", return_value="Linux"
            ), mock.patch(
                "hardware.platform.machine", return_value="x86_64"
            ), mock.patch(
                "hardware.affinity_mutation_canary",
                return_value={"attempted": True, "denied": True, "errno": 1},
            ):
                record = snapshot_hardware(strict=True)

        self.assertTrue(record["admitted"])
        self.assertEqual(record["cgroup_cpuset_effective"], [])
        self.assertTrue(record["checks"]["cgroup_cpuset_exactly_8_if_exposed"])

    def test_pilot20_profile_requires_its_exact_lane_and_24_gib(self) -> None:
        lane = {0, 1, 2, 3, 16, 17, 18, 19}
        memory = 24 * 1024 ** 3
        with tempfile.TemporaryDirectory() as temporary:
            cgroup = Path(temporary)
            (cgroup / "memory.max").write_text(str(memory), encoding="ascii")
            (cgroup / "memory.swap.max").write_text("0", encoding="ascii")
            (cgroup / "pids.max").write_text(str(EXPECTED_TASKS_MAX), encoding="ascii")

            def limits(_root: Path, filename: str) -> list[int]:
                return [memory] if filename == "memory.max" else [EXPECTED_TASKS_MAX]

            with mock.patch.dict("hardware.os.environ", {
                "HIGHAMBENCH_HARDWARE_PROFILE": "pilot20-lane-A",
            }, clear=True), mock.patch(
                "hardware._cgroup_v2_path", return_value=cgroup
            ), mock.patch(
                "hardware._finite_ancestor_limits", side_effect=limits
            ), mock.patch(
                "hardware.os.sched_getaffinity", return_value=lane, create=True
            ), mock.patch(
                "hardware.platform.system", return_value="Linux"
            ), mock.patch(
                "hardware.platform.machine", return_value="x86_64"
            ), mock.patch(
                "hardware.affinity_mutation_canary",
                return_value={"attempted": True, "denied": True, "errno": 1},
            ):
                record = snapshot_hardware(strict=True)
                self.assertTrue(record["admitted"])
                with mock.patch(
                    "hardware.os.sched_getaffinity", return_value=set(range(8)),
                    create=True,
                ):
                    with self.assertRaisesRegex(BenchmarkError, "affinity_matches_profile"):
                        snapshot_hardware(strict=True)


if __name__ == "__main__":
    unittest.main()
