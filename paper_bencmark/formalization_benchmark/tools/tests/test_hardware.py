from __future__ import annotations

from pathlib import Path
import sys
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from hardware import frozen_hardware_identity, verify_frozen_hardware_identity  # noqa: E402


def fixture() -> dict:
    return {
        "platform": "Linux-test",
        "machine": "x86_64",
        "hostname": "titan",
        "affinity_cpus": list(range(8)),
        "cpu_model_names": ["Test CPU"],
    }


class HardwareIdentityTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
