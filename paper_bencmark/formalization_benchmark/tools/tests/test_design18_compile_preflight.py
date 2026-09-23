from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from design18_compile_preflight import _proposal_packet, run  # noqa: E402
from design18_preflight import DESIGN_ROOT  # noqa: E402


class Pilot18CompilePreflightTests(unittest.TestCase):
    def test_unadopted_proposals_bind_exact_pdf(self) -> None:
        for filename, task_id in (("HI21-2-6.json", "HI21-2-6"),
                                  ("HM19-3-4-corrected.json", "HM19-3-4")):
            with self.subTest(task_id=task_id):
                resolved_id, packet = _proposal_packet(
                    DESIGN_ROOT / "proposals" / filename
                )
                self.assertEqual(resolved_id, task_id)
                self.assertTrue(packet["status"].startswith("UNADOPTED_"))

    def test_proposal_outside_dedicated_directory_rejected(self) -> None:
        with self.assertRaisesRegex(BenchmarkError, "regular file"):
            _proposal_packet(DESIGN_ROOT / "packets" / "HM19-3-4.json")

    def test_flagged_source_rejected_before_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "preflight"
            with self.assertRaisesRegex(BenchmarkError, "flagged source tasks"):
                run(deployment_path=Path("/synthetic/deployment.json"),
                    mathlib_atlas=Path("/synthetic/mathlib.jsonl"),
                    numstability_atlas=Path("/synthetic/numstability"),
                    output_root=root, task_ids=["HM19-3-4"])
            self.assertFalse(root.exists())


if __name__ == "__main__":
    unittest.main()
