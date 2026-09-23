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
from design18_preflight import DESIGN_ROOT, check_corpus  # noqa: E402


class Pilot18CompilePreflightTests(unittest.TestCase):
    def test_source_resolved_packets_bind_exact_pdf(self) -> None:
        corpus, packets, flags = check_corpus()
        self.assertFalse(flags)
        self.assertEqual(corpus["pilot_identity"], "19-source-resolved")
        by_id = {packet["task_id"]: packet for packet in packets}
        for task_id in ("HI21-2-6", "HM19-3-4"):
            with self.subTest(task_id=task_id):
                self.assertEqual(by_id[task_id]["status"],
                                 "SOURCE_RESOLVED_PILOT_19_NOT_RUN")

    def test_proposal_outside_dedicated_directory_rejected(self) -> None:
        with self.assertRaisesRegex(BenchmarkError, "regular file"):
            _proposal_packet(DESIGN_ROOT / "packets" / "HM19-3-4.json")

    def test_unknown_task_rejected_before_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "preflight"
            with self.assertRaisesRegex(BenchmarkError, "unknown task"):
                run(deployment_path=Path("/synthetic/deployment.json"),
                    mathlib_atlas=Path("/synthetic/mathlib.jsonl"),
                    numstability_atlas=Path("/synthetic/numstability"),
                    output_root=root, task_ids=["CASTRO24-4-1"])
            self.assertFalse(root.exists())


if __name__ == "__main__":
    unittest.main()
