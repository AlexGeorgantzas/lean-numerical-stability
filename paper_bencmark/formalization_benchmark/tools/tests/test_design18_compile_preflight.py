from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError  # noqa: E402
from design18_compile_preflight import run  # noqa: E402


class Pilot18CompilePreflightTests(unittest.TestCase):
    def test_flagged_source_rejected_before_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw) / "preflight"
            with self.assertRaisesRegex(BenchmarkError, "flagged source tasks"):
                run(deployment_path=Path("/synthetic/deployment.json"),
                    mathlib_atlas=Path("/synthetic/mathlib.jsonl"),
                    output_root=root, task_ids=["HM19-3-4"])
            self.assertFalse(root.exists())


if __name__ == "__main__":
    unittest.main()
