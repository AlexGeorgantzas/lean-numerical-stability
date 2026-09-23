import json
from pathlib import Path
import tempfile
import unittest

from design27_search_diagnostics import inspect_events


class SearchDiagnosticsTests(unittest.TestCase):
    def test_explicit_tool_intervals_are_not_called_total_search_time(self):
        events = [
            {"method": "turn/started", "emittedAtMs": 1000},
            {"method": "item/started", "emittedAtMs": 1500,
             "params": {"item": {"type": "commandExecution", "id": "a",
                                 "command": "rg -n gamma /library/NumStability"}}},
            {"method": "item/completed", "emittedAtMs": 3500,
             "params": {"item": {"type": "commandExecution", "id": "a"}}},
            {"method": "item/started", "emittedAtMs": 4100,
             "params": {"item": {"type": "fileChange", "id": "e"}}},
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "events.jsonl"
            path.write_text("\n".join(json.dumps(item) for item in events) + "\n")
            report = inspect_events(path)
        self.assertEqual(
            report["tool_wall_seconds_by_category_not_deduplicated"]
            ["explicit_library_search_or_type_probe"], 2.0,
        )
        self.assertEqual(
            report["pre_first_file_change_seconds_includes_paper_and_reasoning"],
            3.1,
        )
        self.assertIn("do not subtract", report["interpretation"])


if __name__ == "__main__":
    unittest.main()
