from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / "formalization_benchmark" / "tools"
for directory in (str(TOOLS), str(ROOT / "pilot35")):
    if directory not in sys.path:
        sys.path.insert(0, directory)

from common import BenchmarkError, canonical_json_bytes, sha256_file  # noqa: E402
from recovery_controller import verify_source  # noqa: E402


class RecoveryPartitionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.source = Path(self.temp.name) / "pilot34"
        self.source.mkdir()
        self.schedule = [f"TASK-{index:02d}" for index in range(15)]
        self.preserved: dict[str, str] = {}
        self.incident: dict[str, str] = {}
        self.entries: list[dict] = []
        for index in range(5):
            task = self.schedule[index]
            directory = self.source / task
            directory.mkdir()
            status = "PAIR_INCIDENT" if index == 3 else "AUDITED_FAITHFUL_PAIR"
            path = directory / "pair-report.json"
            path.write_text(json.dumps({"task_id": task, "status": status}))
            digest = sha256_file(path)
            (self.incident if index == 3 else self.preserved)[task] = digest
            self.entries.append({"task_id": task, "pair_report_sha256": digest})
        inputs = {"schedule": self.schedule}
        inputs_sha = hashlib.sha256(canonical_json_bytes(inputs)).hexdigest()
        prior = {
            "status": "PAUSED_CONCURRENT_INCIDENT",
            "inputs": inputs, "inputs_sha256": inputs_sha,
            "pairs": self.entries,
            # The reviewed canary was launched before parallel launch logging.
            "launches": [{"task_id": task} for task in self.schedule[1:5]],
        }
        path = self.source / "campaign.json"
        path.write_text(json.dumps(prior))
        self.manifest = {
            "source_campaign_root": str(self.source),
            "source_campaign_sha256": sha256_file(path),
            "source_inputs_sha256": inputs_sha,
            "preserved_pair_report_sha256": self.preserved,
            "incident_pair_report_sha256": self.incident,
            "recovery_task_order": [task for task in self.schedule
                                    if task not in self.preserved],
        }

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_only_incident_and_unstarted_tasks_are_recovered(self) -> None:
        source, prior = verify_source(
            self.manifest, {"scheduled_order": self.schedule},
        )
        self.assertEqual(source, self.source)
        self.assertEqual(len(prior["pairs"]), 5)
        self.assertEqual(len(self.manifest["recovery_task_order"]), 11)

    def test_modified_preserved_pair_is_refused(self) -> None:
        task = next(iter(self.preserved))
        (self.source / task / "pair-report.json").write_text("changed")
        with self.assertRaisesRegex(BenchmarkError, "sealed pair changed"):
            verify_source(self.manifest, {"scheduled_order": self.schedule})

    def test_unstarted_artifact_is_refused(self) -> None:
        (self.source / self.schedule[5]).mkdir()
        with self.assertRaisesRegex(BenchmarkError, "unstarted"):
            verify_source(self.manifest, {"scheduled_order": self.schedule})


if __name__ == "__main__":
    unittest.main()
