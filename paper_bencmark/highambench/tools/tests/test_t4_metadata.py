from __future__ import annotations

import copy
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
TESTS = Path(__file__).resolve().parent
for directory in (TOOLS, TESTS):
    if str(directory) not in sys.path:
        sys.path.insert(0, str(directory))

from common import BenchmarkToolError  # noqa: E402
from t4_metadata import manage_t4_metadata  # noqa: E402
from test_task_tags import base_t4_task  # noqa: E402


def _replace_paper(value: object, paper_id: str) -> object:
    if isinstance(value, str):
        return value.replace("P01", paper_id)
    if isinstance(value, list):
        return [_replace_paper(item, paper_id) for item in value]
    if isinstance(value, dict):
        return {key: _replace_paper(item, paper_id) for key, item in value.items()}
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class T4MetadataTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name) / "highambench"
        self.root.mkdir()

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _stage(self, paper_id: str, *, accepted: bool = False) -> Path:
        task = copy.deepcopy(_replace_paper(base_t4_task(), paper_id))
        assert isinstance(task, dict)
        if not accepted:
            task["construction_inputs"]["review_campaign_status"] = (
                "replacement_required"
            )
            for review_unit in task["review_units"]:
                review_unit["review_status"] = "pending"
            task["faithfulness_reviews"] = []

        definitions = (
            self.root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean"
        )
        task_root = self.root / "tasks" / paper_id / "T4"
        definitions.parent.mkdir(parents=True, exist_ok=True)
        task_root.mkdir(parents=True)
        definitions.write_text(
            "import Mathlib\nnamespace HighamBench\ndef value := 0\nend HighamBench\n",
            encoding="utf-8",
        )
        target = task_root / "Target.lean"
        target.write_text(
            f"import HighamBench.{paper_id}Definitions\n"
            "namespace HighamBench\ntheorem placeholder : True := by sorry\n"
            "end HighamBench\n",
            encoding="utf-8",
        )
        inventory = task_root / "source_inventory.json"
        inventory.write_text(
            json.dumps(
                {
                    "schema_version": "highambench-t4-source-inventory-0.3",
                    "paper_id": paper_id,
                    "title": "Synthetic T4 paper",
                    "status": "construction",
                    "inventory_method": "Synthetic complete source-order inventory.",
                    "source": copy.deepcopy(task["paper_source"]),
                    "named_results": ["Theorem 2.1"],
                    "local_numbered_equations": [],
                    "items": copy.deepcopy(task["source_inventory"]),
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        if accepted:
            task["construction_inputs"].update(
                {
                    "paper_definitions_sha256": _sha256(definitions),
                    "source_inventory_sha256": _sha256(inventory),
                    "target_sha256": _sha256(target),
                }
            )
        else:
            task["construction_inputs"].update(
                {
                    "paper_definitions_sha256": "0" * 64,
                    "source_inventory_sha256": "0" * 64,
                    "target_sha256": "0" * 64,
                }
            )
        task_path = task_root / "task.json"
        task_path.write_text(
            json.dumps(task, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        return task_path

    def test_write_set_reports_only_own_task_record_without_creating_it(self) -> None:
        result = manage_t4_metadata(self.root, "P06", mode="write-set")
        self.assertEqual(
            result["write_set"], [{"path": "tasks/P06/T4/task.json"}]
        )
        self.assertEqual(result["written"], [])
        self.assertFalse((self.root / "tasks").exists())

    def test_parallel_freeze_has_disjoint_paper_local_writes(self) -> None:
        paths = {paper_id: self._stage(paper_id) for paper_id in ("P06", "P07")}
        global_sentinel = self.root / "metadata" / "manifest.json"
        sibling_sentinel = self.root / "tasks" / "P01" / "T4" / "task.json"
        for sentinel, payload in (
            (global_sentinel, b'{"global":true}\n'),
            (sibling_sentinel, b'{"paper_id":"P01"}\n'),
        ):
            sentinel.parent.mkdir(parents=True, exist_ok=True)
            sentinel.write_bytes(payload)
        sentinel_bytes = {
            sentinel: sentinel.read_bytes()
            for sentinel in (global_sentinel, sibling_sentinel)
        }

        with ThreadPoolExecutor(max_workers=2) as executor:
            results = list(
                executor.map(
                    lambda paper_id: manage_t4_metadata(
                        self.root, paper_id, mode="freeze"
                    ),
                    ("P06", "P07"),
                )
            )

        write_sets = [
            {entry["path"] for entry in result["write_set"]} for result in results
        ]
        self.assertTrue(write_sets[0].isdisjoint(write_sets[1]))
        for paper_id, result in zip(("P06", "P07"), results, strict=True):
            relative = f"tasks/{paper_id}/T4/task.json"
            self.assertEqual(result["write_set"], [{"path": relative}])
            self.assertEqual(result["written"], [relative])
            task = json.loads(paths[paper_id].read_text(encoding="utf-8"))
            self.assertEqual(
                task["source_inventory_file"],
                f"paper_bencmark/highambench/tasks/{paper_id}/T4/source_inventory.json",
            )
            self.assertEqual(
                task["construction_inputs"]["review_campaign_status"],
                "replacement_required",
            )
            checked = manage_t4_metadata(self.root, paper_id, mode="check")
            self.assertEqual(checked["written"], [])
        self.assertEqual(
            sentinel_bytes,
            {sentinel: sentinel.read_bytes() for sentinel in sentinel_bytes},
        )
        self.assertEqual(
            list(self.root.rglob(".task.json.t4-metadata-*")),
            [],
        )

    def test_check_detects_tampered_target_without_mutating_metadata(self) -> None:
        task_path = self._stage("P06")
        manage_t4_metadata(self.root, "P06", mode="freeze")
        before = task_path.read_bytes()
        target = self.root / "tasks" / "P06" / "T4" / "Target.lean"
        target.write_text(target.read_text(encoding="utf-8") + "-- tamper\n")

        with self.assertRaisesRegex(BenchmarkToolError, "target_sha256"):
            manage_t4_metadata(self.root, "P06", mode="check")
        self.assertEqual(task_path.read_bytes(), before)

    def test_accepted_campaign_hash_change_fails_closed(self) -> None:
        task_path = self._stage("P06", accepted=True)
        before = task_path.read_bytes()
        definitions = self.root / "shared" / "HighamBench" / "P06Definitions.lean"
        definitions.write_text(
            definitions.read_text(encoding="utf-8") + "-- changed\n",
            encoding="utf-8",
        )

        with self.assertRaisesRegex(BenchmarkToolError, "accepted review campaign"):
            manage_t4_metadata(self.root, "P06", mode="freeze")
        self.assertEqual(task_path.read_bytes(), before)

    def test_rejects_invalid_campaign_status_before_writing(self) -> None:
        task_path = self._stage("P06")
        task = json.loads(task_path.read_text(encoding="utf-8"))
        task["construction_inputs"]["review_campaign_status"] = "finished"
        task_path.write_text(
            json.dumps(task, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        before = task_path.read_bytes()

        with self.assertRaisesRegex(BenchmarkToolError, "review_campaign_status"):
            manage_t4_metadata(self.root, "P06", mode="freeze")
        self.assertEqual(task_path.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
