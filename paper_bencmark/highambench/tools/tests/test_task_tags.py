from __future__ import annotations

import copy
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, write_json  # noqa: E402
from task_tags import (  # noqa: E402
    ALLOWED_SOURCE_TAGS,
    main,
    validate_task_catalog,
    validate_task_source_tags,
)


def base_task() -> dict:
    return {
        "schema_version": "highambench-task-0.3",
        "task_id": "P03-T1",
        "source_tags": ["EQN", "TXT"],
        "author_label": None,
        "classification_frozen_before_runs": False,
        "source_locations": [{"anchor": "equation (2.1) and following text"}],
    }


class TaskTagTests(unittest.TestCase):
    def test_allowed_vocabulary_is_compact_and_fixed(self) -> None:
        self.assertEqual(
            ALLOWED_SOURCE_TAGS,
            ("THM", "LEM", "PROP", "COR", "EQN", "TXT", "UNL"),
        )

    def test_accepts_numbered_equation_with_essential_prose(self) -> None:
        result = validate_task_source_tags(base_task())
        self.assertEqual(result["source_tags"], ["EQN", "TXT"])
        self.assertIsNone(result["author_label"])

    def test_accepts_explicit_proposition_with_exact_label(self) -> None:
        task = base_task()
        task["source_tags"] = ["PROP"]
        task["author_label"] = "Proposition 4.5"
        result = validate_task_source_tags(task)
        self.assertEqual(result["author_label"], "Proposition 4.5")

        task["source_tags"] = ["THM"]
        task["author_label"] = "THEOREM 3.4"
        result = validate_task_source_tags(task)
        self.assertEqual(result["author_label"], "THEOREM 3.4")

    def test_rejects_malformed_tag_metadata(self) -> None:
        cases = {
            "old schema": {"schema_version": "highambench-task-0.2"},
            "missing tags": {"source_tags": None},
            "unknown tag": {"source_tags": ["OTHER"]},
            "duplicate": {"source_tags": ["EQN", "EQN"]},
            "wrong order": {"source_tags": ["TXT", "EQN"]},
            "named mixed with equation": {
                "source_tags": ["THM", "EQN"],
                "author_label": "Theorem 2.1",
            },
            "named without label": {"source_tags": ["LEM"], "author_label": None},
            "wrong named label": {
                "source_tags": ["COR"],
                "author_label": "Theorem 5.1",
            },
            "label on equation": {
                "source_tags": ["EQN"],
                "author_label": "Equation 2.1",
            },
            "numbered and unnumbered": {"source_tags": ["EQN", "UNL"]},
            "invalid construction state": {"classification_frozen_before_runs": "no"},
            "no evidence": {"source_locations": []},
        }
        for name, changes in cases.items():
            with self.subTest(name=name):
                task = copy.deepcopy(base_task())
                task.update(changes)
                with self.assertRaises(BenchmarkToolError):
                    validate_task_source_tags(task)

    def test_catalog_checks_path_identity_and_cli(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            task_path = root / "tasks" / "P03" / "T1" / "task.json"
            write_json(task_path, base_task())
            result = validate_task_catalog(root)
            self.assertEqual(result["task_count"], 1)
            self.assertEqual(main(["--benchmark-root", str(root)]), 0)

            changed = base_task()
            changed["task_id"] = "P99-T1"
            write_json(task_path, changed)
            with self.assertRaises(BenchmarkToolError):
                validate_task_catalog(root)

    def test_real_catalog_has_tags_for_all_current_tasks(self) -> None:
        result = validate_task_catalog(TOOLS.parent)
        paths = sorted((TOOLS.parent / "tasks").glob("P*/T*/task.json"))
        self.assertEqual(result["task_count"], len(paths))
        self.assertGreater(result["task_count"], 0)
        self.assertTrue(all(row["source_tags"] for row in result["tasks"]))
