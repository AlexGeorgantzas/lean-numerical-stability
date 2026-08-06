from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import read_json, sha256_file, write_json  # noqa: E402
from refresh_snapshot import (  # noqa: E402
    PHASE_CONSTRUCTION,
    PHASE_MEASUREMENT_READY,
    refresh_snapshot,
)
from run_matrix import environment_bundle_digest  # noqa: E402


class RefreshSnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name) / "benchmark"
        (self.root / "metadata").mkdir(parents=True)
        (self.root / "shared" / "HighamBench").mkdir(parents=True)
        (self.root / "shared" / "HighamBench" / "Core.lean").write_text(
            "namespace HighamBench\nend HighamBench\n", encoding="utf-8"
        )
        for paper_id in ("P07", "P12"):
            (self.root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean").write_text(
                "import HighamBench.Core\n", encoding="utf-8"
            )
        (self.root / "agent_prompt.md").write_text("prove the task\n", encoding="utf-8")

        papers = []
        for paper_id, tier, digest in (
            ("P07", "T1", "7" * 64),
            ("P12", "T3", "c" * 64),
        ):
            task_id = f"{paper_id}-{tier}"
            task_root = self.root / "tasks" / paper_id / tier
            task_root.mkdir(parents=True)
            (task_root / "Target.lean").write_text(
                f"namespace HighamBench\ntheorem {paper_id.lower()}_{tier.lower()} : True := by sorry\nend HighamBench\n",
                encoding="utf-8",
            )
            (task_root / "context.md").write_text("paper context\n", encoding="utf-8")
            write_json(
                task_root / "task.json",
                {
                    "schema_version": "highambench-task-0.3",
                    "task_id": task_id,
                    "paper_id": paper_id,
                    "tier": tier,
                    "source_tags": ["EQN"],
                    "author_label": None,
                    "classification_frozen_before_runs": True,
                    "source_locations": [{"anchor": "equation (1.1)"}],
                },
            )
            write_json(
                self.root / "tasks" / paper_id / "paper.json",
                {
                    "paper_id": paper_id,
                    "source": {"sha256": digest},
                    "classification_frozen_before_runs": True,
                    "included_tasks": [task_id],
                },
            )
            papers.append(
                {
                    "paper_id": paper_id,
                    "source": {"sha256": digest},
                    "targets": [
                        {
                            "task_id": task_id,
                            "tier": tier,
                            "availability": "available",
                            "lean_target": {
                                "declaration": f"{paper_id.lower()}_{tier.lower()}",
                                "file": f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/Target.lean",
                            },
                        }
                    ],
                }
            )

        write_json(
            self.root / "metadata" / "manifest.json",
            {
                "benchmark_id": "stale-id",
                "specification": {"version": "0.2"},
                "corpus": {"paper_count": 0, "paper_ids": []},
                "controlled_shared_files": [
                    {
                        "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                        "paper_ids": ["P07", "P12"],
                    },
                    {
                        "path": "paper_bencmark/highambench/shared/HighamBench/P07Definitions.lean",
                        "paper_ids": ["P07"],
                    },
                    {
                        "path": "paper_bencmark/highambench/shared/HighamBench/P12Definitions.lean",
                        "paper_ids": ["P12"],
                    },
                ],
                "papers": papers,
            },
        )
        write_json(
            self.root / "metadata" / "config.json",
            {
                "benchmark_id": "stale-id",
                "frozen_environment": {},
                "repetitions": [{"id": "rep-a"}, {"id": "rep-b"}],
            },
        )
        write_json(self.root / "metadata" / "environment.json", {})

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_one_workflow_refreshes_arbitrary_paper_ids_and_both_phases(self) -> None:
        first = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        self.assertEqual(first["paper_ids"], ["P07", "P12"])
        self.assertEqual(first["benchmark_id"], "highambench-0.2-p07-p12")
        self.assertEqual(first["pair_count"], 4)
        self.assertEqual(first["run_count"], 8)

        manifest = read_json(self.root / "metadata" / "manifest.json")
        self.assertEqual(manifest["corpus"]["paper_ids"], ["P07", "P12"])
        self.assertEqual(manifest["corpus"]["paper_count"], 2)
        for paper_id, tier in (("P07", "T1"), ("P12", "T3")):
            task = read_json(self.root / "tasks" / paper_id / tier / "task.json")
            paper = read_json(self.root / "tasks" / paper_id / "paper.json")
            self.assertIs(task["classification_frozen_before_runs"], False)
            self.assertIs(paper["classification_frozen_before_runs"], False)
            self.assertTrue(
                (self.root / "metadata" / "controlled" / f"{paper_id}-{tier}.json").is_file()
            )
            controlled = read_json(
                self.root / "metadata" / "controlled" / f"{paper_id}-{tier}.json"
            )
            controlled_paths = {entry["path"] for entry in controlled["files"]}
            self.assertIn("shared/HighamBench/Core.lean", controlled_paths)
            self.assertIn(
                f"shared/HighamBench/{paper_id}Definitions.lean", controlled_paths
            )
            other = "P12" if paper_id == "P07" else "P07"
            self.assertNotIn(
                f"shared/HighamBench/{other}Definitions.lean", controlled_paths
            )
            target = next(
                item
                for entry in manifest["papers"]
                if entry["paper_id"] == paper_id
                for item in entry["targets"]
            )
            self.assertEqual(
                target["lean_target"]["controlled_file_sha256"],
                sha256_file(self.root / "tasks" / paper_id / tier / "Target.lean"),
            )

        run_order = read_json(self.root / "metadata" / "run_order.json")
        self.assertEqual(len(run_order["pairs"]), 4)
        self.assertEqual(run_order["method"]["version"], 2)
        self.assertNotIn("p01", run_order["method"]["salt"])
        release_paths = {
            item["path"]
            for item in read_json(self.root / "metadata" / "release_files.json")["files"]
        }
        self.assertIn("tasks/P07/T1/task.json", release_paths)
        self.assertIn("tasks/P12/T3/task.json", release_paths)
        self.assertIn("shared/HighamBench/Core.lean", release_paths)
        self.assertIn("shared/HighamBench/P07Definitions.lean", release_paths)
        self.assertIn("shared/HighamBench/P12Definitions.lean", release_paths)

        second = refresh_snapshot(self.root, phase=PHASE_CONSTRUCTION)
        self.assertEqual(second["release_manifest_sha256"], first["release_manifest_sha256"])
        self.assertEqual(second["environment_bundle_sha256"], first["environment_bundle_sha256"])

        with self.assertRaisesRegex(Exception, "passing full-corpus"):
            refresh_snapshot(self.root, phase=PHASE_MEASUREMENT_READY)

        task_ids = ["P07-T1", "P12-T3"]
        write_json(
            self.root / "metadata" / "evidence" / "construction_all.json",
            {
                "kind": "highambench-private-construction-check",
                "record_status": "current_final",
                "pass": True,
                "scope": {
                    "complete_manifest_scope": True,
                    "selected_task_ids": task_ids,
                    "central_manifest_sha256": sha256_file(
                        self.root / "metadata" / "manifest.json"
                    ),
                },
                "summary": {"expected": 4, "checked": 4, "passed": 4},
            },
        )
        for number in (1, 2):
            write_json(
                self.root / "metadata" / "reviews" / f"review_{number}.json",
                {
                    "record_status": "current_final",
                    "task_reviews": [
                        {"task_id": task_id, "outcome": "pass"} for task_id in task_ids
                    ],
                },
            )

        ready = refresh_snapshot(self.root, phase=PHASE_MEASUREMENT_READY)
        self.assertEqual(ready["task_ids"], ["P07-T1", "P12-T3"])
        for paper_id, tier in (("P07", "T1"), ("P12", "T3")):
            task = read_json(self.root / "tasks" / paper_id / tier / "task.json")
            self.assertIs(task["classification_frozen_before_runs"], True)
        config = read_json(self.root / "metadata" / "config.json")
        environment = read_json(self.root / "metadata" / "environment.json")
        self.assertEqual(
            environment["environment_bundle_sha256"],
            environment_bundle_digest(config, environment),
        )


if __name__ == "__main__":
    unittest.main()
