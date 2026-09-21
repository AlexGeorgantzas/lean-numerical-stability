from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
from design16_campaign import (  # noqa: E402
    EXPECTED_STRATA,
    EXPECTED_TASKS,
    _append_record,
    _read_journal,
    load_plan,
    run_campaign,
)


CONFIG = ROOT / "config.json"
READINESS = ROOT / "design16" / "higham13_readiness.json"


def _git_runner(root: Path) -> tuple[Path, str, str]:
    repository = root / "repo"
    repository.mkdir()
    runner = repository / "fake_runner.py"
    runner.write_text(
        """#!/usr/bin/env python3
import argparse, json
from pathlib import Path
p = argparse.ArgumentParser()
names = (
    'deployment', 'mathlib-atlas', 'task-id', 'condition-order',
    'output-root', 'model', 'reasoning-effort', 'time-limit-seconds',
    'validation-timeout-seconds', 'root-limit', 'dependency-limit',
    'maximum-packet-bytes',
)
for name in names:
    p.add_argument('--' + name, required=True)
a = p.parse_args()
root = Path(a.output_root)
root.mkdir(parents=True)
failed = a.task_id == 'H22-5'
report = {
    'task_id': a.task_id,
    'pair_status': 'PAIR_INCIDENT' if failed else 'COMPILED_UNAUDITED',
}
(root / 'pair-report.json').write_text(json.dumps(report))
raise SystemExit(7 if failed else 0)
""",
        encoding="utf-8",
    )
    subprocess.run(["git", "init", "-q", str(repository)], check=True)
    subprocess.run(["git", "-C", str(repository), "add", "fake_runner.py"], check=True)
    subprocess.run(
        [
            "git",
            "-C",
            str(repository),
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.invalid",
            "commit",
            "-qm",
            "runner",
        ],
        check=True,
    )
    commit = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    return runner, commit, sha256_file(runner)


def _atlas(root: Path) -> Path:
    atlas = root / "mathlib-atlas"
    atlas.mkdir()
    declarations = atlas / "declarations.jsonl"
    declarations.write_text(
        json.dumps({"name": "Mathlib.sample", "module": "Mathlib"}) + "\n",
        encoding="utf-8",
    )
    (atlas / "atlas.json").write_text(
        json.dumps(
            {
                "schema_version": "numstability-library-atlas-2",
                "declaration_count": 1,
                "declarations_sha256": sha256_file(declarations),
            }
        ),
        encoding="utf-8",
    )
    return atlas


def _args(root: Path, *, dry_run: bool) -> argparse.Namespace:
    runner, commit, digest = _git_runner(root)
    return argparse.Namespace(
        deployment=root / "deployment.json",
        mathlib_atlas=_atlas(root),
        campaign_root=root / "campaign",
        runner=runner,
        runner_commit=commit,
        runner_sha256=digest,
        config=CONFIG,
        readiness=READINESS,
        host_lock=root / "host.lock",
        model="gpt-5.6-sol",
        reasoning_effort="xhigh",
        time_limit_seconds=18000,
        validation_timeout_seconds=600,
        root_limit=3,
        dependency_limit=5,
        maximum_packet_bytes=48 * 1024,
        max_new_tasks=None,
        wave_task_ids=None,
        dry_run=dry_run,
    )


class Design16CampaignTests(unittest.TestCase):
    def test_plan_preserves_alternation_and_exact_strata(self) -> None:
        plan = load_plan(CONFIG, READINESS)
        self.assertEqual(tuple(item["task_id"] for item in plan), EXPECTED_TASKS)
        self.assertEqual(plan[0]["condition_order"], ["R1", "R0"])
        self.assertEqual(plan[1]["condition_order"], ["R0", "R1"])
        for left, right in zip(plan, plan[1:]):
            self.assertNotEqual(left["condition_order"], right["condition_order"])
        observed = {
            stratum: tuple(item["task_id"] for item in plan if item["stratum"] == stratum)
            for stratum in EXPECTED_STRATA
        }
        self.assertEqual(observed, EXPECTED_STRATA)

    def test_hash_chained_journal_detects_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "journal.jsonl"
            _append_record(path, {"event_type": "ONE"})
            _append_record(path, {"event_type": "TWO"})
            self.assertEqual(len(_read_journal(path)), 2)
            lines = path.read_text(encoding="utf-8").splitlines()
            first = json.loads(lines[0])
            first["event_type"] = "ALTERED"
            lines[0] = json.dumps(first, sort_keys=True, separators=(",", ":"))
            path.chmod(0o600)
            path.write_text("\n".join(lines) + "\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                _read_journal(path)

    def test_dry_run_performs_no_campaign_writes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            result = run_campaign(args)
            self.assertTrue(result["dry_run"])
            self.assertFalse(result["writes_performed"])
            self.assertEqual(len(result["commands"]), 13)
            self.assertFalse(args.campaign_root.exists())

    def test_incident_continues_and_resume_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 3
            wave = run_campaign(args)
            wave_pending = sum(
                stratum["pending_count"] for stratum in wave["strata"].values()
            )
            self.assertEqual(wave_pending, 10)
            self.assertFalse(
                any(
                    event["event_type"] == "CAMPAIGN_COMPLETED"
                    for event in _read_journal(
                        args.campaign_root / "campaign-state.jsonl"
                    )
                )
            )
            args.max_new_tasks = None
            first = run_campaign(args)
            self.assertEqual(
                first["strata"]["excluded_collision_or_router_error"]["incident_task_ids"],
                ["H22-5"],
            )
            self.assertIsNone(first["pooled_effect_estimate"])
            state_path = args.campaign_root / "campaign-state.jsonl"
            before = state_path.read_bytes()
            second = run_campaign(args)
            self.assertEqual(before, state_path.read_bytes())
            self.assertEqual(first["strata"], second["strata"])
            terminals = [
                event
                for event in _read_journal(state_path)
                if event["event_type"].startswith("TASK_")
                and event["event_type"] != "TASK_STARTED"
            ]
            self.assertEqual(len(terminals), 13)
            self.assertTrue((args.campaign_root / "tasks" / "H15-3" / "pair").is_dir())

    def test_wave_subset_preserves_requested_task_order_and_frozen_condition_orders(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            args.wave_task_ids = ["H5-5", "H10-7", "H7-12"]
            result = run_campaign(args)
            self.assertEqual(
                [item["task_id"] for item in result["invocation_plan"]],
                ["H5-5", "H10-7", "H7-12"],
            )
            self.assertEqual(
                [item["condition_order"] for item in result["invocation_plan"]],
                [["R0", "R1"], ["R1", "R0"], ["R0", "R1"]],
            )
            self.assertFalse(args.campaign_root.exists())

    def test_wave_subset_rejects_duplicates(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            args.wave_task_ids = ["H5-5", "H5-5"]
            with self.assertRaises(BenchmarkError):
                run_campaign(args)


if __name__ == "__main__":
    unittest.main()
