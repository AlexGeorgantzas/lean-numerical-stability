from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
import design16_campaign as campaign_module  # noqa: E402
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
    'maximum-packet-bytes', 'submission-limit', 'audit-model',
    'audit-reasoning-effort', 'audit-timeout-seconds',
    'audit-infrastructure-retries',
)
for name in names:
    p.add_argument('--' + name, required=True)
a = p.parse_args()
root = Path(a.output_root)
root.mkdir(parents=True)
failed = a.task_id == 'H22-5'
prompt = root / 'prompt.txt'
prompt.write_text('frozen prompt')
prompt_sha = __import__('hashlib').sha256(prompt.read_bytes()).hexdigest()
condition_reports = {}
for condition in ('R0', 'R1'):
    condition_root = root / condition
    workspace = condition_root / 'workspace'
    source = workspace / 'source'
    source.mkdir(parents=True)
    candidate = workspace / 'Candidate.lean'
    candidate.write_text('theorem test : True := by trivial\\n')
    candidate_sha = __import__('hashlib').sha256(candidate.read_bytes()).hexdigest()
    library_api = workspace / 'LIBRARY_API.md'
    library_api.write_text('api')
    composition = condition_root / 'composition-packet.json'
    composition.write_text('{}')
    (source / 'paper.pdf').write_bytes(b'pdf')
    (source / 'task.md').write_text('task')
    (condition_root / 'validation.json').write_text(json.dumps({'pass': True}))
    report_condition = {
        'task_id': a.task_id,
        'condition': condition,
        'benchmark_object': 'FORMALIZED_STATEMENT_AND_COMPLETE_PROOF',
        'source_contract': 'complete-kernel-checked-proof',
        'faithfulness_status': 'NOT_AUDITED',
        'result_status': 'COMPILED_AND_INTEGRITY_VALIDATED',
        'validation_pass': True,
        'prompt_sha256': prompt_sha,
        'candidate_sha256': candidate_sha,
        'composition_packet_sha256': __import__('hashlib').sha256(composition.read_bytes()).hexdigest(),
        'library_api_sha256': __import__('hashlib').sha256(library_api.read_bytes()).hexdigest(),
        'source_packet_sha256': 'a' * 64,
    }
    (condition_root / 'report.json').write_text(json.dumps(report_condition))
    condition_reports[condition] = report_condition
report = {
    'task_id': a.task_id,
    'pair_status': 'PAIR_INCIDENT' if failed else 'COMPILED_UNAUDITED',
    'condition_order': a.condition_order.split(','),
    'conditions_run_sequentially': True,
    'benchmark_object': 'FORMALIZED_STATEMENT_AND_COMPLETE_PROOF',
    'source_contract': 'complete-kernel-checked-proof',
    'faithfulness_status': 'NOT_AUDITED',
    'prompt_sha256': prompt_sha,
    'source_packet_sha256': 'a' * 64,
    'source_pdf_sha256': __import__('hashlib').sha256(b'pdf').hexdigest(),
    'condition_reports': condition_reports,
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
        controller_commit=None,
        controller_sha256=None,
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
        submission_limit=4,
        audit_model="gpt-6-astra",
        audit_reasoning_effort="high",
        audit_timeout_seconds=7200.0,
        audit_infrastructure_retries=2,
        max_new_tasks=None,
        wave_task_ids=None,
        enforce_titan_envelope=False,
        statement_only=False,
        dry_run=dry_run,
    )


def _rewind_last_terminal(campaign_root: Path) -> None:
    for name in ("campaign-state.jsonl", "campaign-summary.jsonl"):
        path = campaign_root / name
        lines = path.read_text(encoding="utf-8").splitlines()
        path.write_text("\n".join(lines[:-1]) + "\n", encoding="utf-8")


class Design16CampaignTests(unittest.TestCase):
    def setUp(self) -> None:
        closure = {"test_only_frozen_input_closure": True}
        closure["closure_sha256"] = campaign_module._canonical_hash(closure)
        self._closure_patch = patch.object(
            campaign_module,
            "_frozen_input_closure",
            return_value=closure,
        )
        self._closure_patch.start()

    def tearDown(self) -> None:
        self._closure_patch.stop()

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
            self.assertEqual(
                sum(
                    stratum["formalization_complete_audit_pending_count"]
                    for stratum in wave["strata"].values()
                ),
                2,
            )
            self.assertEqual(
                sum(stratum["completed_count"] for stratum in wave["strata"].values()),
                0,
            )
            wave_pending = sum(
                stratum["pending_count"] for stratum in wave["strata"].values()
            )
            self.assertEqual(wave_pending, 10)
            self.assertFalse(
                any(
                    event["event_type"] == "CAMPAIGN_FORMALIZATION_COMPLETE"
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

    def test_recovery_requires_and_verifies_campaign_pair_attestation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 1
            run_campaign(args)
            manifest = json.loads(
                (args.campaign_root / "campaign-manifest.json").read_text(encoding="utf-8")
            )
            self.assertRegex(manifest["campaign_nonce"], r"^[0-9a-f]{64}$")
            attestation = (
                args.campaign_root / "tasks" / "H22-11" / "campaign-pair-attestation.json"
            )
            self.assertTrue(attestation.is_file())
            _rewind_last_terminal(args.campaign_root)
            run_campaign(args)
            events = _read_journal(args.campaign_root / "campaign-state.jsonl")
            self.assertEqual(events[-1]["event_type"], "TASK_RECOVERED_FORMALIZATION_COMPLETE")
            self.assertEqual(events[-1]["outcome"], "FORMALIZATION_COMPLETE_AUDIT_PENDING")
            self.assertEqual(
                events[-1]["details"]["pair_attestation_sha256"], sha256_file(attestation)
            )

    def test_recovery_fails_closed_after_frozen_candidate_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 1
            run_campaign(args)
            _rewind_last_terminal(args.campaign_root)
            candidate = (
                args.campaign_root
                / "tasks"
                / "H22-11"
                / "pair"
                / "R0"
                / "workspace"
                / "Candidate.lean"
            )
            candidate.write_text("theorem altered : False := by contradiction\n")
            run_campaign(args)
            events = _read_journal(args.campaign_root / "campaign-state.jsonl")
            self.assertEqual(events[-1]["event_type"], "TASK_RECOVERED_INCIDENT")
            self.assertEqual(events[-1]["outcome"], "INCIDENT")
            self.assertIn("candidate is absent, unsafe, or stale", events[-1]["details"]["reason"])

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

    def test_statement_only_mode_is_frozen_and_passed_to_every_condition(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            args.statement_only = True
            args.wave_task_ids = ["H5-5"]
            result = run_campaign(args)
            self.assertIn("--statement-only", result["commands"][0])

    def test_statement_only_non_dry_run_requires_titan_envelope(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            args = _args(Path(raw), dry_run=False)
            args.statement_only = True
            with self.assertRaisesRegex(BenchmarkError, "require --enforce-titan-envelope"):
                run_campaign(args)

    def test_statement_pair_requires_audited_faithful_condition_closure(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            pair_root = Path(raw) / "pair"
            pair_root.mkdir()
            prompt = pair_root / "prompt.txt"
            prompt.write_text("statement prompt", encoding="utf-8")
            reports: dict[str, dict[str, object]] = {}
            for condition in ("R0", "R1"):
                condition_root = pair_root / condition
                source = condition_root / "workspace" / "source"
                source.mkdir(parents=True)
                (source / "paper.pdf").write_bytes(b"paper")
                (source / "task.md").write_text("task", encoding="utf-8")
                api = condition_root / "workspace" / "LIBRARY_API.md"
                api.write_text("api", encoding="utf-8")
                composition = condition_root / "composition-packet.json"
                composition.write_text("{}", encoding="utf-8")
                attempt_root = condition_root / "submissions" / "01"
                attempt_root.mkdir(parents=True)
                candidate = attempt_root / "Candidate.lean"
                candidate.write_text(
                    "theorem HighamBenchCandidate.target : True := by sorry\n",
                    encoding="utf-8",
                )
                validation = attempt_root / "validation.json"
                validation.write_text(json.dumps({"pass": True}), encoding="utf-8")
                candidate_record = {
                    "path": str(candidate),
                    "sha256": sha256_file(candidate),
                    "bytes": candidate.stat().st_size,
                    "lines": 1,
                }
                attempt = {
                    "attempt": 1,
                    "candidate": candidate_record,
                    "validation_sha256": sha256_file(validation),
                    "hardware_after": {"strict": True},
                    "status": "ACCEPTED_FAITHFUL",
                }
                report = {
                    "task_id": "H5-5",
                    "condition": condition,
                    "benchmark_object": "FORMALIZED_STATEMENT_ONLY",
                    "source_contract": "statement-only-single-target-sorry",
                    "faithfulness_status": "FAITHFUL",
                    "result_status": "ACCEPTED_FAITHFUL",
                    "attempts": [attempt],
                    "submission_count": 1,
                    "hardware_envelope_required": True,
                    "hardware_snapshot": {"strict": True},
                    "candidate": candidate_record,
                    "candidate_sha256": sha256_file(candidate),
                    "composition_packet_sha256": sha256_file(composition),
                    "library_api_sha256": sha256_file(api),
                    "source_pdf_sha256": sha256_file(source / "paper.pdf"),
                    "staged_task_sha256": sha256_file(source / "task.md"),
                }
                (condition_root / "report.json").write_text(
                    json.dumps(report), encoding="utf-8"
                )
                reports[condition] = report
            pair_report = {
                "task_id": "H5-5",
                "condition_order": ["R0", "R1"],
                "conditions_run_sequentially": True,
                "benchmark_object": "FORMALIZED_STATEMENT_ONLY",
                "source_contract": "statement-only-single-target-sorry",
                "faithfulness_status": "BOTH_FAITHFUL",
                "pair_status": "AUDITED_FAITHFUL_PAIR",
                "prompt_sha256": sha256_file(prompt),
                "source_packet_sha256": "a" * 64,
                "source_pdf_sha256": hashlib.sha256(b"paper").hexdigest(),
                "condition_reports": reports,
            }
            (pair_root / "pair-report.json").write_text(
                json.dumps(pair_report), encoding="utf-8"
            )
            outcome, details = campaign_module._inspect_pair(
                pair_root,
                task_id="H5-5",
                condition_order=["R0", "R1"],
                statement_only=True,
                require_titan_envelope=True,
            )
            self.assertEqual(outcome, "AUDITED_FAITHFUL_PAIR")
            self.assertRegex(details["pair_artifact_closure_sha256"], r"^[0-9a-f]{64}$")


if __name__ == "__main__":
    unittest.main()
