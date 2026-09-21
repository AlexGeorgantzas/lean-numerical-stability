from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
from design16_audit_batch import (  # noqa: E402
    SCHEMA,
    _batch_core,
    _canonical_hash,
    _load_or_create_manifest,
    _pair_artifact_closure,
    _record_event,
    authenticate_campaign,
    run_batch,
)
from design16_campaign import (  # noqa: E402
    EXPECTED_TASKS,
    SCHEMA as CAMPAIGN_SCHEMA,
    _append_record,
)


def _campaign(
    root: Path,
    *,
    complete: bool = True,
    source_contract: str = "complete-kernel-checked-proof",
) -> tuple[Path, Path]:
    campaign = root / "campaign"
    campaign.mkdir()
    deployment = root / "deployment.json"
    deployment.write_text("{}\n", encoding="utf-8")
    core = {
        "schema_version": CAMPAIGN_SCHEMA,
        "plan": [
            {"task_id": task_id, "condition_order": ["R0", "R1"]}
            for task_id in EXPECTED_TASKS
        ],
        "deployment_path": str(deployment.resolve()),
        "formalizer": {
            "benchmark_object": (
                "FORMALIZED_STATEMENT_ONLY"
                if source_contract == "statement-only-single-target-sorry"
                else "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF"
            ),
            "source_contract": source_contract,
        },
    }
    import hashlib
    from common import canonical_json_bytes

    identity = hashlib.sha256(canonical_json_bytes(core)).hexdigest()
    manifest = {
        "campaign_core": core,
        "campaign_identity_sha256": identity,
        "campaign_nonce": "a" * 64,
        "created_at_utc": "test",
    }
    manifest["manifest_payload_sha256"] = hashlib.sha256(
        canonical_json_bytes(manifest)
    ).hexdigest()
    (campaign / "campaign-manifest.json").write_text(
        json.dumps(manifest) + "\n", encoding="utf-8"
    )

    completed_task = "H5-5"
    pair_report_path: Path | None = None
    pair_report: dict[str, object] | None = None
    pair_root = campaign / "tasks" / completed_task / "pair"
    for condition in ("R0", "R1"):
        condition_root = pair_root / condition
        source = condition_root / "workspace" / "source"
        source.mkdir(parents=True)
        candidate = condition_root / "submissions" / "01" / "Candidate.lean"
        candidate.parent.mkdir(parents=True)
        candidate.write_text(
            "theorem HighamBenchCandidate.target : True := by\n  sorry\n",
            encoding="utf-8",
        )
        (source / "paper.pdf").write_bytes(b"%PDF-identical-test")
        (source / "task.md").write_text("frozen source packet\n", encoding="utf-8")
        condition_report = {
            "schema_version": "formalization-design17-matched-condition-2",
            "task_id": completed_task,
            "condition": condition,
            "result_status": "COMPILED_AND_INTEGRITY_VALIDATED",
            "validation_pass": True,
            "candidate_sha256": sha256_file(candidate),
            "candidate": {
                "path": str(candidate.resolve()),
                "sha256": sha256_file(candidate),
                "bytes": candidate.stat().st_size,
                "lines": 2,
            },
            "source_contract": source_contract,
        }
        (condition_root / "report.json").write_text(
            json.dumps(condition_report) + "\n", encoding="utf-8"
        )
        if pair_report is None:
            pair_report = {
                "schema_version": "formalization-design17-matched-pair-2",
                "task_id": completed_task,
                "pair_status": "FORMALIZATION_FROZEN_PENDING_AUDIT",
                "source_pdf_sha256": sha256_file(source / "paper.pdf"),
                "source_contract": source_contract,
                "condition_reports": {},
            }
        pair_report["condition_reports"][condition] = condition_report  # type: ignore[index]
    pair_report_path = pair_root / "pair-report.json"
    pair_report_path.write_text(json.dumps(pair_report) + "\n", encoding="utf-8")
    task_root = pair_root.parent
    stdout_path = task_root / "runner.stdout.log"
    stderr_path = task_root / "runner.stderr.log"
    stdout_path.write_text("runner stdout\n", encoding="utf-8")
    stderr_path.write_text("", encoding="utf-8")
    closure = _pair_artifact_closure(pair_root)
    closure_sha256 = _canonical_hash({"files": closure})
    pair_nonce = "b" * 64
    attestation = {
        "schema_version": "formalization-design16-campaign-pair-attestation-1",
        "campaign_identity_sha256": identity,
        "campaign_nonce": manifest["campaign_nonce"],
        "pair_nonce": pair_nonce,
        "task_id": completed_task,
        "condition_order": ["R0", "R1"],
        "benchmark_object": core["formalizer"]["benchmark_object"],
        "source_contract": source_contract,
        "pair_status": pair_report["pair_status"],
        "pair_report_sha256": sha256_file(pair_report_path),
        "pair_artifact_closure": closure,
        "pair_artifact_closure_sha256": closure_sha256,
        "runner_return_code": 0,
        "runner_stdout_sha256": sha256_file(stdout_path),
        "runner_stderr_sha256": sha256_file(stderr_path),
        "created_at_utc": "test",
    }
    attestation_path = task_root / "campaign-pair-attestation.json"
    attestation_path.write_text(json.dumps(attestation) + "\n", encoding="utf-8")

    state = campaign / "campaign-state.jsonl"
    events: list[dict[str, object]] = []

    def event(value: dict[str, object]) -> None:
        events.append(
            _append_record(
                state,
                {**value, "schema_version": CAMPAIGN_SCHEMA, "recorded_at_utc": "test"},
            )
        )

    event({"event_type": "CAMPAIGN_STARTED", "outcome": "RUNNING"})
    for task_id in EXPECTED_TASKS:
        started = {"event_type": "TASK_STARTED", "task_id": task_id, "outcome": "RUNNING"}
        if task_id == completed_task:
            started.update(
                {
                    "condition_order": ["R0", "R1"],
                    "campaign_identity_sha256": identity,
                    "campaign_nonce": manifest["campaign_nonce"],
                    "pair_nonce": pair_nonce,
                    "benchmark_object": core["formalizer"]["benchmark_object"],
                    "source_contract": source_contract,
                }
            )
        event(started)
        if task_id == completed_task:
            event(
                {
                    "event_type": "TASK_FORMALIZATION_COMPLETE",
                    "task_id": task_id,
                    "outcome": (
                        "FORMALIZATION_COMPLETE_AUDIT_PENDING"
                        if source_contract == "complete-kernel-checked-proof"
                        else "AUDITED_FAITHFUL_PAIR"
                    ),
                    "details": {
                        "pair_report_sha256": sha256_file(pair_report_path),
                        "pair_attestation_sha256": sha256_file(attestation_path),
                        "pair_artifact_closure_sha256": closure_sha256,
                    },
                }
            )
        else:
            event(
                {
                    "event_type": "TASK_INCIDENT",
                    "task_id": task_id,
                    "outcome": "INCIDENT",
                    "details": {"reason": "fixture incident"},
                }
            )
    if complete:
        event(
            {
                "event_type": "CAMPAIGN_FORMALIZATION_COMPLETE",
                "outcome": "FORMALIZATION_COMPLETE_WITH_INCIDENTS",
            }
        )

    summary = campaign / "campaign-summary.jsonl"
    for index, item in enumerate(events, 1):
        _append_record(
            summary,
            {
                "schema_version": CAMPAIGN_SCHEMA,
                "latest_state_sequence": index,
                "latest_state_sha256": item["record_sha256"],
            },
        )
    return campaign, deployment


def _audit_runner(root: Path) -> Path:
    runner = root / "fake_audit.py"
    runner.write_text("# fake audit runner\n", encoding="utf-8")
    return runner


def _args(root: Path, campaign: Path, deployment: Path) -> argparse.Namespace:
    return argparse.Namespace(
        campaign_root=campaign,
        deployment=deployment,
        output_root=root / "audit-batch",
        audit_runner=_audit_runner(root),
        max_parallel=2,
        model="gpt-6-astra",
        reasoning_effort="high",
        timeout_seconds=7200,
        validation_timeout_seconds=600,
        infrastructure_retries=2,
    )


class FakeAuditRunner:
    def __init__(
        self,
        *,
        failing_compiler_condition: str | None = None,
        unfaithful_compiler_condition: str | None = None,
    ) -> None:
        self.failing = failing_compiler_condition
        self.unfaithful = unfaithful_compiler_condition
        self.commands: list[list[str]] = []
        self._lock = threading.Lock()
        self._active = 0
        self.maximum_active = 0

    def __call__(self, command: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        with self._lock:
            self.commands.append(command)
            self._active += 1
            self.maximum_active = max(self.maximum_active, self._active)
        try:
            time.sleep(0.04)
            values = {
                command[index][2:]: command[index + 1]
                for index in range(len(command) - 1)
                if command[index].startswith("--")
            }
            if values["condition"] == self.failing:
                return subprocess.CompletedProcess(command, 9)
            output = Path(values["output-root"])
            output.mkdir(parents=True)
            result = {
                "schema_version": "formalization-design16-full-audit-run-1",
                "scientific_status": "CANONICAL_MULTI_ROLE_FAITHFULNESS_AUDIT",
                "task_id": values["task-id"],
                "candidate_sha256": sha256_file(Path(values["candidate"])),
                "source_contract": (
                    "statement-only-single-target-sorry"
                    if "--statement-only" in command
                    else "complete-kernel-checked-proof"
                ),
                "output_root": str(output.resolve()),
                "condition_blind": True,
                "attempt_blind": True,
                "decision": {
                    "verdict": (
                        "unfaithful"
                        if values["condition"] == self.unfaithful
                        else "faithful"
                    ),
                    "accepted": values["condition"] != self.unfaithful,
                },
            }
            (output / "result.json").write_text(
                json.dumps(result) + "\n", encoding="utf-8"
            )
            return subprocess.CompletedProcess(command, 0)
        finally:
            with self._lock:
                self._active -= 1


class Design16AuditBatchTests(unittest.TestCase):
    def test_refuses_running_campaign_before_auditor_calls(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(root, complete=False)
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner()
            with self.assertRaisesRegex(BenchmarkError, "RUNNING"):
                run_batch(args, process_runner=runner)
            self.assertEqual(runner.commands, [])
            self.assertFalse(args.output_root.exists())

    def test_refuses_tampered_pair_closure_before_auditor_calls(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(root)
            candidate = (
                campaign
                / "tasks"
                / "H5-5"
                / "pair"
                / "R0"
                / "submissions"
                / "01"
                / "Candidate.lean"
            )
            candidate.chmod(0o600)
            candidate.write_text("theorem HighamBenchCandidate.target : False := by sorry\n")
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner()
            with self.assertRaisesRegex(BenchmarkError, "attestation changed"):
                run_batch(args, process_runner=runner)
            self.assertEqual(runner.commands, [])

    def test_only_completed_pair_is_audited_with_mapping_and_bounded_parallelism(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(root)
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner()
            summary = run_batch(args, process_runner=runner)
            self.assertEqual(summary["eligible_job_count"], 2)
            self.assertEqual(summary["audited_count"], 2)
            self.assertEqual(summary["scientifically_eligible_count"], 2)
            self.assertEqual(summary["incident_count"], 0)
            self.assertEqual(len(runner.commands), 2)
            self.assertLessEqual(runner.maximum_active, 2)
            self.assertEqual(runner.maximum_active, 2)
            mapping = {
                Path(command[command.index("--output-root") + 1]).name:
                command[command.index("--condition") + 1]
                for command in runner.commands
            }
            self.assertEqual(mapping, {"R0": "N", "R1": "L"})
            self.assertTrue(
                all("--statement-only" not in command for command in runner.commands)
            )
            self.assertTrue((args.output_root / "audits" / "H5-5" / "R0").is_dir())
            self.assertTrue((args.output_root / "audits" / "H5-5" / "R1").is_dir())

    def test_complete_proof_contract_omits_statement_only_flag(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(
                root, source_contract="complete-kernel-checked-proof"
            )
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner()
            run_batch(args, process_runner=runner)
            self.assertTrue(all("--statement-only" not in command for command in runner.commands))

    def test_already_audited_statement_pair_is_skipped(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(
                root, source_contract="statement-only-single-target-sorry"
            )
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner()
            summary = run_batch(args, process_runner=runner)
            self.assertEqual(summary["eligible_job_count"], 0)
            self.assertEqual(summary["audited_count"], 0)
            self.assertEqual(runner.commands, [])

    def test_incident_does_not_stop_batch_and_resume_never_reruns(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(root)
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner(failing_compiler_condition="N")
            first = run_batch(args, process_runner=runner)
            self.assertEqual(first["audited_count"], 1)
            self.assertEqual(first["scientifically_eligible_count"], 1)
            self.assertEqual(first["incident_count"], 1)
            self.assertEqual(len(runner.commands), 2)
            state = args.output_root / "audit-state.jsonl"
            before = state.read_bytes()
            second = run_batch(args, process_runner=runner)
            self.assertEqual(first, second)
            self.assertEqual(len(runner.commands), 2)
            self.assertEqual(before, state.read_bytes())

    def test_unfaithful_audit_is_scientifically_ineligible_not_incident(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign, deployment = _campaign(root)
            args = _args(root, campaign, deployment)
            runner = FakeAuditRunner(unfaithful_compiler_condition="L")
            summary = run_batch(args, process_runner=runner)
            self.assertEqual(summary["audited_count"], 2)
            self.assertEqual(summary["scientifically_eligible_count"], 1)
            self.assertEqual(summary["scientifically_ineligible_count"], 1)
            self.assertEqual(summary["incident_count"], 0)

    def test_resume_reconciles_started_result_and_runs_only_pending_job(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            campaign_root, deployment = _campaign(root)
            args = _args(root, campaign_root, deployment)
            campaign = authenticate_campaign(campaign_root)
            core = _batch_core(args, campaign)
            args.output_root.mkdir()
            _load_or_create_manifest(args.output_root, core)
            _record_event(
                args.output_root,
                {"event_type": "BATCH_STARTED", "outcome": "RUNNING"},
            )
            job = campaign["jobs"][0]
            output = args.output_root / "audits" / job["task_id"] / job["condition"]
            _record_event(
                args.output_root,
                {
                    "event_type": "AUDIT_STARTED",
                    "job_id": job["job_id"],
                    "task_id": job["task_id"],
                    "outcome": "RUNNING",
                },
            )
            output.mkdir(parents=True)
            (output / "result.json").write_text(
                json.dumps(
                    {
                        "schema_version": "formalization-design16-full-audit-run-1",
                        "scientific_status": "CANONICAL_MULTI_ROLE_FAITHFULNESS_AUDIT",
                        "task_id": job["task_id"],
                        "candidate_sha256": job["candidate_sha256"],
                        "source_contract": job["source_contract"],
                        "output_root": str(output.resolve()),
                        "condition_blind": True,
                        "attempt_blind": True,
                        "decision": {"verdict": "faithful", "accepted": True},
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            runner = FakeAuditRunner()
            summary = run_batch(args, process_runner=runner)
            self.assertEqual(summary["audited_count"], 2)
            self.assertEqual(len(runner.commands), 1)
            self.assertEqual(
                runner.commands[0][runner.commands[0].index("--condition") + 1], "L"
            )


if __name__ == "__main__":
    unittest.main()
