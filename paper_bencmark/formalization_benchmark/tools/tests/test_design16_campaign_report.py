from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
from audit_controller import audit_evidence_manifest  # noqa: E402
from design16_campaign import (  # noqa: E402
    SCHEMA,
    SCIENTIFIC_STATUS,
    _append_record,
    _canonical_hash,
    _pair_artifact_closure,
    _read_journal,
    _summary_payload,
    load_plan,
)
from design16_campaign_report import build_report, write_report  # noqa: E402


CONFIG = ROOT / "config.json"
READINESS = ROOT / "design16" / "higham13_readiness.json"


def _write_audit_result(
    audit_root: Path,
    *,
    task_id: str,
    candidate_sha256: str,
    source_contract: str,
) -> Path:
    audit_root.mkdir(parents=True)
    evidence_root = audit_root / "audit"
    evidence_root.mkdir()
    (evidence_root / "blind_translation.json").write_text(
        json.dumps({"translation": "test"}) + "\n", encoding="utf-8"
    )
    decision = {
        "task_id": task_id,
        "verdict": "faithful",
        "accepted": True,
        "audit_incident": False,
        "classification": "faithful-equivalent",
        "adjudicated": False,
        "implications": {
            "paper_implies_candidate": "yes",
            "candidate_implies_paper": "yes",
        },
        "mismatches": [],
        "audit_wall_seconds": 20.0,
        "auditor_telemetry": [
            {
                "usage": {"total_tokens": 300},
                "tries": [{"usage_complete": True}],
            }
        ],
        "evidence_manifest": audit_evidence_manifest(evidence_root),
    }
    (evidence_root / "decision.json").write_text(
        json.dumps(decision, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    result = {
        "schema_version": "formalization-design16-full-audit-run-1",
        "scientific_status": "CANONICAL_MULTI_ROLE_FAITHFULNESS_AUDIT",
        "task_id": task_id,
        "candidate_sha256": candidate_sha256,
        "condition_blind": True,
        "attempt_blind": True,
        "auditor_tokens_excluded_from_benchmark": True,
        "source_contract": source_contract,
        "output_root": str(audit_root.resolve()),
        "decision": decision,
    }
    result_path = audit_root / "result.json"
    result_path.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return result_path


class CampaignFixture:
    def __init__(self, root: Path, *, statement_only: bool = False) -> None:
        self.root = root / "campaign"
        self.root.mkdir()
        benchmark_object = (
            "FORMALIZED_STATEMENT_ONLY"
            if statement_only
            else "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF"
        )
        source_contract = (
            "statement-only-single-target-sorry"
            if statement_only
            else "complete-kernel-checked-proof"
        )
        frozen_input_closure = {"test_fixture": True}
        frozen_input_closure["closure_sha256"] = _canonical_hash(
            frozen_input_closure
        )
        self.core = {
            "schema_version": SCHEMA,
            "scientific_status": SCIENTIFIC_STATUS,
            "tasks_run_sequentially": True,
            "pooled_effect_estimate_forbidden": True,
            "plan": load_plan(CONFIG, READINESS),
            "formalizer": {
                "benchmark_object": benchmark_object,
                "source_contract": source_contract,
            },
            "hardware_envelope": {"enforced": False},
            "frozen_input_closure": frozen_input_closure,
        }
        self.manifest = {
            "campaign_core": self.core,
            "campaign_identity_sha256": _canonical_hash(self.core),
            "campaign_nonce": "a" * 64,
            "created_at_utc": "2026-09-22T00:00:00Z",
        }
        self.manifest["manifest_payload_sha256"] = _canonical_hash(self.manifest)
        (self.root / "campaign-manifest.json").write_text(
            json.dumps(self.manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self.events: list[dict[str, object]] = []
        self.append_event({"event_type": "CAMPAIGN_STARTED", "outcome": "RUNNING"})

    @property
    def benchmark_object(self) -> str:
        return self.core["formalizer"]["benchmark_object"]

    @property
    def source_contract(self) -> str:
        return self.core["formalizer"]["source_contract"]

    def append_event(self, value: dict[str, object]) -> None:
        state = self.root / "campaign-state.jsonl"
        _append_record(state, {**value, "schema_version": SCHEMA})
        self.events = _read_journal(state)
        _append_record(
            self.root / "campaign-summary.jsonl",
            _summary_payload(manifest=self.manifest, events=self.events),
        )

    def add_completed_pair(self, task_id: str = "H5-5", *, with_audits: bool = True) -> Path:
        if self.benchmark_object == "FORMALIZED_STATEMENT_ONLY":
            raise AssertionError("this fixture helper constructs proof-mode pairs only")
        task = next(item for item in self.core["plan"] if item["task_id"] == task_id)
        pair_root = self.root / "tasks" / task_id / "pair"
        pair_root.mkdir(parents=True)
        prompt = pair_root / "prompt.txt"
        prompt.write_text("frozen prompt\n", encoding="utf-8")
        reports = {}
        settings = {
            "R0": {
                "system": 12.0,
                "formalizer": 10.0,
                "retrieval": 2.0,
                "tokens": 200,
                "lines": 100,
                "route": "NO_ROUTE",
                "root": None,
                "corpus": "mathlib-only",
                "visible": False,
            },
            "R1": {
                "system": 6.0,
                "formalizer": 5.0,
                "retrieval": 1.0,
                "tokens": 100,
                "lines": 80,
                "route": "DIRECT_OR_COMPOSITION",
                "root": "NumStability.route",
                "corpus": "mathlib-plus-numstability",
                "visible": True,
            },
        }
        for condition, values in settings.items():
            condition_root = pair_root / condition
            workspace = condition_root / "workspace"
            workspace.mkdir(parents=True)
            candidate = condition_root / "submissions" / "01" / "Candidate.lean"
            candidate.parent.mkdir(parents=True)
            candidate.write_text(
                "\n".join(
                    ["-- candidate"] * (values["lines"] - 1)
                    + ["theorem HighamBenchCandidate.target : True := by trivial"]
                )
                + "\n",
                encoding="utf-8",
            )
            api = workspace / "LIBRARY_API.md"
            api.write_text(f"# {condition} API\n", encoding="utf-8")
            composition = condition_root / "composition-packet.json"
            composition.write_text(
                json.dumps(
                    {
                        "route_status": values["route"],
                        "retrieved_roots": (
                            [
                                {
                                    "declaration": {
                                        "name": values["root"],
                                        "module": "NumStability.Test",
                                    }
                                }
                            ]
                            if values["root"]
                            else []
                        ),
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            report = {
                "schema_version": "formalization-design17-matched-condition-2",
                "scientific_status": SCIENTIFIC_STATUS,
                "benchmark_object": self.benchmark_object,
                "source_contract": self.source_contract,
                "faithfulness_status": "NOT_AUDITED",
                "result_status": "COMPILED_AND_INTEGRITY_VALIDATED",
                "task_id": task_id,
                "condition": condition,
                "corpus_id": values["corpus"],
                "fresh_stateless_formalizer": True,
                "warm_or_forked_conversation": False,
                "hardware_envelope_required": False,
                "hardware_snapshot": None,
                "hardware_snapshot_after": None,
                "route_status": values["route"],
                "primary_route": values["root"],
                "library_olean_visible": values["visible"],
                "prompt_sha256": sha256_file(prompt),
                "composition_packet_sha256": sha256_file(composition),
                "library_api_sha256": sha256_file(api),
                "candidate": {
                    "path": str(candidate),
                    "sha256": sha256_file(candidate),
                    "bytes": candidate.stat().st_size,
                    "lines": values["lines"],
                },
                "candidate_sha256": sha256_file(candidate),
                "candidate_lines": values["lines"],
                "numstability_name_mentions": 1 if condition == "R1" else 0,
                "retrieval_wall_seconds": values["retrieval"],
                "formalizer_wall_seconds": values["formalizer"],
                "contestant_active_seconds": values["formalizer"],
                "contestant_system_wall_seconds": values["system"],
                "usage_complete": True,
                "usage": {
                    "input_tokens": values["tokens"],
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 0,
                },
                "net_new_tokens": values["tokens"],
                "validation_pass": True,
            }
            (condition_root / "report.json").write_text(
                json.dumps(report, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            reports[condition] = report
            if with_audits:
                _write_audit_result(
                    condition_root / "full-audit",
                    task_id=task_id,
                    candidate_sha256=sha256_file(candidate),
                    source_contract=self.source_contract,
                )
        pair = {
            "schema_version": "formalization-design17-matched-pair-2",
            "scientific_status": SCIENTIFIC_STATUS,
            "benchmark_object": self.benchmark_object,
            "source_contract": self.source_contract,
            "faithfulness_status": "NOT_AUDITED",
            "pair_status": "FORMALIZATION_FROZEN_PENDING_AUDIT",
            "task_id": task_id,
            "condition_order": task["condition_order"],
            "conditions_run_sequentially": True,
            "prompt_sha256": sha256_file(prompt),
            "condition_reports": reports,
            "comparison": {
                "effect_analysis_eligible": True,
                "r1_over_r0_contestant_system_wall": 0.5,
                "r1_over_r0_contestant_active": 0.5,
                "r1_over_r0_formalizer_wall": 0.5,
                "r1_over_r0_net_new_tokens": 0.5,
                "r1_over_r0_candidate_lines": 0.8,
                "interpretation": "engineering comparison only",
            },
        }
        pair_path = pair_root / "pair-report.json"
        pair_path.write_text(
            json.dumps(pair, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        task_root = pair_root.parent
        stdout = task_root / "runner.stdout.log"
        stderr = task_root / "runner.stderr.log"
        stdout.write_text("runner output\n", encoding="utf-8")
        stderr.write_text("", encoding="utf-8")
        pair_nonce = "b" * 64
        closure = _pair_artifact_closure(pair_root)
        closure_sha256 = _canonical_hash({"files": closure})
        attestation = {
            "schema_version": "formalization-design16-campaign-pair-attestation-1",
            "campaign_identity_sha256": self.manifest["campaign_identity_sha256"],
            "campaign_nonce": self.manifest["campaign_nonce"],
            "pair_nonce": pair_nonce,
            "task_id": task_id,
            "condition_order": task["condition_order"],
            "benchmark_object": self.benchmark_object,
            "source_contract": self.source_contract,
            "pair_status": pair["pair_status"],
            "pair_report_sha256": sha256_file(pair_path),
            "pair_artifact_closure": closure,
            "pair_artifact_closure_sha256": closure_sha256,
            "runner_return_code": 0,
            "runner_stdout_sha256": sha256_file(stdout),
            "runner_stderr_sha256": sha256_file(stderr),
            "created_at_utc": "2026-09-22T00:00:00Z",
        }
        attestation_path = task_root / "campaign-pair-attestation.json"
        attestation_path.write_text(
            json.dumps(attestation, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self.append_event(
            {
                "event_type": "TASK_STARTED",
                "task_id": task_id,
                "stratum": task["stratum"],
                "condition_order": task["condition_order"],
                "campaign_identity_sha256": self.manifest[
                    "campaign_identity_sha256"
                ],
                "campaign_nonce": self.manifest["campaign_nonce"],
                "pair_nonce": pair_nonce,
                "outcome": "RUNNING",
            }
        )
        self.append_event(
            {
                "event_type": "TASK_FORMALIZATION_COMPLETE",
                "task_id": task_id,
                "stratum": task["stratum"],
                "outcome": "FORMALIZATION_COMPLETE_AUDIT_PENDING",
                "details": {
                    "pair_report_sha256": sha256_file(pair_path),
                    "pair_report_path": str(pair_path),
                    "pair_attestation_sha256": sha256_file(attestation_path),
                    "pair_artifact_closure_sha256": closure_sha256,
                },
            }
        )
        return pair_path

    def add_external_audit_batch(self, root: Path, task_id: str = "H5-5") -> Path:
        batch_root = root / "audit-batch"
        jobs = []
        pair = json.loads(
            (self.root / "tasks" / task_id / "pair" / "pair-report.json").read_text(
                encoding="utf-8"
            )
        )
        for condition in ("R0", "R1"):
            jobs.append(
                {
                    "job_id": f"{task_id}:{condition}",
                    "task_id": task_id,
                    "condition": condition,
                    "candidate_sha256": pair["condition_reports"][condition][
                        "candidate_sha256"
                    ],
                    "source_contract": self.source_contract,
                }
            )
        campaign_events = _read_journal(self.root / "campaign-state.jsonl")
        campaign_binding = {
            "campaign_root": str(self.root.resolve()),
            "campaign_manifest_sha256": sha256_file(
                self.root / "campaign-manifest.json"
            ),
            "campaign_identity_sha256": self.manifest["campaign_identity_sha256"],
            "campaign_nonce": self.manifest["campaign_nonce"],
            "campaign_state_sequence": len(campaign_events),
            "campaign_state_sha256": campaign_events[-1]["record_sha256"],
            "jobs": jobs,
        }
        core = {
            "schema_version": "formalization-design16-audit-batch-1",
            "campaign": campaign_binding,
        }
        manifest = {
            "batch_core": core,
            "batch_identity_sha256": _canonical_hash(core),
            "created_at_utc": "2026-09-22T00:00:00Z",
        }
        batch_root.mkdir()
        (batch_root / "audit-batch-manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        state = batch_root / "audit-state.jsonl"
        _append_record(
            state,
            {
                "schema_version": "formalization-design16-audit-batch-1",
                "event_type": "BATCH_STARTED",
                "outcome": "RUNNING",
            },
        )
        for job in jobs:
            _append_record(
                state,
                {
                    "schema_version": "formalization-design16-audit-batch-1",
                    "event_type": "AUDIT_STARTED",
                    "job_id": job["job_id"],
                    "task_id": task_id,
                    "condition": job["condition"],
                    "outcome": "RUNNING",
                },
            )
            result_path = _write_audit_result(
                batch_root / "audits" / task_id / job["condition"],
                task_id=task_id,
                candidate_sha256=job["candidate_sha256"],
                source_contract=self.source_contract,
            )
            _append_record(
                state,
                {
                    "schema_version": "formalization-design16-audit-batch-1",
                    "event_type": "AUDIT_COMPLETED",
                    "job_id": job["job_id"],
                    "task_id": task_id,
                    "outcome": "SCIENTIFICALLY_ELIGIBLE",
                    "details": {
                        "result_sha256": sha256_file(result_path),
                        "accepted": True,
                    },
                },
            )
        return batch_root

    def add_statement_pair(
        self,
        task_id: str = "H5-5",
        *,
        faithful: bool = True,
        infrastructure: bool = False,
    ) -> Path:
        if self.benchmark_object != "FORMALIZED_STATEMENT_ONLY":
            raise AssertionError("statement fixture requires statement-only campaign")
        task = next(item for item in self.core["plan"] if item["task_id"] == task_id)
        pair_root = self.root / "tasks" / task_id / "pair"
        pair_root.mkdir(parents=True)
        prompt = pair_root / "prompt.txt"
        prompt.write_text("statement prompt\n", encoding="utf-8")
        reports = {}
        for condition, scale in (("R0", 2), ("R1", 1)):
            condition_infrastructure = infrastructure and condition == "R1"
            condition_faithful = (faithful and not infrastructure) or condition == "R0"
            condition_root = pair_root / condition
            workspace = condition_root / "workspace"
            workspace.mkdir(parents=True)
            api = workspace / "LIBRARY_API.md"
            api.write_text("# API\n", encoding="utf-8")
            composition = condition_root / "composition-packet.json"
            composition.write_text(
                json.dumps({"route_status": "NO_ROUTE", "retrieved_roots": []}) + "\n",
                encoding="utf-8",
            )
            attempt_root = condition_root / "submissions" / "01"
            attempt_root.mkdir(parents=True)
            candidate = attempt_root / "Candidate.lean"
            candidate.write_text(
                "theorem HighamBenchCandidate.target : True := by sorry\n",
                encoding="utf-8",
            )
            validation = attempt_root / "validation.json"
            validation.write_text(json.dumps({"pass": True}) + "\n", encoding="utf-8")
            frozen = {
                "path": str(candidate),
                "sha256": sha256_file(candidate),
                "bytes": candidate.stat().st_size,
                "lines": 1,
            }
            semantic_sha256 = ("c" if condition == "R0" else "d") * 64
            audit_root = condition_root / "audits" / semantic_sha256
            audit_root.mkdir(parents=True)
            (audit_root / "blind_translation.json").write_text(
                json.dumps({"translation": "statement"}) + "\n", encoding="utf-8"
            )
            verdict = "faithful" if condition_faithful else "unfaithful"
            decision = {
                "task_id": task_id,
                "candidate_semantic_sha256": semantic_sha256,
                "verdict": verdict,
                "accepted": condition_faithful,
                "audit_incident": False,
                "classification": "faithful-equivalent",
                "adjudicated": False,
                "implications": {},
                "mismatches": [],
                "auditor_telemetry": [
                    {
                        "usage": {"total_tokens": 50},
                        "tries": [{"usage_complete": True}],
                    }
                ],
                "evidence_manifest": audit_evidence_manifest(audit_root),
            }
            decision_path = audit_root / "decision.json"
            decision_path.write_text(
                json.dumps(decision, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            attempts = [
                {
                    "attempt": 1,
                    "candidate": frozen,
                    "validation_sha256": sha256_file(validation),
                    "validation_pass": True,
                    "usage_complete": True,
                    "hardware_after": None,
                    "contestant_active_seconds": 4.0 * scale,
                    "status": (
                        "ACCEPTED_FAITHFUL"
                        if condition_faithful
                        else "AUDIT_SYSTEM_INCIDENT"
                        if condition_infrastructure
                        else "AUDIT_REJECTED"
                    ),
                    "semantic_sha256": semantic_sha256,
                    "audit": (
                        {
                            "verdict": "audit-system-incident",
                            "accepted": None,
                            "error": {"message": "synthetic audit infrastructure incident"},
                            "wall_seconds_excluded": 5.0,
                        }
                        if condition_infrastructure
                        else {
                            "verdict": verdict,
                            "accepted": condition_faithful,
                            "decision_sha256": sha256_file(decision_path),
                            "wall_seconds_excluded": 5.0,
                        }
                    ),
                }
            ]
            report = {
                "schema_version": "formalization-design17-statement-condition-1",
                "scientific_status": SCIENTIFIC_STATUS,
                "benchmark_object": self.benchmark_object,
                "source_contract": self.source_contract,
                "faithfulness_status": (
                    "FAITHFUL"
                    if condition_faithful
                    else "NOT_DECIDED_INFRASTRUCTURE"
                    if condition_infrastructure
                    else "UNFAITHFUL_OR_FAILED"
                ),
                "result_status": (
                    "ACCEPTED_FAITHFUL"
                    if condition_faithful
                    else "AUDIT_SYSTEM_INCIDENT"
                    if condition_infrastructure
                    else "ATTEMPT_LIMIT_UNFAITHFUL"
                ),
                "task_id": task_id,
                "condition": condition,
                "corpus_id": "mathlib-only" if condition == "R0" else "mathlib-plus-numstability",
                "fresh_stateless_formalizer": True,
                "same_conversation_repairs": True,
                "submission_count": 1,
                "attempts": attempts,
                "hardware_envelope_required": False,
                "hardware_snapshot": None,
                "route_status": "NO_ROUTE",
                "library_olean_visible": condition == "R1",
                "composition_packet_sha256": sha256_file(composition),
                "library_api_sha256": sha256_file(api),
                "candidate": frozen,
                "candidate_sha256": sha256_file(candidate),
                "candidate_lines": 1,
                "numstability_name_mentions": 0,
                "retrieval_wall_seconds": 1.0 * scale,
                "formalizer_wall_seconds": 5.0 * scale,
                "contestant_active_seconds": 4.0 * scale,
                "contestant_system_wall_seconds": 5.0 * scale,
                "audit_seconds_excluded_from_contestant": 5.0,
                "audit_usage_excluded": {"total_tokens": 50},
                "audit_usage_complete": True,
                "usage": {
                    "input_tokens": 100 * scale,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 0,
                },
                "net_new_tokens": 100 * scale,
                "validation_pass": True,
            }
            (condition_root / "report.json").write_text(
                json.dumps(report, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            reports[condition] = report
        pair_status = (
            "PAIR_INCIDENT"
            if infrastructure
            else "AUDITED_FAITHFUL_PAIR"
            if faithful
            else "AUDITED_PAIR_INELIGIBLE"
        )
        pair = {
            "schema_version": "formalization-design17-matched-pair-2",
            "scientific_status": SCIENTIFIC_STATUS,
            "benchmark_object": self.benchmark_object,
            "source_contract": self.source_contract,
            "faithfulness_status": (
                "NOT_DECIDED_INFRASTRUCTURE"
                if infrastructure
                else "BOTH_FAITHFUL"
                if faithful
                else "PAIR_NOT_BOTH_FAITHFUL"
            ),
            "pair_status": pair_status,
            "task_id": task_id,
            "condition_order": task["condition_order"],
            "conditions_run_sequentially": True,
            "prompt_sha256": sha256_file(prompt),
            "condition_reports": reports,
            "comparison": {
                "effect_analysis_eligible": faithful and not infrastructure,
                "r1_over_r0_contestant_system_wall": (
                    0.5 if faithful and not infrastructure else None
                ),
                "r1_over_r0_contestant_active": (
                    0.5 if faithful and not infrastructure else None
                ),
                "r1_over_r0_formalizer_wall": (
                    0.5 if faithful and not infrastructure else None
                ),
                "r1_over_r0_net_new_tokens": (
                    0.5 if faithful and not infrastructure else None
                ),
                "r1_over_r0_candidate_lines": (
                    1.0 if faithful and not infrastructure else None
                ),
                "r1_over_r0_submission_count": (
                    1.0 if faithful and not infrastructure else None
                ),
            },
        }
        pair_path = pair_root / "pair-report.json"
        pair_path.write_text(
            json.dumps(pair, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        task_root = pair_root.parent
        stdout = task_root / "runner.stdout.log"
        stderr = task_root / "runner.stderr.log"
        stdout.write_text("runner output\n", encoding="utf-8")
        stderr.write_text("", encoding="utf-8")
        pair_nonce = "e" * 64
        closure = _pair_artifact_closure(pair_root)
        closure_sha256 = _canonical_hash({"files": closure})
        attestation = {
            "schema_version": "formalization-design16-campaign-pair-attestation-1",
            "campaign_identity_sha256": self.manifest["campaign_identity_sha256"],
            "campaign_nonce": self.manifest["campaign_nonce"],
            "pair_nonce": pair_nonce,
            "task_id": task_id,
            "condition_order": task["condition_order"],
            "benchmark_object": self.benchmark_object,
            "source_contract": self.source_contract,
            "pair_status": pair["pair_status"],
            "pair_report_sha256": sha256_file(pair_path),
            "pair_artifact_closure": closure,
            "pair_artifact_closure_sha256": closure_sha256,
            "runner_return_code": 0,
            "runner_stdout_sha256": sha256_file(stdout),
            "runner_stderr_sha256": sha256_file(stderr),
        }
        attestation_path = task_root / "campaign-pair-attestation.json"
        attestation_path.write_text(json.dumps(attestation) + "\n", encoding="utf-8")
        self.append_event(
            {
                "event_type": "TASK_STARTED",
                "task_id": task_id,
                "stratum": task["stratum"],
                "condition_order": task["condition_order"],
                "campaign_identity_sha256": self.manifest["campaign_identity_sha256"],
                "campaign_nonce": self.manifest["campaign_nonce"],
                "pair_nonce": pair_nonce,
                "outcome": "RUNNING",
            }
        )
        self.append_event(
            {
                "event_type": (
                    "TASK_INCIDENT"
                    if infrastructure
                    else "TASK_AUDITED_FAITHFUL"
                    if faithful
                    else "TASK_AUDITED_INELIGIBLE"
                ),
                "task_id": task_id,
                "stratum": task["stratum"],
                "outcome": (
                    "PAIR_INFRASTRUCTURE_INCIDENT" if infrastructure else pair_status
                ),
                "details": {
                    "pair_report_sha256": sha256_file(pair_path),
                    "pair_attestation_sha256": sha256_file(attestation_path),
                    "pair_artifact_closure_sha256": closure_sha256,
                },
            }
        )
        return pair_path


class Design16CampaignReportTests(unittest.TestCase):
    def test_authenticates_complete_pair_audits_and_all_five_ratios(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw))
            fixture.add_completed_pair()
            report = build_report(fixture.root)
            primary = report["strata"]["primary_engineering"]
            task = next(item for item in primary["tasks"] if item["task_id"] == "H5-5")
            self.assertEqual(report["campaign_kind"], "DESIGN16_COMPLETE_PROOF")
            self.assertEqual(primary["both_faithful_count"], 1)
            self.assertEqual(task["admission"]["full_audit_status"], "BOTH_FAITHFUL")
            self.assertEqual(
                task["admission"]["analysis_admission"],
                "PRIMARY_PROOF_EXTERNALLY_AUDITED_NO_EFFECT_COUNT",
            )
            self.assertFalse(task["admission"]["effect_analysis_eligible"])
            self.assertEqual(
                set(task["ratios"]),
                {
                    "r1_over_r0_system_time",
                    "r1_over_r0_formalizer_time",
                    "r1_over_r0_net_new_tokens",
                    "r1_over_r0_candidate_lines",
                    "r1_over_r0_retrieval_time",
                },
            )
            self.assertEqual(task["ratios"]["r1_over_r0_candidate_lines"], 0.8)
            self.assertEqual(
                task["conditions"]["R1"]["audit"][
                    "auditor_total_tokens_excluded"
                ],
                300,
            )
            self.assertIsNone(report["pooled_effect_estimate"])
            self.assertIsNone(primary["aggregate_treatment_effect"])

    def test_labels_statement_only_campaign_as_design17(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw), statement_only=True)
            report = build_report(fixture.root)
            self.assertEqual(report["campaign_kind"], "DESIGN17_STATEMENT_ONLY")
            self.assertEqual(report["source_contract"], "statement-only-single-target-sorry")
            self.assertEqual(
                report["strata"]["primary_engineering"]["pending_count"], 2
            )

    def test_statement_internal_audits_admit_only_audited_faithful_pair(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw), statement_only=True)
            fixture.add_statement_pair()
            report = build_report(fixture.root)
            task = next(
                item
                for item in report["strata"]["primary_engineering"]["tasks"]
                if item["task_id"] == "H5-5"
            )
            self.assertEqual(task["campaign_outcome"], "AUDITED_FAITHFUL_PAIR")
            self.assertEqual(task["admission"]["full_audit_status"], "BOTH_FAITHFUL")
            self.assertTrue(task["admission"]["effect_analysis_eligible"])
            self.assertEqual(
                task["admission"]["analysis_admission"],
                "PRIMARY_EXPLORATORY_FAITHFUL_PAIR",
            )
            self.assertEqual(task["ratios"]["r1_over_r0_system_time"], 0.5)
            self.assertEqual(
                task["ratios"]["r1_over_r0_contestant_active_time"], 0.5
            )
            self.assertEqual(task["primary_effect_metric"], "contestant_active_time")
            self.assertEqual(task["primary_effect_ratio"], 0.5)
            self.assertEqual(
                task["conditions"]["R0"]["metrics"]["contestant_active_time"],
                8.0,
            )

    def test_statement_ineligible_pair_never_publishes_effect_ratios(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw), statement_only=True)
            fixture.add_statement_pair(faithful=False)
            report = build_report(fixture.root)
            task = next(
                item
                for item in report["strata"]["primary_engineering"]["tasks"]
                if item["task_id"] == "H5-5"
            )
            self.assertEqual(task["campaign_outcome"], "AUDITED_PAIR_INELIGIBLE")
            self.assertEqual(
                task["admission"]["full_audit_status"], "AT_LEAST_ONE_UNFAITHFUL"
            )
            self.assertFalse(task["runner_comparison_available"])
            self.assertFalse(task["admission"]["effect_analysis_eligible"])
            self.assertIsNone(task["ratios"])
            self.assertIsNone(task["primary_effect_ratio"])

    def test_authenticated_infrastructure_pair_is_distinct_and_excluded(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw), statement_only=True)
            fixture.add_statement_pair(infrastructure=True)
            report = build_report(fixture.root)
            primary = report["strata"]["primary_engineering"]
            task = next(
                item for item in primary["tasks"] if item["task_id"] == "H5-5"
            )
            self.assertEqual(
                task["campaign_outcome"], "PAIR_INFRASTRUCTURE_INCIDENT"
            )
            self.assertEqual(task["pair_status"], "PAIR_INCIDENT")
            self.assertTrue(task["admission"]["pair_report_authenticated"])
            self.assertEqual(
                task["conditions"]["R1"]["faithfulness_status"],
                "NOT_DECIDED_INFRASTRUCTURE",
            )
            self.assertEqual(
                task["admission"]["analysis_admission"],
                "INFRASTRUCTURE_INCIDENT_EXCLUDED",
            )
            self.assertEqual(primary["incident_count"], 1)
            self.assertEqual(primary["authenticated_infrastructure_incident_count"], 1)
            self.assertIsNone(task["ratios"])
            self.assertIsNone(task["primary_effect_ratio"])

    def test_rejects_pair_report_not_bound_to_terminal_state(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw))
            pair_path = fixture.add_completed_pair()
            pair_path.chmod(0o600)
            value = json.loads(pair_path.read_text(encoding="utf-8"))
            value["comparison"]["r1_over_r0_net_new_tokens"] = 0.25
            pair_path.write_text(json.dumps(value) + "\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                build_report(fixture.root)

    def test_rejects_mutated_summary_chain(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = CampaignFixture(Path(raw))
            summary = fixture.root / "campaign-summary.jsonl"
            value = json.loads(summary.read_text(encoding="utf-8"))
            value["latest_state_sequence"] = 99
            summary.write_text(json.dumps(value) + "\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                build_report(fixture.root)

    def test_write_report_refuses_existing_output_directory(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            fixture = CampaignFixture(root)
            output = root / "report"
            output.mkdir()
            with self.assertRaises(BenchmarkError):
                write_report(fixture.root, output)

    def test_external_audit_batch_is_authenticated_and_hash_bound(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            fixture = CampaignFixture(root)
            fixture.add_completed_pair(with_audits=False)
            batch = fixture.add_external_audit_batch(root)
            report = build_report(fixture.root, batch)
            self.assertEqual(
                report["audit_batch_authentication"]["status"], "AUTHENTICATED"
            )
            task = next(
                item
                for item in report["strata"]["primary_engineering"]["tasks"]
                if item["task_id"] == "H5-5"
            )
            self.assertEqual(task["admission"]["full_audit_status"], "BOTH_FAITHFUL")
            result_path = batch / "audits" / "H5-5" / "R1" / "result.json"
            result_path.chmod(0o600)
            result_path.write_text("{}\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                build_report(fixture.root, batch)

    def test_missing_requested_audit_batch_remains_pending(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            fixture = CampaignFixture(root)
            fixture.add_completed_pair(with_audits=False)
            report = build_report(fixture.root, root / "not-created")
            self.assertEqual(
                report["audit_batch_authentication"]["status"],
                "NOT_PRESENT_AUDITS_PENDING",
            )
            self.assertEqual(
                report["strata"]["primary_engineering"]["audit_pending_count"], 1
            )

    def test_write_report_emits_separate_strata_json_and_markdown(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            fixture = CampaignFixture(root)
            fixture.add_completed_pair()
            output = root / "report"
            result = write_report(fixture.root, output)
            self.assertFalse(result["provider_calls_made"])
            self.assertTrue((output / "campaign-report.json").is_file())
            markdown = (output / "campaign-report.md").read_text(encoding="utf-8")
            self.assertIn("## Primary engineering", markdown)
            self.assertIn("## Negative controls", markdown)
            self.assertIn("## Excluded collision/router diagnostics", markdown)
            self.assertNotIn("pooled treatment estimate\n|", markdown)


if __name__ == "__main__":
    unittest.main()
