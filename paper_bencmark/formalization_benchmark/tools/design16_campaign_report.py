#!/usr/bin/env python3
"""Authenticate and report a Design-16/17 exploratory campaign offline.

The reporter makes no provider calls and never edits the campaign.  It
authenticates the campaign manifest, both hash-chained journals, terminal pair
reports, condition reports, and their principal immutable artifacts before
computing per-task R1/R0 ratios.  Contestant-active time is the primary timer;
its ratio is emitted only for audited-faithful pairs.  Primary-engineering
tasks, negative controls, and excluded diagnostics remain separate in both
JSON and Markdown; this tool never emits a pooled treatment estimate.
"""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
import sys
from typing import Any, Mapping

from audit_controller import audit_evidence_manifest
from common import BenchmarkError, sha256_file, utc_now
from design16_campaign import (
    ATTESTED_PAIR_INCIDENT,
    AUDITED_FAITHFUL,
    AUDITED_INELIGIBLE,
    AUDIT_PENDING,
    EXPECTED_STRATA,
    EXPECTED_TASKS,
    PAIR_ATTESTATION,
    SCHEMA as CAMPAIGN_SCHEMA,
    SCIENTIFIC_STATUS,
    _canonical_hash,
    _read_journal,
    _read_object,
    _pair_artifact_closure,
    _summary_payload,
    _terminal_by_task,
)
from design16_smoke import _net_new
from hardware import frozen_hardware_identity


REPORT_SCHEMA = "formalization-design16-campaign-report-1"
PAIR_SCHEMA = "formalization-design17-matched-pair-2"
CONDITION_SCHEMA = "formalization-design17-matched-condition-2"
FULL_AUDIT_SCHEMA = "formalization-design16-full-audit-run-1"
FULL_AUDIT_STATUS = "CANONICAL_MULTI_ROLE_FAITHFULNESS_AUDIT"
AUDIT_BATCH_SCHEMA = "formalization-design16-audit-batch-1"
CONDITIONS = ("R0", "R1")
INFRASTRUCTURE_CONDITION_STATUSES = frozenset(
    {
        "FORMALIZER_INCIDENT",
        "VALIDATION_INFRASTRUCTURE_INCIDENT",
        "AUDIT_PREPARATION_INCIDENT",
        "AUDIT_SYSTEM_INCIDENT",
    }
)
METRICS = {
    "contestant_system_wall_seconds": "system_time",
    "formalizer_wall_seconds": "formalizer_time",
    "net_new_tokens": "net_new_tokens",
    "candidate_lines": "candidate_lines",
    "retrieval_wall_seconds": "retrieval_time",
}
CAMPAIGN_KINDS = {
    (
        "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF",
        "complete-kernel-checked-proof",
    ): "DESIGN16_COMPLETE_PROOF",
    (
        "FORMALIZED_STATEMENT_ONLY",
        "statement-only-single-target-sorry",
    ): "DESIGN17_STATEMENT_ONLY",
}


def _write_bytes_once(path: Path, payload: bytes) -> None:
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        if path.exists() and not path.is_symlink():
            path.unlink()
        raise


def _write_json_once(path: Path, value: Mapping[str, Any]) -> None:
    _write_bytes_once(path, json.dumps(value, indent=2, sort_keys=True).encode() + b"\n")


def _number(value: Any, label: str, *, integer: bool = False) -> int | float:
    valid = (
        isinstance(value, int)
        if integer
        else isinstance(value, (int, float)) and math.isfinite(float(value))
    )
    if isinstance(value, bool) or not valid or value < 0:
        raise BenchmarkError(f"{label} must be a finite nonnegative number")
    return value


def _ratio(numerator: int | float, denominator: int | float) -> float | None:
    return float(numerator) / float(denominator) if denominator else None


def _same_number(left: Any, right: Any) -> bool:
    return (
        isinstance(left, (int, float))
        and not isinstance(left, bool)
        and isinstance(right, (int, float))
        and not isinstance(right, bool)
        and math.isclose(float(left), float(right), rel_tol=1e-12, abs_tol=1e-12)
    )


def _same_optional_number(left: Any, right: float | None) -> bool:
    return left is None if right is None else _same_number(left, right)


def _stable_summary(value: Mapping[str, Any]) -> dict[str, Any]:
    ignored = {
        "recorded_at_utc",
        "sequence",
        "previous_record_sha256",
        "record_sha256",
    }
    return {key: item for key, item in value.items() if key not in ignored}


def _authenticate_campaign(
    root: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    manifest_path = root / "campaign-manifest.json"
    state_path = root / "campaign-state.jsonl"
    summary_path = root / "campaign-summary.jsonl"
    manifest = _read_object(manifest_path, "campaign manifest")
    core = manifest.get("campaign_core")
    identity = manifest.get("campaign_identity_sha256")
    if not isinstance(core, dict) or identity != _canonical_hash(core):
        raise BenchmarkError("campaign manifest identity is stale")
    unsigned_manifest = dict(manifest)
    observed_payload_sha256 = unsigned_manifest.pop("manifest_payload_sha256", None)
    nonce = manifest.get("campaign_nonce")
    if (
        not isinstance(nonce, str)
        or len(nonce) != 64
        or any(character not in "0123456789abcdef" for character in nonce)
        or observed_payload_sha256 != _canonical_hash(unsigned_manifest)
    ):
        raise BenchmarkError("campaign manifest payload authentication failed")
    if (
        core.get("schema_version") != CAMPAIGN_SCHEMA
        or core.get("scientific_status") != SCIENTIFIC_STATUS
        or core.get("pooled_effect_estimate_forbidden") is not True
    ):
        raise BenchmarkError("campaign manifest protocol fields are malformed")
    frozen_closure = core.get("frozen_input_closure")
    if not isinstance(frozen_closure, dict):
        raise BenchmarkError("campaign manifest lacks the frozen input closure")
    unhashed_closure = dict(frozen_closure)
    closure_sha256 = unhashed_closure.pop("closure_sha256", None)
    if closure_sha256 != _canonical_hash(unhashed_closure):
        raise BenchmarkError("campaign frozen input closure identity is stale")
    plan = core.get("plan")
    if not isinstance(plan, list):
        raise BenchmarkError("campaign manifest plan is missing")
    task_ids = [item.get("task_id") for item in plan if isinstance(item, dict)]
    if tuple(task_ids) != EXPECTED_TASKS or len(plan) != len(task_ids):
        raise BenchmarkError("campaign manifest does not contain the exact Higham-13 plan")
    observed_strata = {
        stratum: tuple(
            item["task_id"] for item in plan if item.get("stratum") == stratum
        )
        for stratum in EXPECTED_STRATA
    }
    if observed_strata != EXPECTED_STRATA:
        raise BenchmarkError("campaign manifest strata are stale")

    events = _read_journal(state_path)
    summaries = _read_journal(summary_path)
    if not events or len(events) != len(summaries):
        raise BenchmarkError("state and summary journals are incomplete or out of sync")
    for index, summary in enumerate(summaries, 1):
        expected = _summary_payload(manifest=manifest, events=events[:index])
        if _stable_summary(summary) != _stable_summary(expected):
            raise BenchmarkError(f"summary journal does not authenticate state record {index}")
    authentication = {
        "campaign_manifest_path": str(manifest_path),
        "campaign_manifest_sha256": sha256_file(manifest_path),
        "campaign_identity_sha256": identity,
        "campaign_nonce": nonce,
        "state_journal_path": str(state_path),
        "state_journal_sha256": sha256_file(state_path),
        "state_record_count": len(events),
        "state_head_sha256": events[-1]["record_sha256"],
        "summary_journal_path": str(summary_path),
        "summary_journal_sha256": sha256_file(summary_path),
        "summary_record_count": len(summaries),
        "summary_head_sha256": summaries[-1]["record_sha256"],
        "authenticated": True,
    }
    return manifest, events, authentication


def _validate_artifact(path: Path, expected_sha256: Any, label: str) -> None:
    if (
        path.is_symlink()
        or not path.is_file()
        or not isinstance(expected_sha256, str)
        or sha256_file(path) != expected_sha256
    ):
        raise BenchmarkError(f"{label} is missing, unsafe, or hash-mismatched")


def _audit_result_paths(condition_root: Path) -> list[Path]:
    result: list[Path] = []
    resolved_root = condition_root.resolve()
    for path in condition_root.rglob("result.json"):
        if path.is_symlink() or not path.is_file():
            continue
        resolved = path.resolve()
        if resolved_root not in resolved.parents:
            raise BenchmarkError(f"audit result escapes condition root: {path}")
        value = _read_object(path, "possible full-audit result")
        if value.get("schema_version") == FULL_AUDIT_SCHEMA:
            result.append(path)
    return sorted(result)


def _audit_usage(decision: Mapping[str, Any]) -> tuple[int | None, bool]:
    telemetry = decision.get("auditor_telemetry")
    if not isinstance(telemetry, list):
        return None, False
    total = 0
    complete = True
    for role in telemetry:
        usage = role.get("usage") if isinstance(role, dict) else None
        tries = role.get("tries") if isinstance(role, dict) else None
        value = usage.get("total_tokens") if isinstance(usage, dict) else None
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            complete = False
        else:
            total += value
        if not isinstance(tries, list) or not tries or any(
            not isinstance(item, dict) or item.get("usage_complete") is not True
            for item in tries
        ):
            complete = False
    return (total if complete else None), complete


def _authenticate_audit_batch(
    requested_root: Path | None,
    *,
    campaign_root: Path,
    campaign_authentication: Mapping[str, Any],
) -> tuple[dict[tuple[str, str], dict[str, Any]], dict[str, Any]]:
    if requested_root is None:
        return {}, {"status": "NOT_REQUESTED", "authenticated": False}
    requested = requested_root.expanduser()
    if not requested.exists():
        return {}, {
            "status": "NOT_PRESENT_AUDITS_PENDING",
            "authenticated": False,
            "requested_path": str(requested.absolute()),
        }
    if requested.is_symlink() or not requested.is_dir():
        raise BenchmarkError("audit batch root is unsafe")
    root = requested.resolve()
    manifest_path = root / "audit-batch-manifest.json"
    if not manifest_path.exists():
        if any(root.iterdir()):
            raise BenchmarkError("nonempty audit batch root lacks a manifest")
        return {}, {
            "status": "NOT_INITIALIZED_AUDITS_PENDING",
            "authenticated": False,
            "requested_path": str(root),
        }
    manifest = _read_object(manifest_path, "audit batch manifest")
    core = manifest.get("batch_core")
    if (
        not isinstance(core, dict)
        or core.get("schema_version") != AUDIT_BATCH_SCHEMA
        or manifest.get("batch_identity_sha256") != _canonical_hash(core)
    ):
        raise BenchmarkError("audit batch manifest identity is stale")
    campaign = core.get("campaign")
    if not isinstance(campaign, dict):
        raise BenchmarkError("audit batch has no authenticated campaign binding")
    expected_campaign_binding = {
        "campaign_root": str(campaign_root),
        "campaign_manifest_sha256": campaign_authentication["campaign_manifest_sha256"],
        "campaign_identity_sha256": campaign_authentication["campaign_identity_sha256"],
        "campaign_nonce": campaign_authentication["campaign_nonce"],
        "campaign_state_sequence": campaign_authentication["state_record_count"],
        "campaign_state_sha256": campaign_authentication["state_head_sha256"],
    }
    if any(campaign.get(key) != value for key, value in expected_campaign_binding.items()):
        raise BenchmarkError("audit batch is bound to a different campaign state")
    jobs = campaign.get("jobs")
    if not isinstance(jobs, list):
        raise BenchmarkError("audit batch campaign binding has no jobs")
    by_job: dict[str, Mapping[str, Any]] = {}
    for job in jobs:
        if not isinstance(job, dict):
            raise BenchmarkError("audit batch contains a malformed job")
        job_id = job.get("job_id")
        task_id = job.get("task_id")
        condition = job.get("condition")
        if (
            not isinstance(job_id, str)
            or job_id in by_job
            or task_id not in EXPECTED_TASKS
            or condition not in CONDITIONS
            or job_id != f"{task_id}:{condition}"
            or not isinstance(job.get("candidate_sha256"), str)
        ):
            raise BenchmarkError("audit batch contains an invalid or duplicate job")
        by_job[job_id] = job
    state_path = root / "audit-state.jsonl"
    if not state_path.exists():
        return {}, {
            "status": "MANIFEST_ONLY_AUDITS_PENDING",
            "authenticated": True,
            "batch_manifest_path": str(manifest_path),
            "batch_manifest_sha256": sha256_file(manifest_path),
            "batch_identity_sha256": manifest["batch_identity_sha256"],
            "state_record_count": 0,
        }
    events = _read_journal(state_path)
    started: set[str] = set()
    terminals: dict[str, Mapping[str, Any]] = {}
    terminal_types = {
        "AUDIT_COMPLETED",
        "AUDIT_INCIDENT",
        "AUDIT_RECOVERED_COMPLETED",
        "AUDIT_RECOVERED_INCIDENT",
    }
    for event in events:
        if event.get("schema_version") != AUDIT_BATCH_SCHEMA:
            raise BenchmarkError("audit batch journal contains a foreign schema")
        event_type = event.get("event_type")
        job_id = event.get("job_id")
        if event_type == "AUDIT_STARTED":
            if job_id not in by_job or job_id in started:
                raise BenchmarkError("audit batch contains a duplicate or unknown start")
            started.add(str(job_id))
        elif event_type in terminal_types:
            if job_id not in by_job or job_id in terminals or job_id not in started:
                raise BenchmarkError("audit batch contains a malformed terminal")
            terminals[str(job_id)] = event
    index: dict[tuple[str, str], dict[str, Any]] = {}
    for job_id, job in by_job.items():
        key = (str(job["task_id"]), str(job["condition"]))
        terminal = terminals.get(job_id)
        if terminal is None:
            index[key] = {"status": "AUDIT_PENDING", "job": dict(job)}
            continue
        outcome = terminal.get("outcome")
        details = terminal.get("details")
        if not isinstance(details, dict):
            raise BenchmarkError(f"audit batch terminal lacks details: {job_id}")
        if outcome == "AUDIT_INCIDENT":
            index[key] = {
                "status": "AUDIT_INCIDENT",
                "job": dict(job),
                "terminal": dict(terminal),
            }
            continue
        if outcome not in {"SCIENTIFICALLY_ELIGIBLE", "SCIENTIFICALLY_INELIGIBLE"}:
            raise BenchmarkError(f"audit batch terminal outcome is invalid: {job_id}")
        result_path = root / "audits" / str(job["task_id"]) / str(job["condition"]) / "result.json"
        if (
            result_path.is_symlink()
            or not result_path.is_file()
            or details.get("result_sha256") != sha256_file(result_path)
            or details.get("accepted") is not (outcome == "SCIENTIFICALLY_ELIGIBLE")
        ):
            raise BenchmarkError(f"audit batch result is not hash-bound: {job_id}")
        index[key] = {
            "status": "AUDIT_COMPLETED",
            "job": dict(job),
            "terminal": dict(terminal),
            "result_path": result_path,
            "result_sha256": sha256_file(result_path),
        }
    authentication = {
        "status": "AUTHENTICATED",
        "authenticated": True,
        "batch_manifest_path": str(manifest_path),
        "batch_manifest_sha256": sha256_file(manifest_path),
        "batch_identity_sha256": manifest["batch_identity_sha256"],
        "state_journal_path": str(state_path),
        "state_journal_sha256": sha256_file(state_path),
        "state_record_count": len(events),
        "state_head_sha256": events[-1]["record_sha256"] if events else None,
        "job_count": len(jobs),
        "terminal_count": len(terminals),
    }
    return index, authentication


def _load_audit(
    condition_root: Path,
    *,
    task_id: str,
    condition: str,
    candidate_sha256: str,
    source_contract: str,
    audit_record: Mapping[str, Any] | None,
) -> dict[str, Any] | None:
    if audit_record is not None:
        job = audit_record.get("job")
        if (
            not isinstance(job, Mapping)
            or job.get("task_id") != task_id
            or job.get("condition") != condition
            or job.get("candidate_sha256") != candidate_sha256
            or job.get("source_contract") != source_contract
        ):
            raise BenchmarkError(f"audit batch job is not bound to {task_id} {condition}")
    if audit_record is not None and audit_record.get("status") == "AUDIT_INCIDENT":
        terminal = audit_record.get("terminal")
        return {
            "present": False,
            "status": "AUDIT_INCIDENT",
            "accepted": None,
            "incident": terminal.get("details") if isinstance(terminal, dict) else None,
        }
    if audit_record is not None and audit_record.get("status") == "AUDIT_PENDING":
        return None
    paths = _audit_result_paths(condition_root) if audit_record is None else []
    if audit_record is not None and audit_record.get("status") == "AUDIT_COMPLETED":
        external_path = audit_record.get("result_path")
        if not isinstance(external_path, Path):
            raise BenchmarkError(
                f"authenticated audit path is malformed for {task_id} {condition}"
            )
        paths = [external_path]
    if len(paths) > 1:
        raise BenchmarkError(f"multiple canonical full-audit results found under {condition_root}")
    if not paths:
        return None
    path = paths[0]
    if audit_record is not None and sha256_file(path) != audit_record.get("result_sha256"):
        raise BenchmarkError(f"authenticated audit result changed for {task_id} {condition}")
    result = _read_object(path, "full-audit result")
    decision = result.get("decision")
    if (
        result.get("scientific_status") != FULL_AUDIT_STATUS
        or result.get("task_id") != task_id
        or result.get("candidate_sha256") != candidate_sha256
        or result.get("source_contract") != source_contract
        or result.get("output_root") != str(path.parent.resolve())
        or result.get("condition_blind") is not True
        or result.get("attempt_blind") is not True
        or result.get("auditor_tokens_excluded_from_benchmark") is not True
        or not isinstance(decision, dict)
    ):
        raise BenchmarkError(f"full-audit result is not bound to {task_id} candidate")
    audit_root = path.parent / "audit"
    decision_path = audit_root / "decision.json"
    recorded_decision = _read_object(decision_path, "full-audit decision")
    if (
        recorded_decision != decision
        or decision.get("evidence_manifest") != audit_evidence_manifest(audit_root)
    ):
        raise BenchmarkError(f"full-audit evidence closure is stale for {task_id}")
    verdict = decision.get("verdict")
    if (
        verdict not in {"faithful", "unfaithful"}
        or decision.get("accepted") is not (verdict == "faithful")
        or decision.get("audit_incident") is not False
        or decision.get("task_id") != task_id
    ):
        raise BenchmarkError(f"full-audit decision is malformed for {task_id}")
    audit_seconds = _number(
        decision.get("audit_wall_seconds"), f"{task_id} audit wall seconds"
    )
    tokens, usage_complete = _audit_usage(decision)
    return {
        "present": True,
        "status": "AUDIT_COMPLETED",
        "condition": condition,
        "result_path": str(path),
        "result_sha256": sha256_file(path),
        "decision_path": str(decision_path),
        "decision_sha256": sha256_file(decision_path),
        "verdict": verdict,
        "accepted": verdict == "faithful",
        "classification": decision.get("classification"),
        "adjudicated": decision.get("adjudicated"),
        "implications": decision.get("implications"),
        "mismatch_count": len(decision.get("mismatches", []))
        if isinstance(decision.get("mismatches"), list)
        else None,
        "audit_wall_seconds_excluded": audit_seconds,
        "auditor_total_tokens_excluded": tokens,
        "auditor_usage_complete": usage_complete,
    }


def _load_statement_audit(
    condition_root: Path,
    *,
    task_id: str,
    condition: str,
    attempt: Mapping[str, Any],
) -> dict[str, Any] | None:
    embedded = attempt.get("audit")
    if not isinstance(embedded, dict):
        return None
    if embedded.get("verdict") == "audit-system-incident":
        return {
            "present": False,
            "status": "AUDIT_INCIDENT",
            "condition": condition,
            "accepted": None,
            "incident": embedded.get("error"),
        }
    semantic_sha256 = attempt.get("semantic_sha256")
    if not isinstance(semantic_sha256, str) or len(semantic_sha256) != 64:
        raise BenchmarkError(f"{task_id} {condition} audited attempt lacks semantic identity")
    audit_root = condition_root / "audits" / semantic_sha256
    decision_path = audit_root / "decision.json"
    decision = _read_object(decision_path, "statement-loop audit decision")
    verdict = decision.get("verdict")
    if (
        sha256_file(decision_path) != embedded.get("decision_sha256")
        or decision.get("task_id") != task_id
        or decision.get("candidate_semantic_sha256") != semantic_sha256
        or verdict not in {"faithful", "unfaithful"}
        or decision.get("accepted") is not (verdict == "faithful")
        or embedded.get("verdict") != verdict
        or embedded.get("accepted") is not (verdict == "faithful")
        or decision.get("audit_incident") is not False
        or decision.get("evidence_manifest") != audit_evidence_manifest(audit_root)
    ):
        raise BenchmarkError(f"{task_id} {condition} statement-loop audit is stale")
    tokens, usage_complete = _audit_usage(decision)
    return {
        "present": True,
        "status": "AUDIT_COMPLETED",
        "condition": condition,
        "decision_path": str(decision_path),
        "decision_sha256": sha256_file(decision_path),
        "semantic_sha256": semantic_sha256,
        "verdict": verdict,
        "accepted": verdict == "faithful",
        "classification": decision.get("classification"),
        "adjudicated": decision.get("adjudicated"),
        "implications": decision.get("implications"),
        "mismatch_count": len(decision.get("mismatches", []))
        if isinstance(decision.get("mismatches"), list)
        else None,
        "audit_wall_seconds_excluded": embedded.get("wall_seconds_excluded"),
        "auditor_total_tokens_excluded": tokens,
        "auditor_usage_complete": usage_complete,
    }


def _hardware_status(
    report: Mapping[str, Any],
    campaign_envelope: Mapping[str, Any],
    *,
    statement_only: bool,
) -> str:
    enforced = "identity" in campaign_envelope
    snapshot = report.get("hardware_snapshot")
    if statement_only:
        attempts = report.get("attempts")
        snapshots_after = (
            [
                attempt.get("hardware_after")
                for attempt in attempts
                if isinstance(attempt, dict)
            ]
            if isinstance(attempts, list)
            else []
        )
    else:
        snapshots_after = [report.get("hardware_snapshot_after")]
    if not enforced:
        if (
            report.get("hardware_envelope_required") is not False
            or snapshot is not None
            or any(item is not None for item in snapshots_after)
        ):
            raise BenchmarkError("condition hardware record disagrees with unenforced campaign")
        return "NOT_ENFORCED_EXPLORATORY"
    if (
        report.get("hardware_envelope_required") is not True
        or not isinstance(snapshot, dict)
        or not snapshots_after
        or any(not isinstance(item, dict) for item in snapshots_after)
        or snapshot.get("admitted") is not True
        or any(item.get("admitted") is not True for item in snapshots_after)
        or frozen_hardware_identity(snapshot) != campaign_envelope.get("identity")
        or any(
            frozen_hardware_identity(item) != campaign_envelope.get("identity")
            for item in snapshots_after
        )
    ):
        raise BenchmarkError("condition did not satisfy the frozen Titan hardware envelope")
    return "TITAN_ENVELOPE_ADMITTED"


def _validate_condition(
    condition_root: Path,
    embedded: Any,
    *,
    task_id: str,
    condition: str,
    prompt_sha256: str,
    source_contract: str,
    benchmark_object: str,
    campaign_envelope: Mapping[str, Any],
    audit_record: Mapping[str, Any] | None,
) -> dict[str, Any]:
    statement_only = benchmark_object == "FORMALIZED_STATEMENT_ONLY"
    if not isinstance(embedded, dict):
        raise BenchmarkError(f"{task_id} {condition} condition report is missing")
    report_path = condition_root / "report.json"
    report = _read_object(report_path, f"{task_id} {condition} condition report")
    if report != embedded:
        raise BenchmarkError(f"{task_id} {condition} embedded condition report changed")
    expected_schema = (
        "formalization-design17-statement-condition-1"
        if statement_only
        else CONDITION_SCHEMA
    )
    common_invalid = (
        report.get("schema_version") != expected_schema
        or report.get("scientific_status") != SCIENTIFIC_STATUS
        or report.get("task_id") != task_id
        or report.get("condition") != condition
        or report.get("source_contract") != source_contract
        or report.get("benchmark_object") != benchmark_object
        or report.get("fresh_stateless_formalizer") is not True
    )
    if statement_only:
        attempts = report.get("attempts")
        result_status = report.get("result_status")
        accepted_condition = result_status == "ACCEPTED_FAITHFUL"
        infrastructure_condition = result_status in INFRASTRUCTURE_CONDITION_STATUSES
        expected_faithfulness = (
            "FAITHFUL"
            if accepted_condition
            else "NOT_DECIDED_INFRASTRUCTURE"
            if infrastructure_condition
            else "UNFAITHFUL_OR_FAILED"
        )
        mode_invalid = (
            not isinstance(attempts, list)
            or not attempts
            or report.get("submission_count") != len(attempts)
            or report.get("same_conversation_repairs") is not True
            or report.get("faithfulness_status") != expected_faithfulness
        )
    else:
        attempts = []
        accepted_condition = False
        mode_invalid = (
            report.get("prompt_sha256") != prompt_sha256
            or report.get("result_status") != "COMPILED_AND_INTEGRITY_VALIDATED"
            or report.get("validation_pass") is not True
            or report.get("usage_complete") is not True
            or report.get("faithfulness_status") != "NOT_AUDITED"
            or report.get("warm_or_forked_conversation") is not False
        )
    if common_invalid or mode_invalid:
        raise BenchmarkError(f"{task_id} {condition} condition report is inadmissible")

    if statement_only:
        attempt_active_seconds = 0.0
        for attempt_number, attempt in enumerate(attempts, 1):
            if not isinstance(attempt, dict) or attempt.get("attempt") != attempt_number:
                raise BenchmarkError(f"{task_id} {condition} attempt sequence is malformed")
            attempt_root = condition_root / "submissions" / f"{attempt_number:02d}"
            _validate_artifact(
                attempt_root / "Candidate.lean",
                attempt.get("candidate", {}).get("sha256")
                if isinstance(attempt.get("candidate"), dict)
                else None,
                f"{task_id} {condition} attempt {attempt_number} candidate",
            )
            _validate_artifact(
                attempt_root / "validation.json",
                attempt.get("validation_sha256"),
                f"{task_id} {condition} attempt {attempt_number} validation",
            )
            attempt_active_seconds += float(
                _number(
                    attempt.get("contestant_active_seconds"),
                    f"{task_id} {condition} attempt {attempt_number} active seconds",
                )
            )
        final_attempt = attempts[-1]
        if infrastructure_condition and final_attempt.get("status") != result_status:
            raise BenchmarkError(
                f"{task_id} {condition} final attempt status disagrees with condition"
            )
        if report.get("candidate") != final_attempt.get("candidate"):
            raise BenchmarkError(f"{task_id} {condition} final candidate is not final attempt")
        candidate_path = (
            condition_root
            / "submissions"
            / f"{len(attempts):02d}"
            / "Candidate.lean"
        )
    else:
        final_attempt = None
        candidate_path = condition_root / "submissions" / "01" / "Candidate.lean"
    _validate_artifact(
        candidate_path,
        report.get("candidate_sha256"),
        f"{task_id} {condition} candidate",
    )
    try:
        candidate_payload = candidate_path.read_bytes()
        observed_text = candidate_payload.decode("utf-8")
        observed_lines = len(observed_text.splitlines())
    except UnicodeDecodeError as error:
        raise BenchmarkError(f"{task_id} {condition} candidate is not UTF-8") from error
    frozen_candidate = report.get("candidate")
    if (
        not isinstance(frozen_candidate, dict)
        or frozen_candidate.get("sha256") != report.get("candidate_sha256")
        or frozen_candidate.get("bytes") != len(candidate_payload)
        or frozen_candidate.get("lines") != observed_lines
    ):
        raise BenchmarkError(f"{task_id} {condition} frozen candidate record is stale")
    composition_path = condition_root / "composition-packet.json"
    _validate_artifact(
        composition_path,
        report.get("composition_packet_sha256"),
        f"{task_id} {condition} composition packet",
    )
    _validate_artifact(
        condition_root / "workspace" / "LIBRARY_API.md",
        report.get("library_api_sha256"),
        f"{task_id} {condition} library API",
    )

    metrics: dict[str, int | float] = {}
    for source_name, output_name in METRICS.items():
        metrics[output_name] = _number(
            report.get(source_name),
            f"{task_id} {condition} {source_name}",
            integer=source_name in {"net_new_tokens", "candidate_lines"},
        )
    metrics["contestant_active_time"] = _number(
        report.get("contestant_active_seconds"),
        f"{task_id} {condition} contestant_active_seconds",
    )
    if metrics["candidate_lines"] != observed_lines:
        raise BenchmarkError(f"{task_id} {condition} candidate line count is stale")
    usage = report.get("usage")
    if not isinstance(usage, dict) or any(
        not isinstance(usage.get(name), int)
        or isinstance(usage.get(name), bool)
        or usage[name] < 0
        for name in (
            "input_tokens",
            "cached_input_tokens",
            "cache_write_input_tokens",
            "output_tokens",
        )
    ):
        raise BenchmarkError(f"{task_id} {condition} formalizer usage is malformed")
    if _net_new(usage) != metrics["net_new_tokens"]:
        raise BenchmarkError(f"{task_id} {condition} net-new token count is stale")
    if statement_only:
        active_seconds = metrics["contestant_active_time"]
        if not _same_number(active_seconds, attempt_active_seconds):
            raise BenchmarkError(
                f"{task_id} {condition} contestant active time is stale"
            )
        expected_system = metrics["retrieval_time"] + active_seconds
    else:
        expected_system = metrics["retrieval_time"] + metrics["formalizer_time"]
    if not _same_number(metrics["system_time"], expected_system):
        raise BenchmarkError(f"{task_id} {condition} system time is internally inconsistent")
    composition = _read_object(composition_path, f"{task_id} {condition} composition packet")
    route_status = report.get("route_status")
    roots = composition.get("retrieved_roots")
    if not isinstance(roots, list):
        raise BenchmarkError(f"{task_id} {condition} composition roots are malformed")
    if roots:
        declaration = roots[0].get("declaration") if isinstance(roots[0], dict) else None
        primary_route = declaration.get("name") if isinstance(declaration, dict) else None
    else:
        primary_route = None
    if route_status not in {"DIRECT_OR_COMPOSITION", "NO_ROUTE"}:
        raise BenchmarkError(f"{task_id} {condition} route status is invalid")
    if composition.get("route_status") != route_status:
        raise BenchmarkError(f"{task_id} {condition} route report disagrees with packet")
    if (route_status == "NO_ROUTE") is not (primary_route is None):
        raise BenchmarkError(f"{task_id} {condition} primary route is inconsistent")
    if not statement_only and report.get("primary_route") != primary_route:
        raise BenchmarkError(f"{task_id} {condition} primary route report is stale")
    hardware_status = _hardware_status(
        report, campaign_envelope, statement_only=statement_only
    )
    if statement_only:
        if audit_record is not None:
            raise BenchmarkError(
                "statement-only campaign cannot be rebound to external audit batch"
            )
        assert isinstance(final_attempt, dict)
        audit = _load_statement_audit(
            condition_root,
            task_id=task_id,
            condition=condition,
            attempt=final_attempt,
        )
        if accepted_condition and (audit is None or audit.get("accepted") is not True):
            raise BenchmarkError(f"{task_id} {condition} faithful status lacks audit evidence")
        audit_usage = report.get("audit_usage_excluded")
        if audit is not None:
            audit["condition_audit_wall_seconds_excluded"] = _number(
                report.get("audit_seconds_excluded_from_contestant"),
                f"{task_id} {condition} excluded audit seconds",
            )
            audit["condition_auditor_total_tokens_excluded"] = (
                audit_usage.get("total_tokens")
                if isinstance(audit_usage, dict)
                and isinstance(audit_usage.get("total_tokens"), int)
                and not isinstance(audit_usage.get("total_tokens"), bool)
                and audit_usage["total_tokens"] >= 0
                else None
            )
            audit["condition_auditor_usage_complete"] = (
                report.get("audit_usage_complete") is True
            )
    else:
        audit = _load_audit(
            condition_root,
            task_id=task_id,
            condition=condition,
            candidate_sha256=report["candidate_sha256"],
            source_contract=source_contract,
            audit_record=audit_record,
        )
    return {
        "condition_report_path": str(report_path),
        "condition_report_sha256": sha256_file(report_path),
        "condition": condition,
        "result_status": report.get("result_status"),
        "faithfulness_status": report.get("faithfulness_status"),
        "corpus_id": report.get("corpus_id"),
        "route_status": route_status,
        "primary_route": primary_route,
        "library_olean_visible": report.get("library_olean_visible"),
        "numstability_name_mentions": report.get("numstability_name_mentions"),
        "metrics": metrics,
        "hardware_status": hardware_status,
        "hardware_snapshot": report.get("hardware_snapshot"),
        "candidate_sha256": report["candidate_sha256"],
        "audit": audit,
    }


def _task_admission(
    stratum: str, conditions: Mapping[str, Any], *, pair_status: str
) -> dict[str, Any]:
    if pair_status == "PAIR_INCIDENT":
        return {
            "pair_report_authenticated": True,
            "compiled_and_integrity_validated": False,
            "full_audit_status": "NOT_DECIDED_INFRASTRUCTURE",
            "analysis_admission": "INFRASTRUCTURE_INCIDENT_EXCLUDED",
            "audited_faithful_pair": False,
            "effect_analysis_eligible": False,
            "scientific_status": SCIENTIFIC_STATUS,
        }
    audits = [conditions[name]["audit"] for name in CONDITIONS]
    if any(
        audit is not None and audit.get("status") == "AUDIT_INCIDENT"
        for audit in audits
    ):
        audit_status = "AUDIT_INCIDENT"
    elif all(
        audit is not None and audit.get("status") == "AUDIT_COMPLETED"
        for audit in audits
    ):
        audit_status = (
            "BOTH_FAITHFUL"
            if all(audit["accepted"] for audit in audits if audit is not None)
            else "AT_LEAST_ONE_UNFAITHFUL"
        )
    elif any(audit is not None for audit in audits):
        audit_status = "PARTIAL_FULL_AUDIT"
    else:
        audit_status = "NOT_FULLY_AUDITED"
    if stratum == "primary_engineering":
        if pair_status == AUDITED_FAITHFUL and audit_status == "BOTH_FAITHFUL":
            analysis_admission = "PRIMARY_EXPLORATORY_FAITHFUL_PAIR"
        elif (
            pair_status == "FORMALIZATION_FROZEN_PENDING_AUDIT"
            and audit_status == "BOTH_FAITHFUL"
        ):
            analysis_admission = "PRIMARY_PROOF_EXTERNALLY_AUDITED_NO_EFFECT_COUNT"
        else:
            analysis_admission = {
                "BOTH_FAITHFUL": "PRIMARY_EXPLORATORY_NOT_ADMITTED",
                "AT_LEAST_ONE_UNFAITHFUL": (
                    "PRIMARY_EXPLORATORY_UNFAITHFUL_NOT_ADMITTED"
                ),
                "PARTIAL_FULL_AUDIT": "PRIMARY_EXPLORATORY_AUDIT_PENDING",
                "NOT_FULLY_AUDITED": "PRIMARY_EXPLORATORY_AUDIT_PENDING",
                "AUDIT_INCIDENT": "PRIMARY_EXPLORATORY_AUDIT_INCIDENT",
            }[audit_status]
    elif stratum == "negative_control":
        analysis_admission = (
            "NEGATIVE_CONTROL_ONLY"
            if audit_status == "BOTH_FAITHFUL"
            else "NEGATIVE_CONTROL_NOT_FAITHFULLY_ADMITTED"
        )
    else:
        analysis_admission = "EXCLUDED_DIAGNOSTIC_ONLY"
    return {
        "pair_report_authenticated": True,
        "compiled_and_integrity_validated": True,
        "full_audit_status": audit_status,
        "analysis_admission": analysis_admission,
        "audited_faithful_pair": pair_status == AUDITED_FAITHFUL,
        "effect_analysis_eligible": (
            stratum == "primary_engineering" and pair_status == AUDITED_FAITHFUL
        ),
        "scientific_status": SCIENTIFIC_STATUS,
    }


def _validate_pair(
    pair_root: Path,
    *,
    manifest: Mapping[str, Any],
    task: Mapping[str, Any],
    started: Mapping[str, Any],
    terminal: Mapping[str, Any],
    campaign_envelope: Mapping[str, Any],
    expected_benchmark_object: str,
    expected_source_contract: str,
    audit_index: Mapping[tuple[str, str], Mapping[str, Any]],
) -> dict[str, Any]:
    task_id = str(task["task_id"])
    if (
        pair_root.parent.is_symlink()
        or not pair_root.parent.is_dir()
        or pair_root.parent.parent.is_symlink()
    ):
        raise BenchmarkError(f"{task_id} task root is missing or unsafe")
    report_path = pair_root / "pair-report.json"
    report = _read_object(report_path, f"{task_id} pair report")
    details = terminal.get("details")
    if not isinstance(details, dict):
        raise BenchmarkError(f"{task_id} terminal state lacks pair details")
    expected_digest = details.get("pair_report_sha256")
    if sha256_file(report_path) != expected_digest:
        raise BenchmarkError(f"{task_id} pair report does not match terminal state")
    terminal_outcome = terminal.get("outcome")
    expected_event_and_status = {
        AUDIT_PENDING: (
            {"TASK_FORMALIZATION_COMPLETE", "TASK_RECOVERED_FORMALIZATION_COMPLETE"},
            "FORMALIZATION_FROZEN_PENDING_AUDIT",
            "NOT_AUDITED",
        ),
        AUDITED_FAITHFUL: (
            {"TASK_AUDITED_FAITHFUL", "TASK_RECOVERED_AUDITED_FAITHFUL"},
            AUDITED_FAITHFUL,
            "BOTH_FAITHFUL",
        ),
        AUDITED_INELIGIBLE: (
            {"TASK_AUDITED_INELIGIBLE", "TASK_RECOVERED_AUDITED_INELIGIBLE"},
            AUDITED_INELIGIBLE,
            "PAIR_NOT_BOTH_FAITHFUL",
        ),
        ATTESTED_PAIR_INCIDENT: (
            {"TASK_INCIDENT", "TASK_RECOVERED_INCIDENT"},
            "PAIR_INCIDENT",
            "NOT_DECIDED_INFRASTRUCTURE",
        ),
    }
    if terminal_outcome not in expected_event_and_status:
        raise BenchmarkError(f"{task_id} has an invalid nonincident terminal outcome")
    event_types, expected_pair_status, expected_faithfulness = expected_event_and_status[
        terminal_outcome
    ]
    if (
        report.get("schema_version") != PAIR_SCHEMA
        or report.get("scientific_status") != SCIENTIFIC_STATUS
        or report.get("task_id") != task_id
        or report.get("pair_status") != expected_pair_status
        or report.get("faithfulness_status") != expected_faithfulness
        or terminal.get("event_type") not in event_types
        or report.get("condition_order") != task.get("condition_order")
        or report.get("conditions_run_sequentially") is not True
    ):
        raise BenchmarkError(f"{task_id} pair report is malformed or inadmissible")
    prompt_sha256 = report.get("prompt_sha256")
    _validate_artifact(pair_root / "prompt.txt", prompt_sha256, f"{task_id} prompt")
    source_contract = report.get("source_contract")
    benchmark_object = report.get("benchmark_object")
    if (
        source_contract != expected_source_contract
        or benchmark_object != expected_benchmark_object
    ):
        raise BenchmarkError(f"{task_id} pair does not match the campaign benchmark contract")
    embedded = report.get("condition_reports")
    if not isinstance(embedded, dict) or set(embedded) != set(CONDITIONS):
        raise BenchmarkError(f"{task_id} pair lacks the two matched conditions")
    conditions = {
        condition: _validate_condition(
            pair_root / condition,
            embedded[condition],
            task_id=task_id,
            condition=condition,
            prompt_sha256=prompt_sha256,
            source_contract=source_contract,
            benchmark_object=benchmark_object,
            campaign_envelope=campaign_envelope,
            audit_record=audit_index.get((task_id, condition)),
        )
        for condition in CONDITIONS
    }
    computed_ratios: dict[str, float | None] = {}
    for output_name in ("contestant_active_time", *METRICS.values()):
        computed_ratios[f"r1_over_r0_{output_name}"] = _ratio(
            conditions["R1"]["metrics"][output_name],
            conditions["R0"]["metrics"][output_name],
        )
    stored = report.get("comparison")
    runner_comparison_available = expected_pair_status in {
        "FORMALIZATION_FROZEN_PENDING_AUDIT",
        AUDITED_FAITHFUL,
    }
    expected_stored = {
        "r1_over_r0_contestant_system_wall": (
            computed_ratios["r1_over_r0_system_time"]
            if runner_comparison_available
            else None
        ),
        "r1_over_r0_contestant_active": (
            computed_ratios["r1_over_r0_contestant_active_time"]
            if runner_comparison_available
            else None
        ),
        "r1_over_r0_formalizer_wall": (
            computed_ratios["r1_over_r0_formalizer_time"]
            if runner_comparison_available
            else None
        ),
        "r1_over_r0_net_new_tokens": (
            computed_ratios["r1_over_r0_net_new_tokens"]
            if runner_comparison_available
            else None
        ),
        "r1_over_r0_candidate_lines": (
            computed_ratios["r1_over_r0_candidate_lines"]
            if runner_comparison_available
            else None
        ),
    }
    if (
        not isinstance(stored, dict)
        or stored.get("effect_analysis_eligible") is not runner_comparison_available
        or any(
            not _same_optional_number(stored.get(key), value)
            for key, value in expected_stored.items()
        )
    ):
        raise BenchmarkError(f"{task_id} stored pair comparison is stale")
    ratios = None
    if runner_comparison_available:
        ratios = {
            key: value
            for key, value in computed_ratios.items()
            if key != "r1_over_r0_contestant_active_time"
            or expected_pair_status == AUDITED_FAITHFUL
        }
    attestation = _validate_pair_attestation(
        task_root=pair_root.parent,
        pair_root=pair_root,
        manifest=manifest,
        task=task,
        started=started,
        terminal=terminal,
        pair_report=report,
    )
    admission = _task_admission(
        str(task["stratum"]), conditions, pair_status=str(report["pair_status"])
    )
    if (
        terminal_outcome == AUDITED_FAITHFUL
        and admission["full_audit_status"] != "BOTH_FAITHFUL"
    ):
        raise BenchmarkError(f"{task_id} audited-faithful terminal lacks two faithful audits")
    if (
        terminal_outcome == AUDITED_INELIGIBLE
        and admission["full_audit_status"] == "BOTH_FAITHFUL"
    ):
        raise BenchmarkError(f"{task_id} ineligible terminal contradicts condition audits")
    if terminal_outcome == ATTESTED_PAIR_INCIDENT and not any(
        condition["faithfulness_status"] == "NOT_DECIDED_INFRASTRUCTURE"
        for condition in conditions.values()
    ):
        raise BenchmarkError(
            f"{task_id} infrastructure terminal lacks an infrastructure condition"
        )
    return {
        "task_id": task_id,
        "campaign_outcome": terminal_outcome,
        "stratum": task["stratum"],
        "readiness_decision": task.get("readiness_decision"),
        "coverage_stratum": task.get("coverage_stratum"),
        "condition_order": task["condition_order"],
        "pair_report_path": str(report_path),
        "pair_report_sha256": sha256_file(report_path),
        "pair_status": report["pair_status"],
        "pair_attestation": attestation,
        "benchmark_object": benchmark_object,
        "source_contract": source_contract,
        "conditions": conditions,
        "ratios": ratios,
        "runner_comparison_available": runner_comparison_available,
        "primary_effect_metric": "contestant_active_time",
        "primary_effect_ratio": (
            computed_ratios["r1_over_r0_contestant_active_time"]
            if expected_pair_status == AUDITED_FAITHFUL
            else None
        ),
        "ratio_interpretation": "values below 1 favor R1; values above 1 favor R0",
        "admission": admission,
    }


def _incident_task(task: Mapping[str, Any], terminal: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "task_id": task["task_id"],
        "campaign_outcome": "INCIDENT",
        "stratum": task["stratum"],
        "readiness_decision": task.get("readiness_decision"),
        "coverage_stratum": task.get("coverage_stratum"),
        "condition_order": task["condition_order"],
        "terminal_event_type": terminal.get("event_type"),
        "incident_details": terminal.get("details"),
        "conditions": None,
        "ratios": None,
        "admission": {
            "pair_report_authenticated": False,
            "compiled_and_integrity_validated": False,
            "full_audit_status": "NOT_APPLICABLE_INCIDENT",
            "analysis_admission": "INCIDENT_EXCLUDED",
            "scientific_status": SCIENTIFIC_STATUS,
        },
    }


def _validate_pair_attestation(
    *,
    task_root: Path,
    pair_root: Path,
    manifest: Mapping[str, Any],
    task: Mapping[str, Any],
    started: Mapping[str, Any],
    terminal: Mapping[str, Any],
    pair_report: Mapping[str, Any],
) -> dict[str, Any]:
    task_id = str(task["task_id"])
    pair_nonce = started.get("pair_nonce")
    if (
        started.get("task_id") != task_id
        or started.get("campaign_identity_sha256")
        != manifest.get("campaign_identity_sha256")
        or started.get("campaign_nonce") != manifest.get("campaign_nonce")
        or not isinstance(pair_nonce, str)
        or len(pair_nonce) != 64
    ):
        raise BenchmarkError(f"{task_id} TASK_STARTED identity is malformed")
    path = task_root / PAIR_ATTESTATION
    attestation = _read_object(path, f"{task_id} campaign pair attestation")
    closure = _pair_artifact_closure(pair_root)
    closure_sha256 = _canonical_hash({"files": closure})
    details = terminal.get("details")
    if not isinstance(details, dict):
        raise BenchmarkError(f"{task_id} terminal lacks attestation details")
    expected = {
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "campaign_nonce": manifest["campaign_nonce"],
        "pair_nonce": pair_nonce,
        "task_id": task_id,
        "condition_order": task["condition_order"],
        "benchmark_object": manifest["campaign_core"]["formalizer"][
            "benchmark_object"
        ],
        "source_contract": manifest["campaign_core"]["formalizer"][
            "source_contract"
        ],
        "pair_status": pair_report["pair_status"],
        "pair_report_sha256": sha256_file(pair_root / "pair-report.json"),
        "pair_artifact_closure": closure,
        "pair_artifact_closure_sha256": closure_sha256,
        "runner_return_code": 0,
    }
    if (
        attestation.get("schema_version")
        != "formalization-design16-campaign-pair-attestation-1"
        or any(attestation.get(key) != value for key, value in expected.items())
        or details.get("pair_attestation_sha256") != sha256_file(path)
        or details.get("pair_artifact_closure_sha256") != closure_sha256
    ):
        raise BenchmarkError(f"{task_id} pair attestation is stale")
    for filename, field in (
        ("runner.stdout.log", "runner_stdout_sha256"),
        ("runner.stderr.log", "runner_stderr_sha256"),
    ):
        log = task_root / filename
        if log.is_symlink() or not log.is_file() or attestation.get(field) != sha256_file(log):
            raise BenchmarkError(f"{task_id} attested runner log changed")
    return {
        "path": str(path),
        "sha256": sha256_file(path),
        "pair_artifact_closure_sha256": closure_sha256,
    }


def _pending_task(task: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "task_id": task["task_id"],
        "campaign_outcome": "PENDING",
        "stratum": task["stratum"],
        "readiness_decision": task.get("readiness_decision"),
        "coverage_stratum": task.get("coverage_stratum"),
        "condition_order": task["condition_order"],
        "conditions": None,
        "ratios": None,
        "admission": {
            "pair_report_authenticated": False,
            "compiled_and_integrity_validated": False,
            "full_audit_status": "NOT_RUN",
            "analysis_admission": "PENDING",
            "scientific_status": SCIENTIFIC_STATUS,
        },
    }


def build_report(
    campaign_root: Path, audit_batch_root: Path | None = None
) -> dict[str, Any]:
    requested = campaign_root.expanduser()
    if requested.is_symlink() or not requested.is_dir():
        raise BenchmarkError("campaign root is missing or unsafe")
    root = requested.resolve()
    manifest, events, authentication = _authenticate_campaign(root)
    audit_index, audit_batch_authentication = _authenticate_audit_batch(
        audit_batch_root,
        campaign_root=root,
        campaign_authentication=authentication,
    )
    core = manifest["campaign_core"]
    terminals = _terminal_by_task(events)
    starts: dict[str, Mapping[str, Any]] = {}
    for event in events:
        if event.get("event_type") != "TASK_STARTED":
            continue
        task_id = event.get("task_id")
        if task_id not in EXPECTED_TASKS or task_id in starts:
            raise BenchmarkError("campaign has a duplicate or malformed TASK_STARTED event")
        starts[str(task_id)] = event
    campaign_envelope = core.get("hardware_envelope")
    if not isinstance(campaign_envelope, dict):
        raise BenchmarkError("campaign hardware envelope is malformed")
    formalizer = core.get("formalizer")
    if not isinstance(formalizer, dict):
        raise BenchmarkError("campaign formalizer contract is malformed")
    benchmark_object = formalizer.get("benchmark_object")
    source_contract = formalizer.get("source_contract")
    campaign_kind = CAMPAIGN_KINDS.get((benchmark_object, source_contract))
    if campaign_kind is None:
        raise BenchmarkError("campaign benchmark object/source contract combination is invalid")
    strata: dict[str, Any] = {}
    for stratum in EXPECTED_STRATA:
        task_reports: list[dict[str, Any]] = []
        for task in core["plan"]:
            if task["stratum"] != stratum:
                continue
            task_id = task["task_id"]
            terminal = terminals.get(task_id)
            if terminal is None:
                item = _pending_task(task)
            elif terminal.get("outcome") in {
                AUDIT_PENDING,
                AUDITED_FAITHFUL,
                AUDITED_INELIGIBLE,
                ATTESTED_PAIR_INCIDENT,
            }:
                if task_id not in starts:
                    raise BenchmarkError(f"{task_id} terminal has no TASK_STARTED record")
                item = _validate_pair(
                    root / "tasks" / task_id / "pair",
                    manifest=manifest,
                    task=task,
                    started=starts[task_id],
                    terminal=terminal,
                    campaign_envelope=campaign_envelope,
                    expected_benchmark_object=benchmark_object,
                    expected_source_contract=source_contract,
                    audit_index=audit_index,
                )
            elif terminal.get("outcome") == "INCIDENT":
                item = _incident_task(task, terminal)
            else:
                raise BenchmarkError(f"{task_id} terminal event has an invalid outcome")
            task_reports.append(item)
        strata[stratum] = {
            "comparison_policy": "SEPARATE_STRATUM_ONLY",
            "task_count": len(task_reports),
            "formalization_frozen_count": sum(
                item["campaign_outcome"]
                in {AUDIT_PENDING, AUDITED_FAITHFUL, AUDITED_INELIGIBLE}
                for item in task_reports
            ),
            "incident_count": sum(
                item["campaign_outcome"] in {"INCIDENT", ATTESTED_PAIR_INCIDENT}
                for item in task_reports
            ),
            "authenticated_infrastructure_incident_count": sum(
                item["campaign_outcome"] == ATTESTED_PAIR_INCIDENT
                for item in task_reports
            ),
            "pending_count": sum(
                item["campaign_outcome"] == "PENDING" for item in task_reports
            ),
            "both_faithful_count": sum(
                item["admission"]["full_audit_status"] == "BOTH_FAITHFUL"
                for item in task_reports
            ),
            "audit_pending_count": sum(
                item["campaign_outcome"]
                == AUDIT_PENDING
                and item["admission"]["full_audit_status"]
                in {"NOT_FULLY_AUDITED", "PARTIAL_FULL_AUDIT"}
                for item in task_reports
            ),
            "audited_unfaithful_count": sum(
                item["admission"]["full_audit_status"]
                == "AT_LEAST_ONE_UNFAITHFUL"
                for item in task_reports
            ),
            "audit_incident_count": sum(
                item["admission"]["full_audit_status"] == "AUDIT_INCIDENT"
                for item in task_reports
            ),
            "primary_exploratory_faithful_pair_count": sum(
                item["admission"]["analysis_admission"]
                == "PRIMARY_EXPLORATORY_FAITHFUL_PAIR"
                for item in task_reports
            ),
            "audited_pair_ineligible_count": sum(
                item["campaign_outcome"] == AUDITED_INELIGIBLE
                for item in task_reports
            ),
            "tasks": task_reports,
            "aggregate_treatment_effect": None,
        }
    return {
        "schema_version": REPORT_SCHEMA,
        "generated_at_utc": utc_now(),
        "provider_calls_made": False,
        "campaign_root": str(root),
        "scientific_status": SCIENTIFIC_STATUS,
        "report_status": "AUTHENTICATED_EXPLORATORY_CAMPAIGN_REPORT",
        "campaign_kind": campaign_kind,
        "benchmark_object": benchmark_object,
        "source_contract": source_contract,
        "authentication": authentication,
        "audit_batch_authentication": audit_batch_authentication,
        "hardware_envelope": campaign_envelope,
        "strata": strata,
        "pooled_effect_estimate": None,
        "pooling_policy": (
            "primary-engineering, negative-control, and excluded/collision "
            "diagnostic tasks are reported separately and never pooled"
        ),
    }


def _md(value: Any) -> str:
    if value is None:
        return "—"
    if isinstance(value, float):
        return f"{value:.3f}"
    return str(value).replace("|", "\\|").replace("\n", " ")


def _metric_pair(task: Mapping[str, Any], metric: str) -> str:
    conditions = task.get("conditions")
    if not isinstance(conditions, dict):
        return "—"
    return (
        f"{_md(conditions['R0']['metrics'][metric])} / "
        f"{_md(conditions['R1']['metrics'][metric])}"
    )


def _route(task: Mapping[str, Any], condition: str) -> str:
    conditions = task.get("conditions")
    if not isinstance(conditions, dict):
        return "—"
    value = conditions[condition]
    root = value.get("primary_route")
    return value["route_status"] + (f": {root}" if root else "")


def _audit_label(task: Mapping[str, Any]) -> str:
    conditions = task.get("conditions")
    if not isinstance(conditions, dict):
        return task["admission"]["full_audit_status"]
    labels = []
    for condition in CONDITIONS:
        audit = conditions[condition]["audit"]
        if audit is None:
            label = "not run"
        elif audit.get("status") == "AUDIT_INCIDENT":
            label = "incident"
        else:
            label = str(audit.get("verdict"))
        labels.append(f"{condition}={label}")
    return ", ".join(labels)


def _hardware_label(task: Mapping[str, Any]) -> str:
    conditions = task.get("conditions")
    if not isinstance(conditions, dict):
        return "—"
    return " / ".join(
        f"{condition}={conditions[condition]['hardware_status']}"
        for condition in CONDITIONS
    )


def render_markdown(report: Mapping[str, Any]) -> str:
    auth = report["authentication"]
    audit_auth = report["audit_batch_authentication"]
    lines = [
        f"# {report['campaign_kind'].replace('_', ' ').title()} Campaign Report",
        "",
        f"Status: **{report['scientific_status']}**. This is an authenticated "
        "exploratory report, not a pooled scientific effect estimate.",
        "",
        "## Authentication",
        "",
        "| Evidence | Value |",
        "|---|---|",
        f"| Campaign identity | `{auth['campaign_identity_sha256']}` |",
        f"| Manifest SHA-256 | `{auth['campaign_manifest_sha256']}` |",
        f"| State journal | {auth['state_record_count']} records; `{auth['state_head_sha256']}` |",
        f"| Summary journal | {auth['summary_record_count']} records; "
        f"`{auth['summary_head_sha256']}` |",
        f"| Benchmark object | {_md(report.get('benchmark_object'))} |",
        f"| Source contract | {_md(report.get('source_contract'))} |",
        f"| Hardware envelope | {_md(report.get('hardware_envelope'))} |",
        f"| External audit batch | {_md(audit_auth.get('status'))} |",
        "",
        "Every ratio is R1/R0; values below 1 favor R1. Raw metric cells show R0 / R1. "
        "Contestant-active time is the primary timer and its ratio is emitted only for "
        "an audited-faithful pair. Auditor time and tokens are excluded from benchmark "
        "metrics.",
    ]
    titles = {
        "primary_engineering": "Primary engineering",
        "negative_control": "Negative controls",
        "excluded_collision_or_router_error": "Excluded collision/router diagnostics",
    }
    for name in EXPECTED_STRATA:
        stratum = report["strata"][name]
        lines.extend(
            [
                "",
                f"## {titles[name]}",
                "",
                f"Formalizations frozen {stratum['formalization_frozen_count']}; "
                f"audit-pending {stratum['audit_pending_count']}; incidents "
                f"{stratum['incident_count']} (authenticated infrastructure "
                f"{stratum['authenticated_infrastructure_incident_count']}); not run "
                f"{stratum['pending_count']}; "
                f"both-faithful {stratum['both_faithful_count']}; audited-unfaithful "
                f"{stratum['audited_unfaithful_count']}; audit incidents "
                f"{stratum['audit_incident_count']}. "
                "No aggregate treatment effect is computed.",
                "",
                "| Task | Outcome | Admission | Hardware | Full audit | R0 route | R1 route | "
                "Primary active s R0/R1 (faithful ratio) | "
                "System s R0/R1 (ratio) | Formalizer s R0/R1 (ratio) | "
                "Tokens R0/R1 (ratio) | Lines R0/R1 (ratio) | Retrieval s R0/R1 (ratio) |",
                "|---|---|---|---|---|---|---|---:|---:|---:|---:|---:|---:|",
            ]
        )
        for task in stratum["tasks"]:
            ratios = task.get("ratios") or {}
            cells = []
            for metric in (
                "contestant_active_time",
                "system_time",
                "formalizer_time",
                "net_new_tokens",
                "candidate_lines",
                "retrieval_time",
            ):
                raw = _metric_pair(task, metric)
                ratio = ratios.get(f"r1_over_r0_{metric}")
                cells.append(f"{raw} ({_md(ratio)})" if raw != "—" else "—")
            lines.append(
                "| "
                + " | ".join(
                    [
                        _md(task["task_id"]),
                        _md(task["campaign_outcome"]),
                        _md(task["admission"]["analysis_admission"]),
                        _md(_hardware_label(task)),
                        _md(_audit_label(task)),
                        _md(_route(task, "R0")),
                        _md(_route(task, "R1")),
                        *cells,
                    ]
                )
                + " |"
            )
    lines.extend(
        [
            "",
            "## Interpretation boundary",
            "",
            report["pooling_policy"] + ". The five excluded/collision diagnostics "
            "cannot be used as treatment-effect evidence, and negative controls remain controls.",
            "",
        ]
    )
    return "\n".join(lines)


def write_report(
    campaign_root: Path,
    output_directory: Path,
    audit_batch_root: Path | None = None,
) -> dict[str, Any]:
    report = build_report(campaign_root, audit_batch_root)
    requested = output_directory.expanduser()
    if requested.exists() or requested.is_symlink():
        raise BenchmarkError("report output directory already exists; refusing overwrite")
    output = requested.resolve()
    output.mkdir(parents=True, mode=0o700)
    json_path = output / "campaign-report.json"
    markdown_path = output / "campaign-report.md"
    _write_json_once(json_path, report)
    _write_bytes_once(markdown_path, render_markdown(report).encode("utf-8"))
    return {
        "output_directory": str(output),
        "json_path": str(json_path),
        "json_sha256": sha256_file(json_path),
        "markdown_path": str(markdown_path),
        "markdown_sha256": sha256_file(markdown_path),
        "campaign_identity_sha256": report["authentication"][
            "campaign_identity_sha256"
        ],
        "provider_calls_made": False,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-root", type=Path, required=True)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument(
        "--audit-batch-root",
        type=Path,
        help="optional external canonical audit-batch root; absence remains audit-pending",
    )
    return parser


def main() -> int:
    try:
        result = write_report(**vars(make_parser().parse_args()))
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Design-16/17 campaign report error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
