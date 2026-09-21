#!/usr/bin/env python3
"""Audit every completed condition in a terminal Design-16 campaign.

This provider-free control plane invokes ``design16_full_audit.py`` as a
subprocess.  It authenticates the completed timed-campaign journal and matched
pair artifacts before any auditor starts.  Audit subprocesses may run in
parallel, but no audit is permitted while the campaign or a timed task is
running.

Every paid audit has a unique, condition-local output directory.  The batch
journal is append-only and hash-chained.  On resume an audit with a recorded
start is reconciled from its sealed result, or terminalized as an incident; it
is never silently rerun.
"""

from __future__ import annotations

import argparse
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any, Callable, Iterator, Mapping, Sequence

from common import BenchmarkError, canonical_json_bytes, sha256_file, utc_now
from design16_campaign import (
    EXPECTED_TASKS,
    SCHEMA as CAMPAIGN_SCHEMA,
    TERMINAL_EVENT_TYPES,
    _append_record,
    _read_journal,
    _read_object,
)


SCHEMA = "formalization-design16-audit-batch-1"
CONDITION_TO_COMPILER = {"R0": "N", "R1": "L"}
SOURCE_CONTRACTS = frozenset(
    {
        "statement-only-single-target-sorry",
        "complete-kernel-checked-proof",
    }
)
PROOF_SOURCE_CONTRACT = "complete-kernel-checked-proof"
CAMPAIGN_AUDIT_PENDING_OUTCOME = "FORMALIZATION_COMPLETE_AUDIT_PENDING"
PAIR_STATUS_BY_CAMPAIGN_OUTCOME = {
    CAMPAIGN_AUDIT_PENDING_OUTCOME: frozenset(
        {"FORMALIZATION_FROZEN_PENDING_AUDIT"}
    ),
}
CAMPAIGN_TERMINAL_OUTCOMES = frozenset(
    {"AUDIT_PENDING", "FORMALIZATION_COMPLETE_WITH_INCIDENTS"}
)
TERMINAL_AUDIT_EVENTS = frozenset(
    {
        "AUDIT_COMPLETED",
        "AUDIT_INCIDENT",
        "AUDIT_RECOVERED_COMPLETED",
        "AUDIT_RECOVERED_INCIDENT",
    }
)


def _canonical_hash(value: Mapping[str, Any]) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _write_once(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as stream:
            stream.write(json.dumps(value, indent=2, sort_keys=True) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        if path.exists() and not path.is_symlink():
            path.unlink()
        raise


def _safe_file(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"{label} is missing or unsafe: {path}")
    return path.resolve()


@contextmanager
def _exclusive_batch_lock(path: Path) -> Iterator[None]:
    if path.is_symlink():
        raise BenchmarkError("audit batch controller lock may not be a symlink")
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise BenchmarkError("another audit batch controller is running") from error
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _authenticate_summary_journal(
    campaign_root: Path, events: Sequence[Mapping[str, Any]]
) -> None:
    summary_path = campaign_root / "campaign-summary.jsonl"
    summaries = _read_journal(summary_path)
    if len(summaries) != len(events):
        raise BenchmarkError("campaign summary journal is not caught up to campaign state")
    for index, (summary, event) in enumerate(zip(summaries, events), 1):
        if (
            summary.get("latest_state_sequence") != index
            or summary.get("latest_state_sha256") != event.get("record_sha256")
        ):
            raise BenchmarkError("campaign summary journal does not authenticate state")


def _pair_artifact_closure(pair_root: Path) -> list[dict[str, Any]]:
    if pair_root.is_symlink() or not pair_root.is_dir():
        raise BenchmarkError("matched pair root is missing or unsafe")
    records: list[dict[str, Any]] = []
    for path in sorted(pair_root.rglob("*")):
        if path.is_symlink():
            raise BenchmarkError(f"matched pair artifact may not be a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkError(f"matched pair contains a non-regular artifact: {path}")
        records.append(
            {
                "relative_path": path.relative_to(pair_root).as_posix(),
                "sha256": sha256_file(path),
                "size_bytes": path.stat().st_size,
            }
        )
    if not records:
        raise BenchmarkError("matched pair artifact closure is empty")
    return records


def _authenticate_pair_attestation(
    *,
    campaign_root: Path,
    manifest: Mapping[str, Any],
    item: Mapping[str, Any],
    start: Mapping[str, Any],
    terminal: Mapping[str, Any],
    pair_report: Mapping[str, Any],
    pair_report_path: Path,
) -> dict[str, Any]:
    task_id = str(item["task_id"])
    task_root = campaign_root / "tasks" / task_id
    pair_root = task_root / "pair"
    path = _safe_file(
        task_root / "campaign-pair-attestation.json", "campaign pair attestation"
    )
    attestation = _read_object(path, "campaign pair attestation")
    closure = _pair_artifact_closure(pair_root)
    closure_sha256 = _canonical_hash({"files": closure})
    core = manifest["campaign_core"]
    expected = {
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "campaign_nonce": manifest["campaign_nonce"],
        "pair_nonce": start.get("pair_nonce"),
        "task_id": task_id,
        "condition_order": item.get("condition_order"),
        "benchmark_object": core["formalizer"]["benchmark_object"],
        "source_contract": core["formalizer"]["source_contract"],
        "pair_status": pair_report.get("pair_status"),
        "pair_report_sha256": sha256_file(pair_report_path),
        "pair_artifact_closure": closure,
        "pair_artifact_closure_sha256": closure_sha256,
    }
    if (
        attestation.get("schema_version")
        != "formalization-design16-campaign-pair-attestation-1"
        or any(attestation.get(key) != value for key, value in expected.items())
    ):
        raise BenchmarkError(f"campaign pair attestation changed: {task_id}")
    if (
        start.get("campaign_identity_sha256") != manifest["campaign_identity_sha256"]
        or start.get("campaign_nonce") != manifest["campaign_nonce"]
        or start.get("condition_order") != item.get("condition_order")
        or start.get("benchmark_object") != core["formalizer"]["benchmark_object"]
        or start.get("source_contract") != core["formalizer"]["source_contract"]
    ):
        raise BenchmarkError(f"campaign task start identity changed: {task_id}")
    pair_nonce = start.get("pair_nonce")
    if (
        not isinstance(pair_nonce, str)
        or len(pair_nonce) != 64
        or any(character not in "0123456789abcdef" for character in pair_nonce)
    ):
        raise BenchmarkError(f"campaign pair nonce is malformed: {task_id}")
    stdout_path = _safe_file(task_root / "runner.stdout.log", "pair runner stdout")
    stderr_path = _safe_file(task_root / "runner.stderr.log", "pair runner stderr")
    details = terminal.get("details")
    if (
        attestation.get("runner_return_code") != 0
        or attestation.get("runner_stdout_sha256") != sha256_file(stdout_path)
        or attestation.get("runner_stderr_sha256") != sha256_file(stderr_path)
        or not isinstance(attestation.get("created_at_utc"), str)
        or not isinstance(details, dict)
        or details.get("pair_attestation_sha256") != sha256_file(path)
        or details.get("pair_artifact_closure_sha256") != closure_sha256
    ):
        raise BenchmarkError(f"campaign pair runner attestation changed: {task_id}")
    return {
        "pair_attestation": str(path),
        "pair_attestation_sha256": sha256_file(path),
        "pair_artifact_closure_sha256": closure_sha256,
    }


def _campaign_terminals(
    events: Sequence[Mapping[str, Any]],
) -> dict[str, Mapping[str, Any]]:
    terminals: dict[str, Mapping[str, Any]] = {}
    started: set[str] = set()
    campaign_completed: list[Mapping[str, Any]] = []
    for event in events:
        if event.get("schema_version") != CAMPAIGN_SCHEMA:
            raise BenchmarkError("campaign state contains a foreign schema")
        event_type = event.get("event_type")
        task_id = event.get("task_id")
        if event_type == "TASK_STARTED":
            if task_id not in EXPECTED_TASKS or task_id in started:
                raise BenchmarkError("campaign contains duplicate or malformed task starts")
            started.add(str(task_id))
        elif event_type in TERMINAL_EVENT_TYPES:
            if task_id not in EXPECTED_TASKS or task_id in terminals:
                raise BenchmarkError("campaign contains duplicate or malformed task terminals")
            terminals[str(task_id)] = event
        elif event_type == "CAMPAIGN_FORMALIZATION_COMPLETE":
            campaign_completed.append(event)
    active = sorted(started - set(terminals))
    if active:
        raise BenchmarkError(
            "refusing audits while timed tasks are RUNNING: " + ", ".join(active)
        )
    if len(campaign_completed) != 1 or events[-1] is not campaign_completed[0]:
        raise BenchmarkError("refusing audits while the timed campaign is RUNNING")
    if campaign_completed[0].get("outcome") not in CAMPAIGN_TERMINAL_OUTCOMES:
        raise BenchmarkError("campaign completion outcome is invalid")
    if set(terminals) != set(EXPECTED_TASKS):
        raise BenchmarkError("terminal campaign does not account for the exact Higham-13 set")
    return terminals


def _condition_job(
    *,
    campaign_root: Path,
    task_id: str,
    condition: str,
    pair_report: Mapping[str, Any],
) -> dict[str, Any]:
    pair_root = campaign_root / "tasks" / task_id / "pair"
    condition_root = pair_root / condition
    report_path = _safe_file(condition_root / "report.json", "condition report")
    condition_report = _read_object(report_path, "condition report")
    embedded = pair_report.get("condition_reports", {}).get(condition)
    if not isinstance(embedded, dict) or embedded != condition_report:
        raise BenchmarkError(f"{task_id} {condition} condition report mismatch")
    if (
        condition_report.get("schema_version")
        != "formalization-design17-matched-condition-2"
        or condition_report.get("task_id") != task_id
        or condition_report.get("condition") != condition
        or condition_report.get("result_status")
        != "COMPILED_AND_INTEGRITY_VALIDATED"
        or condition_report.get("validation_pass") is not True
    ):
        raise BenchmarkError(f"{task_id} {condition} is not a completed condition")
    pair_source_contract = pair_report.get("source_contract")
    condition_source_contract = condition_report.get("source_contract")
    if (
        pair_source_contract not in SOURCE_CONTRACTS
        or condition_source_contract != pair_source_contract
    ):
        raise BenchmarkError(f"{task_id} {condition} has an unknown/mismatched source contract")

    candidate = _safe_file(
        condition_root / "submissions" / "01" / "Candidate.lean",
        "frozen candidate",
    )
    candidate_record = condition_report.get("candidate")
    if (
        not isinstance(candidate_record, dict)
        or Path(str(candidate_record.get("path"))).resolve() != candidate
        or candidate_record.get("sha256") != condition_report.get("candidate_sha256")
    ):
        raise BenchmarkError(f"{task_id} {condition} frozen candidate record is invalid")
    paper = _safe_file(
        condition_root / "workspace" / "source" / "paper.pdf", "source PDF"
    )
    source_packet = _safe_file(
        condition_root / "workspace" / "source" / "task.md", "source packet"
    )
    if sha256_file(candidate) != condition_report.get("candidate_sha256"):
        raise BenchmarkError(f"{task_id} {condition} candidate hash changed")
    if sha256_file(paper) != pair_report.get("source_pdf_sha256"):
        raise BenchmarkError(f"{task_id} {condition} source PDF hash changed")
    return {
        "job_id": f"{task_id}:{condition}",
        "task_id": task_id,
        "condition": condition,
        "compiler_condition": CONDITION_TO_COMPILER[condition],
        "candidate": str(candidate),
        "candidate_sha256": sha256_file(candidate),
        "paper": str(paper),
        "paper_sha256": sha256_file(paper),
        "source_packet": str(source_packet),
        "source_packet_sha256": sha256_file(source_packet),
        "condition_report": str(report_path),
        "condition_report_sha256": sha256_file(report_path),
        "source_contract": condition_source_contract,
    }


def authenticate_campaign(campaign_root: Path) -> dict[str, Any]:
    """Return immutable audit jobs after authenticating a terminal campaign."""

    if campaign_root.is_symlink() or not campaign_root.is_dir():
        raise BenchmarkError("campaign root is missing or unsafe")
    root = campaign_root.resolve()
    manifest_path = root / "campaign-manifest.json"
    manifest = _read_object(manifest_path, "campaign manifest")
    core = manifest.get("campaign_core")
    unsigned_manifest = dict(manifest)
    manifest_payload_sha256 = unsigned_manifest.pop("manifest_payload_sha256", None)
    campaign_nonce = manifest.get("campaign_nonce")
    if (
        not isinstance(core, dict)
        or core.get("schema_version") != CAMPAIGN_SCHEMA
        or manifest.get("campaign_identity_sha256") != _canonical_hash(core)
        or not isinstance(campaign_nonce, str)
        or len(campaign_nonce) != 64
        or any(character not in "0123456789abcdef" for character in campaign_nonce)
        or manifest_payload_sha256 != _canonical_hash(unsigned_manifest)
    ):
        raise BenchmarkError("campaign manifest identity is malformed or stale")
    plan = core.get("plan")
    if (
        not isinstance(plan, list)
        or [item.get("task_id") for item in plan if isinstance(item, dict)]
        != list(EXPECTED_TASKS)
    ):
        raise BenchmarkError("campaign manifest plan is not the frozen Higham-13 plan")

    events = _read_journal(root / "campaign-state.jsonl")
    if not events:
        raise BenchmarkError("campaign state journal is empty")
    _authenticate_summary_journal(root, events)
    terminals = _campaign_terminals(events)
    starts = {
        str(event["task_id"]): event
        for event in events
        if event.get("event_type") == "TASK_STARTED"
    }

    jobs: list[dict[str, Any]] = []
    for item in plan:
        task_id = item["task_id"]
        terminal = terminals[task_id]
        terminal_outcome = terminal.get("outcome")
        if terminal_outcome != CAMPAIGN_AUDIT_PENDING_OUTCOME:
            continue
        if core.get("formalizer", {}).get("source_contract") != PROOF_SOURCE_CONTRACT:
            raise BenchmarkError(
                "statement-only pairs must be audited in-run, not by the proof audit batch"
            )
        pair_root = root / "tasks" / task_id / "pair"
        pair_report_path = _safe_file(pair_root / "pair-report.json", "pair report")
        pair_report = _read_object(pair_report_path, "pair report")
        details = terminal.get("details")
        if (
            not isinstance(details, dict)
            or details.get("pair_report_sha256") != sha256_file(pair_report_path)
            or pair_report.get("schema_version")
            != "formalization-design17-matched-pair-2"
            or pair_report.get("task_id") != task_id
            or pair_report.get("pair_status")
            not in PAIR_STATUS_BY_CAMPAIGN_OUTCOME[terminal_outcome]
            or set(pair_report.get("condition_reports", {})) != set(CONDITION_TO_COMPILER)
        ):
            raise BenchmarkError(f"completed pair failed authentication: {task_id}")
        if task_id not in starts:
            raise BenchmarkError(f"completed pair lacks an authenticated start: {task_id}")
        attestation = _authenticate_pair_attestation(
            campaign_root=root,
            manifest=manifest,
            item=item,
            start=starts[task_id],
            terminal=terminal,
            pair_report=pair_report,
            pair_report_path=pair_report_path,
        )
        task_jobs = [
            _condition_job(
                campaign_root=root,
                task_id=task_id,
                condition=condition,
                pair_report=pair_report,
            )
            for condition in ("R0", "R1")
        ]
        if (
            task_jobs[0]["paper_sha256"] != task_jobs[1]["paper_sha256"]
            or task_jobs[0]["source_packet_sha256"]
            != task_jobs[1]["source_packet_sha256"]
            or task_jobs[0]["source_contract"] != task_jobs[1]["source_contract"]
        ):
            raise BenchmarkError(f"matched pair source inputs differ: {task_id}")
        jobs.extend(task_jobs)
        for job in task_jobs:
            job.update(attestation)

    return {
        "campaign_root": str(root),
        "campaign_manifest_sha256": sha256_file(manifest_path),
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "campaign_nonce": campaign_nonce,
        "campaign_state_sequence": len(events),
        "campaign_state_sha256": events[-1]["record_sha256"],
        "deployment_path": core.get("deployment_path"),
        "source_contract": core.get("formalizer", {}).get("source_contract"),
        "jobs": jobs,
    }


def _batch_core(args: argparse.Namespace, campaign: Mapping[str, Any]) -> dict[str, Any]:
    audit_runner = _safe_file(args.audit_runner.expanduser(), "audit runner")
    deployment = _safe_file(args.deployment.expanduser(), "deployment manifest")
    frozen_deployment = campaign.get("deployment_path")
    if (
        not isinstance(frozen_deployment, str)
        or Path(frozen_deployment).expanduser().resolve() != deployment
    ):
        raise BenchmarkError("audit deployment does not match the frozen campaign")
    if not isinstance(args.max_parallel, int) or args.max_parallel < 1:
        raise BenchmarkError("--max-parallel must be a positive integer")
    if args.timeout_seconds <= 0 or args.validation_timeout_seconds <= 0:
        raise BenchmarkError("audit timeouts must be positive")
    if args.infrastructure_retries < 0:
        raise BenchmarkError("--infrastructure-retries may not be negative")
    return {
        "schema_version": SCHEMA,
        "provider_free_orchestrator": True,
        "condition_blind_audit_runner": True,
        "campaign": dict(campaign),
        "deployment": {
            "path": str(deployment),
            "sha256": sha256_file(deployment),
        },
        "audit_runner": {
            "path": str(audit_runner),
            "sha256": sha256_file(audit_runner),
        },
        "auditor": {
            "model": args.model,
            "reasoning_effort": args.reasoning_effort,
            "timeout_seconds": args.timeout_seconds,
            "validation_timeout_seconds": args.validation_timeout_seconds,
            "infrastructure_retries": args.infrastructure_retries,
        },
        "maximum_parallel_audits": args.max_parallel,
    }


def _load_or_create_manifest(root: Path, core: Mapping[str, Any]) -> dict[str, Any]:
    path = root / "audit-batch-manifest.json"
    identity = _canonical_hash(core)
    if path.exists() or path.is_symlink():
        manifest = _read_object(path, "audit batch manifest")
        if (
            manifest.get("batch_core") != core
            or manifest.get("batch_identity_sha256") != identity
        ):
            raise BenchmarkError("audit batch manifest does not match requested inputs")
        return manifest
    manifest = {
        "batch_core": dict(core),
        "batch_identity_sha256": identity,
        "created_at_utc": utc_now(),
    }
    _write_once(path, manifest)
    return manifest


def _audit_terminals(
    events: Sequence[Mapping[str, Any]], jobs: Sequence[Mapping[str, Any]]
) -> tuple[dict[str, Mapping[str, Any]], set[str]]:
    valid = {job["job_id"] for job in jobs}
    terminals: dict[str, Mapping[str, Any]] = {}
    started: set[str] = set()
    for event in events:
        if event.get("schema_version") != SCHEMA:
            raise BenchmarkError("audit journal contains a foreign schema")
        event_type = event.get("event_type")
        job_id = event.get("job_id")
        if event_type == "AUDIT_STARTED":
            if job_id not in valid or job_id in started:
                raise BenchmarkError("audit journal contains a duplicate or unknown start")
            started.add(str(job_id))
        elif event_type in TERMINAL_AUDIT_EVENTS:
            if job_id not in valid or job_id in terminals:
                raise BenchmarkError("audit journal contains a duplicate or unknown terminal")
            terminals[str(job_id)] = event
    if set(terminals) - started:
        raise BenchmarkError("audit terminal lacks a corresponding start")
    return terminals, started


def _record_event(root: Path, event: Mapping[str, Any]) -> dict[str, Any]:
    return _append_record(
        root / "audit-state.jsonl",
        {**event, "recorded_at_utc": utc_now(), "schema_version": SCHEMA},
    )


def _result_details(job: Mapping[str, Any], output_root: Path) -> tuple[bool, dict[str, Any]]:
    result_path = output_root / "result.json"
    if result_path.is_symlink() or not result_path.is_file():
        return False, {"reason": "canonical audit result is absent"}
    try:
        result = _read_object(result_path, "canonical audit result")
    except BenchmarkError as error:
        return False, {"reason": str(error)}
    decision = result.get("decision")
    valid = (
        result.get("schema_version") == "formalization-design16-full-audit-run-1"
        and result.get("scientific_status")
        == "CANONICAL_MULTI_ROLE_FAITHFULNESS_AUDIT"
        and result.get("task_id") == job["task_id"]
        and result.get("candidate_sha256") == job["candidate_sha256"]
        and result.get("source_contract") == job["source_contract"]
        and result.get("output_root") == str(output_root.resolve())
        and result.get("condition_blind") is True
        and result.get("attempt_blind") is True
        and isinstance(decision, dict)
        and decision.get("verdict") in {"faithful", "unfaithful"}
        and isinstance(decision.get("accepted"), bool)
        and decision.get("accepted") == (decision.get("verdict") == "faithful")
    )
    details = {
        "result_path": str(result_path.resolve()),
        "result_sha256": sha256_file(result_path),
        "verdict": decision.get("verdict") if isinstance(decision, dict) else None,
        "accepted": decision.get("accepted") if isinstance(decision, dict) else None,
        "condition_blind": result.get("condition_blind"),
    }
    if not valid:
        details["reason"] = "canonical audit result failed identity/blinding checks"
    return valid, details


def _command(
    args: argparse.Namespace, job: Mapping[str, Any], output_root: Path
) -> list[str]:
    command = [
        sys.executable,
        str(args.audit_runner.expanduser().resolve()),
        "--deployment",
        str(args.deployment.expanduser().resolve()),
        "--task-id",
        str(job["task_id"]),
        "--candidate",
        str(job["candidate"]),
        "--paper",
        str(job["paper"]),
        "--source-packet",
        str(job["source_packet"]),
        "--output-root",
        str(output_root),
        "--condition",
        str(job["compiler_condition"]),
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--timeout-seconds",
        str(args.timeout_seconds),
        "--validation-timeout-seconds",
        str(args.validation_timeout_seconds),
        "--infrastructure-retries",
        str(args.infrastructure_retries),
    ]
    return command


def _run_one(
    *,
    command: Sequence[str],
    job: Mapping[str, Any],
    output_root: Path,
    logs_root: Path,
    process_runner: Callable[..., subprocess.CompletedProcess[Any]],
) -> dict[str, Any]:
    label = str(job["job_id"]).replace(":", "-")
    stdout_path = logs_root / f"{label}.stdout.log"
    stderr_path = logs_root / f"{label}.stderr.log"
    process_error: dict[str, str] | None = None
    return_code: int | None
    try:
        with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
            result = process_runner(
                list(command), stdout=stdout, stderr=stderr, check=False
            )
        return_code = int(result.returncode)
    except Exception as error:
        return_code = None
        process_error = {"type": type(error).__name__, "message": str(error)}
    valid, details = _result_details(job, output_root)
    details.update(
        {
            "runner_return_code": return_code,
            "process_error": process_error,
            "stdout_sha256": sha256_file(stdout_path),
            "stderr_sha256": sha256_file(stderr_path),
        }
    )
    audited = return_code == 0 and process_error is None and valid
    return {"audited": audited, "details": details}


def _summary(
    manifest: Mapping[str, Any], events: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    jobs = manifest["batch_core"]["campaign"]["jobs"]
    terminals, _ = _audit_terminals(events, jobs)
    audited = [
        job["job_id"]
        for job in jobs
        if terminals.get(job["job_id"], {}).get("outcome")
        in {"SCIENTIFICALLY_ELIGIBLE", "SCIENTIFICALLY_INELIGIBLE"}
    ]
    eligible = [
        job["job_id"]
        for job in jobs
        if terminals.get(job["job_id"], {}).get("outcome")
        == "SCIENTIFICALLY_ELIGIBLE"
    ]
    ineligible = [
        job["job_id"]
        for job in jobs
        if terminals.get(job["job_id"], {}).get("outcome")
        == "SCIENTIFICALLY_INELIGIBLE"
    ]
    incidents = [
        job["job_id"]
        for job in jobs
        if terminals.get(job["job_id"], {}).get("outcome") == "AUDIT_INCIDENT"
    ]
    return {
        "schema_version": SCHEMA,
        "batch_identity_sha256": manifest["batch_identity_sha256"],
        "eligible_job_count": len(jobs),
        "audited_job_ids": audited,
        "scientifically_eligible_job_ids": eligible,
        "scientifically_ineligible_job_ids": ineligible,
        "incident_job_ids": incidents,
        "pending_job_ids": [
            job["job_id"] for job in jobs if job["job_id"] not in terminals
        ],
        "audited_count": len(audited),
        "scientifically_eligible_count": len(eligible),
        "scientifically_ineligible_count": len(ineligible),
        "incident_count": len(incidents),
        "pending_count": len(jobs) - len(terminals),
        "latest_state_sequence": len(events),
        "latest_state_sha256": events[-1]["record_sha256"] if events else None,
        "auditor_tokens_excluded_from_benchmark": True,
    }


def _run_batch_locked(
    args: argparse.Namespace,
    *,
    process_runner: Callable[..., subprocess.CompletedProcess[Any]] = subprocess.run,
) -> dict[str, Any]:
    campaign = authenticate_campaign(args.campaign_root.expanduser())
    campaign_contract = campaign.get("source_contract")
    if campaign_contract not in SOURCE_CONTRACTS:
        raise BenchmarkError("campaign has an unknown source contract")
    if any(job["source_contract"] != campaign_contract for job in campaign["jobs"]):
        raise BenchmarkError("pair source contract does not match the frozen campaign")
    core = _batch_core(args, campaign)
    requested_root = args.output_root.expanduser()
    if requested_root.is_symlink():
        raise BenchmarkError("audit batch root may not be a symlink")
    root = requested_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    manifest = _load_or_create_manifest(root, core)
    state_path = root / "audit-state.jsonl"
    events = _read_journal(state_path) if state_path.exists() else []
    if not events:
        _record_event(root, {"event_type": "BATCH_STARTED", "outcome": "RUNNING"})
        events = _read_journal(state_path)

    jobs = manifest["batch_core"]["campaign"]["jobs"]
    terminals, started = _audit_terminals(events, jobs)
    if any(event.get("event_type") == "BATCH_COMPLETED" for event in events):
        if len(terminals) != len(jobs):
            raise BenchmarkError("completed audit batch has pending jobs")
        return _summary(manifest, events)

    # Reconcile starts from a previous invocation.  A missing or incomplete
    # result is an incident, not authorization to spend a second auditor call.
    for job in jobs:
        job_id = job["job_id"]
        if job_id not in started or job_id in terminals:
            continue
        output = root / "audits" / job["task_id"] / job["condition"]
        valid, details = _result_details(job, output)
        recovered_outcome = (
            (
                "SCIENTIFICALLY_ELIGIBLE"
                if details.get("accepted") is True
                else "SCIENTIFICALLY_INELIGIBLE"
            )
            if valid
            else "AUDIT_INCIDENT"
        )
        _record_event(
            root,
            {
                "event_type": (
                    "AUDIT_RECOVERED_COMPLETED" if valid else "AUDIT_RECOVERED_INCIDENT"
                ),
                "job_id": job_id,
                "task_id": job["task_id"],
                "outcome": recovered_outcome,
                "details": details,
            },
        )

    events = _read_journal(state_path)
    terminals, started = _audit_terminals(events, jobs)
    pending = [job for job in jobs if job["job_id"] not in terminals]
    logs_root = root / "logs"
    logs_root.mkdir(parents=True, exist_ok=True)
    futures: dict[Future[dict[str, Any]], Mapping[str, Any]] = {}
    pending_iterator = iter(pending)

    def submit(job: Mapping[str, Any], executor: ThreadPoolExecutor) -> None:
        output = root / "audits" / job["task_id"] / job["condition"]
        if output.exists() or output.is_symlink():
            raise BenchmarkError(
                f"fresh audit output root already exists without a start: {output}"
            )
        command = _command(args, job, output)
        _record_event(
            root,
            {
                "event_type": "AUDIT_STARTED",
                "job_id": job["job_id"],
                "task_id": job["task_id"],
                "condition": job["condition"],
                "candidate_sha256": job["candidate_sha256"],
                "output_root": str(output),
                "command": command,
                "outcome": "RUNNING",
            },
        )
        future = executor.submit(
            _run_one,
            command=command,
            job=job,
            output_root=output,
            logs_root=logs_root,
            process_runner=process_runner,
        )
        futures[future] = job

    with ThreadPoolExecutor(max_workers=args.max_parallel) as executor:
        for _ in range(min(args.max_parallel, len(pending))):
            submit(next(pending_iterator), executor)
        while futures:
            future = next(as_completed(tuple(futures)))
            job = futures.pop(future)
            try:
                result = future.result()
            except Exception as error:  # defensive: preserve all other audits
                result = {
                    "audited": False,
                    "details": {
                        "reason": "audit worker failed",
                        "process_error": {
                            "type": type(error).__name__,
                            "message": str(error),
                        },
                    },
                }
            audited = result["audited"] is True
            outcome = (
                (
                    "SCIENTIFICALLY_ELIGIBLE"
                    if result["details"].get("accepted") is True
                    else "SCIENTIFICALLY_INELIGIBLE"
                )
                if audited
                else "AUDIT_INCIDENT"
            )
            _record_event(
                root,
                {
                    "event_type": "AUDIT_COMPLETED" if audited else "AUDIT_INCIDENT",
                    "job_id": job["job_id"],
                    "task_id": job["task_id"],
                    "outcome": outcome,
                    "details": result["details"],
                },
            )
            next_job = next(pending_iterator, None)
            if next_job is not None:
                submit(next_job, executor)

    events = _read_journal(state_path)
    terminals, _ = _audit_terminals(events, jobs)
    if len(terminals) == len(jobs):
        incident_count = sum(
            event.get("outcome") == "AUDIT_INCIDENT" for event in terminals.values()
        )
        _record_event(
            root,
            {
                "event_type": "BATCH_COMPLETED",
                "outcome": (
                    "AUDIT_BATCH_FINISHED"
                    if incident_count == 0
                    else "AUDIT_BATCH_FINISHED_WITH_INCIDENTS"
                ),
                "audited_count": len(jobs) - incident_count,
                "incident_audit_count": incident_count,
            },
        )
    return _summary(manifest, _read_journal(state_path))


def run_batch(
    args: argparse.Namespace,
    *,
    process_runner: Callable[..., subprocess.CompletedProcess[Any]] = subprocess.run,
) -> dict[str, Any]:
    # Fail before creating any batch artifact when the timed campaign is not
    # terminal.  The state is authenticated again under the controller lock.
    authenticate_campaign(args.campaign_root.expanduser())
    requested_root = args.output_root.expanduser()
    if requested_root.is_symlink():
        raise BenchmarkError("audit batch root may not be a symlink")
    root = requested_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    with _exclusive_batch_lock(root / ".controller.lock"):
        return _run_batch_locked(args, process_runner=process_runner)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign-root", type=Path, required=True)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--audit-runner",
        type=Path,
        default=Path(__file__).with_name("design16_full_audit.py"),
    )
    parser.add_argument("--max-parallel", type=int, default=2)
    parser.add_argument("--model", default="gpt-6-astra")
    parser.add_argument("--reasoning-effort", default="high")
    parser.add_argument("--timeout-seconds", type=float, default=7200)
    parser.add_argument("--validation-timeout-seconds", type=float, default=600)
    parser.add_argument("--infrastructure-retries", type=int, default=2)
    return parser


def main() -> int:
    try:
        result = run_batch(make_parser().parse_args())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Design-16 audit batch error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
