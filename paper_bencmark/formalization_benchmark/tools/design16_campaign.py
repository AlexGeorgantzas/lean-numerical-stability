#!/usr/bin/env python3
"""Run the frozen 13-task Design-16 exploratory campaign sequentially.

This is a provider-free control-plane wrapper around ``design16_matched.py``:
it never calls a model itself.  A single host-wide lock prevents two campaign
controllers from running timed contestants concurrently.  State and summaries
are hash-chained JSONL journals, so resume never rewrites prior evidence.

The campaign is explicitly exploratory.  Its two primary engineering tasks,
six negative controls, and five excluded/collision diagnostics are always
reported as separate strata; no pooled treatment estimate is produced.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Callable, Iterator, Mapping, Sequence

from common import BenchmarkError, canonical_json_bytes, sha256_file, utc_now
from manifest_control import ROOT


SCHEMA = "formalization-design16-exploratory-campaign-1"
SCIENTIFIC_STATUS = "UNSCORED_ENGINEERING_EXPLORATORY"
EXPECTED_TASKS = (
    "H22-11",
    "H22-5",
    "H20-6",
    "H7-12",
    "H20-9",
    "H20-8",
    "H23-6",
    "H5-5",
    "H10-7",
    "H12-4",
    "H19-5",
    "H7-14",
    "H15-3",
)
EXPECTED_STRATA = {
    "primary_engineering": ("H5-5", "H10-7"),
    "negative_control": (
        "H22-11",
        "H20-6",
        "H7-12",
        "H12-4",
        "H19-5",
        "H7-14",
    ),
    "excluded_collision_or_router_error": (
        "H22-5",
        "H20-9",
        "H20-8",
        "H23-6",
        "H15-3",
    ),
}
TERMINAL_EVENT_TYPES = frozenset(
    {
        "TASK_COMPLETED",
        "TASK_INCIDENT",
        "TASK_RECOVERED_COMPLETED",
        "TASK_RECOVERED_INCIDENT",
    }
)
HEX40 = re.compile(r"[0-9a-f]{40}")
HEX64 = re.compile(r"[0-9a-f]{64}")


def _read_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"{label} is missing or unsafe: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BenchmarkError(f"cannot read {label}: {error}") from error
    if not isinstance(value, dict):
        raise BenchmarkError(f"{label} is not a JSON object")
    return value


def _canonical_hash(value: Mapping[str, Any]) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _write_once(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, indent=2, sort_keys=True) + "\n"
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        if path.exists() and not path.is_symlink():
            path.unlink()
        raise


def _append_record(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    records = _read_journal(path) if path.exists() else []
    record = dict(payload)
    record["sequence"] = len(records) + 1
    record["previous_record_sha256"] = (
        records[-1]["record_sha256"] if records else None
    )
    digest_input = dict(record)
    record["record_sha256"] = _canonical_hash(digest_input)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Journals are append-only by protocol, but must remain owner-writable for
    # later records and resumed campaigns.
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    with os.fdopen(descriptor, "ab", closefd=True) as stream:
        stream.write(canonical_json_bytes(record))
        stream.flush()
        os.fsync(stream.fileno())
    return record


def _read_journal(path: Path) -> list[dict[str, Any]]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"journal is missing or unsafe: {path}")
    records: list[dict[str, Any]] = []
    previous: str | None = None
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise BenchmarkError(f"malformed journal record {path}:{line_number}") from error
        if not isinstance(value, dict):
            raise BenchmarkError(f"non-object journal record {path}:{line_number}")
        if value.get("sequence") != line_number:
            raise BenchmarkError(f"non-contiguous journal sequence {path}:{line_number}")
        if value.get("previous_record_sha256") != previous:
            raise BenchmarkError(f"broken journal chain {path}:{line_number}")
        observed = value.get("record_sha256")
        if not isinstance(observed, str) or HEX64.fullmatch(observed) is None:
            raise BenchmarkError(f"invalid journal digest {path}:{line_number}")
        unhashed = dict(value)
        unhashed.pop("record_sha256")
        if _canonical_hash(unhashed) != observed:
            raise BenchmarkError(f"stale journal digest {path}:{line_number}")
        previous = observed
        records.append(value)
    return records


def _atlas_identity(root: Path) -> dict[str, Any]:
    if root.is_symlink() or not root.is_dir():
        raise BenchmarkError(f"Mathlib atlas is missing or unsafe: {root}")
    metadata_path = root / "atlas.json"
    declarations_path = root / "declarations.jsonl"
    metadata = _read_object(metadata_path, "Mathlib atlas metadata")
    if declarations_path.is_symlink() or not declarations_path.is_file():
        raise BenchmarkError("Mathlib declarations atlas is missing or unsafe")
    declarations_sha256 = sha256_file(declarations_path)
    if (
        metadata.get("schema_version") != "numstability-library-atlas-2"
        or not isinstance(metadata.get("declaration_count"), int)
        or metadata["declaration_count"] < 1
        or metadata.get("declarations_sha256") != declarations_sha256
    ):
        raise BenchmarkError("Mathlib atlas identity is malformed or stale")
    return {
        "path": str(root.resolve()),
        "metadata_sha256": sha256_file(metadata_path),
        "declarations_sha256": declarations_sha256,
        "schema_version": metadata.get("schema_version"),
        "declaration_count": metadata.get("declaration_count"),
    }


def _runner_identity(runner: Path, commit: str, expected_sha256: str) -> dict[str, Any]:
    if HEX40.fullmatch(commit) is None:
        raise BenchmarkError("runner commit must be a full lowercase 40-digit Git SHA")
    if HEX64.fullmatch(expected_sha256) is None:
        raise BenchmarkError("runner SHA-256 must be 64 lowercase hexadecimal digits")
    if runner.is_symlink() or not runner.is_file():
        raise BenchmarkError(f"runner is missing or unsafe: {runner}")
    runner = runner.resolve()
    if sha256_file(runner) != expected_sha256:
        raise BenchmarkError("working runner does not match the frozen SHA-256")
    try:
        repository = Path(
            subprocess.run(
                ["git", "-C", str(runner.parent), "rev-parse", "--show-toplevel"],
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
        ).resolve()
        canonical_commit = subprocess.run(
            ["git", "-C", str(repository), "rev-parse", f"{commit}^{{commit}}"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        relative = runner.relative_to(repository).as_posix()
        committed_bytes = subprocess.run(
            ["git", "-C", str(repository), "show", f"{commit}:{relative}"],
            check=True,
            capture_output=True,
        ).stdout
    except (subprocess.SubprocessError, ValueError) as error:
        raise BenchmarkError(f"cannot authenticate frozen runner commit: {error}") from error
    if canonical_commit != commit:
        raise BenchmarkError("runner commit is not canonical")
    if hashlib.sha256(committed_bytes).hexdigest() != expected_sha256:
        raise BenchmarkError("runner bytes at the frozen commit do not match SHA-256")
    return {
        "path": str(runner),
        "repository": str(repository),
        "repository_relative_path": relative,
        "commit": commit,
        "sha256": expected_sha256,
    }


def _stratum(decision: str) -> str:
    if decision.startswith("INCLUDE_PRIMARY_ENGINEERING"):
        return "primary_engineering"
    if decision == "NEGATIVE_CONTROL_ONLY":
        return "negative_control"
    return "excluded_collision_or_router_error"


def load_plan(config_path: Path, readiness_path: Path) -> list[dict[str, Any]]:
    config = _read_object(config_path, "frozen condition-order config")
    readiness = _read_object(readiness_path, "Design-16 readiness screen")
    if tuple(readiness.get("task_set", ())) != EXPECTED_TASKS:
        raise BenchmarkError("readiness screen does not contain the exact Higham-13 order")
    raw_tasks = readiness.get("tasks")
    if not isinstance(raw_tasks, list):
        raise BenchmarkError("readiness screen lacks task records")
    by_id = {
        value.get("task_id"): value
        for value in raw_tasks
        if isinstance(value, dict) and isinstance(value.get("task_id"), str)
    }
    orders = config.get("condition_order")
    if not isinstance(orders, dict):
        raise BenchmarkError("config lacks condition_order")
    plan: list[dict[str, Any]] = []
    observed_strata: dict[str, list[str]] = {name: [] for name in EXPECTED_STRATA}
    previous_order: tuple[str, str] | None = None
    translation = {"N": "R0", "L": "R1"}
    for task_id in EXPECTED_TASKS:
        task = by_id.get(task_id)
        if not isinstance(task, dict) or not isinstance(task.get("decision"), str):
            raise BenchmarkError(f"readiness task record is missing: {task_id}")
        raw_order = orders.get(task_id)
        if not isinstance(raw_order, list) or len(raw_order) != 2 or set(raw_order) != {"N", "L"}:
            raise BenchmarkError(f"invalid frozen condition order for {task_id}")
        matched_order = tuple(translation[value] for value in raw_order)
        if previous_order == matched_order:
            raise BenchmarkError("Higham-13 frozen condition orders do not alternate")
        previous_order = matched_order
        stratum = _stratum(task["decision"])
        observed_strata[stratum].append(task_id)
        plan.append(
            {
                "task_id": task_id,
                "condition_order": list(matched_order),
                "legacy_condition_order": list(raw_order),
                "stratum": stratum,
                "readiness_decision": task["decision"],
                "coverage_stratum": task.get("coverage_stratum"),
            }
        )
    if {name: tuple(ids) for name, ids in observed_strata.items()} != EXPECTED_STRATA:
        raise BenchmarkError("readiness strata no longer match the frozen 2/6/5 partition")
    return plan


def _manifest_core(args: argparse.Namespace) -> dict[str, Any]:
    if args.model != "gpt-5.6-sol" or args.reasoning_effort != "xhigh":
        raise BenchmarkError("Design-16 campaign formalizer is frozen to gpt-5.6-sol xhigh")
    positive_limits = {
        "time limit": args.time_limit_seconds,
        "validation timeout": args.validation_timeout_seconds,
        "root limit": args.root_limit,
        "dependency limit": args.dependency_limit,
        "packet-byte limit": args.maximum_packet_bytes,
    }
    if any(not isinstance(value, int) or value < 1 for value in positive_limits.values()):
        raise BenchmarkError("all campaign limits must be positive integers")
    plan = load_plan(args.config, args.readiness)
    core = {
        "schema_version": SCHEMA,
        "scientific_status": SCIENTIFIC_STATUS,
        "tasks_run_sequentially": True,
        "pooled_effect_estimate_forbidden": True,
        "plan": plan,
        "runner": _runner_identity(args.runner, args.runner_commit, args.runner_sha256),
        "mathlib_atlas": _atlas_identity(args.mathlib_atlas.expanduser()),
        "config": {
            "path": str(args.config.resolve()),
            "sha256": sha256_file(args.config),
        },
        "readiness": {
            "path": str(args.readiness.resolve()),
            "sha256": sha256_file(args.readiness),
        },
        "deployment_path": str(args.deployment.resolve()),
        "formalizer": {
            "model": args.model,
            "reasoning_effort": args.reasoning_effort,
            "time_limit_seconds": args.time_limit_seconds,
            "validation_timeout_seconds": args.validation_timeout_seconds,
        },
        "retrieval": {
            "root_limit": args.root_limit,
            "dependency_limit": args.dependency_limit,
            "maximum_packet_bytes": args.maximum_packet_bytes,
        },
    }
    return core


def _load_or_create_manifest(root: Path, core: Mapping[str, Any]) -> dict[str, Any]:
    path = root / "campaign-manifest.json"
    identity = _canonical_hash(core)
    if path.exists() or path.is_symlink():
        manifest = _read_object(path, "campaign manifest")
        observed_core = manifest.get("campaign_core")
        if observed_core != core or manifest.get("campaign_identity_sha256") != identity:
            raise BenchmarkError("campaign manifest does not match the requested frozen inputs")
        return manifest
    manifest = {
        "campaign_core": dict(core),
        "campaign_identity_sha256": identity,
        "created_at_utc": utc_now(),
    }
    _write_once(path, manifest)
    return manifest


def _terminal_by_task(events: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    terminals: dict[str, Mapping[str, Any]] = {}
    for event in events:
        if event.get("event_type") in TERMINAL_EVENT_TYPES:
            task_id = event.get("task_id")
            if task_id not in EXPECTED_TASKS or task_id in terminals:
                raise BenchmarkError("duplicate or malformed terminal task event")
            terminals[task_id] = event
    return terminals


def _summary_payload(
    *,
    manifest: Mapping[str, Any],
    events: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    plan = manifest["campaign_core"]["plan"]
    terminals = _terminal_by_task(events)
    strata: dict[str, Any] = {}
    for stratum in EXPECTED_STRATA:
        entries = [item for item in plan if item["stratum"] == stratum]
        completed = [
            item["task_id"]
            for item in entries
            if terminals.get(item["task_id"], {}).get("outcome") == "COMPLETED"
        ]
        incidents = [
            item["task_id"]
            for item in entries
            if terminals.get(item["task_id"], {}).get("outcome") == "INCIDENT"
        ]
        strata[stratum] = {
            "planned_task_ids": [item["task_id"] for item in entries],
            "completed_task_ids": completed,
            "incident_task_ids": incidents,
            "pending_task_ids": [
                item["task_id"] for item in entries if item["task_id"] not in terminals
            ],
            "completed_count": len(completed),
            "incident_count": len(incidents),
            "pending_count": len(entries) - len(completed) - len(incidents),
            "comparison": "SEPARATE_STRATUM_ONLY",
        }
    return {
        "schema_version": SCHEMA,
        "scientific_status": SCIENTIFIC_STATUS,
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "recorded_at_utc": utc_now(),
        "latest_state_sequence": len(events),
        "latest_state_sha256": events[-1]["record_sha256"] if events else None,
        "strata": strata,
        "pooled_effect_estimate": None,
        "pooling_policy": (
            "primary, negative-control, and excluded/collision strata "
            "must not be pooled"
        ),
    }


def _record_event(root: Path, manifest: Mapping[str, Any], event: Mapping[str, Any]) -> None:
    state_path = root / "campaign-state.jsonl"
    recorded = _append_record(
        state_path,
        {**event, "recorded_at_utc": utc_now(), "schema_version": SCHEMA},
    )
    events = _read_journal(state_path)
    if events[-1]["record_sha256"] != recorded["record_sha256"]:
        raise BenchmarkError("state journal append was not durable")
    _sync_summaries(root, manifest, events)


def _sync_summaries(
    root: Path,
    manifest: Mapping[str, Any],
    events: Sequence[Mapping[str, Any]],
) -> None:
    """Append missing snapshots after a crash between state and summary writes."""

    summary_path = root / "campaign-summary.jsonl"
    summaries = _read_journal(summary_path) if summary_path.exists() else []
    if len(summaries) > len(events):
        raise BenchmarkError("summary journal is ahead of the state journal")
    for index, summary in enumerate(summaries, 1):
        if (
            summary.get("latest_state_sequence") != index
            or summary.get("latest_state_sha256") != events[index - 1].get("record_sha256")
        ):
            raise BenchmarkError("summary journal does not correspond to state history")
    for index in range(len(summaries) + 1, len(events) + 1):
        _append_record(
            summary_path,
            _summary_payload(manifest=manifest, events=events[:index]),
        )


def _pair_status(pair_root: Path, task_id: str) -> tuple[str, dict[str, Any]]:
    report_path = pair_root / "pair-report.json"
    if report_path.is_symlink() or not report_path.is_file():
        return "INCIDENT", {"reason": "pair report is absent"}
    report = _read_object(report_path, "matched pair report")
    if report.get("task_id") != task_id:
        return "INCIDENT", {"reason": "pair report task ID mismatch"}
    status = report.get("pair_status")
    details = {
        "pair_status": status,
        "pair_report_sha256": sha256_file(report_path),
        "pair_report_path": str(report_path),
    }
    if status == "COMPILED_UNAUDITED":
        return "COMPLETED", details
    return "INCIDENT", details


@contextmanager
def _exclusive_host_lock(path: Path) -> Iterator[None]:
    if path.is_symlink():
        raise BenchmarkError("timed-contestant host lock may not be a symlink")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise BenchmarkError("another timed campaign holds the host lock") from error
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _command(args: argparse.Namespace, item: Mapping[str, Any], pair_root: Path) -> list[str]:
    return [
        sys.executable,
        str(args.runner.resolve()),
        "--deployment",
        str(args.deployment.resolve()),
        "--mathlib-atlas",
        str(args.mathlib_atlas.resolve()),
        "--task-id",
        str(item["task_id"]),
        "--condition-order",
        ",".join(item["condition_order"]),
        "--output-root",
        str(pair_root),
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--time-limit-seconds",
        str(args.time_limit_seconds),
        "--validation-timeout-seconds",
        str(args.validation_timeout_seconds),
        "--root-limit",
        str(args.root_limit),
        "--dependency-limit",
        str(args.dependency_limit),
        "--maximum-packet-bytes",
        str(args.maximum_packet_bytes),
    ]


def run_campaign(
    args: argparse.Namespace,
    *,
    process_runner: Callable[..., subprocess.CompletedProcess[Any]] = subprocess.run,
) -> dict[str, Any]:
    core = _manifest_core(args)
    max_new_tasks = getattr(args, "max_new_tasks", None)
    if max_new_tasks is not None and (
        not isinstance(max_new_tasks, int) or max_new_tasks < 1
    ):
        raise BenchmarkError("--max-new-tasks must be a positive integer")
    if args.dry_run:
        invocation_plan = (
            core["plan"][:max_new_tasks] if max_new_tasks is not None else core["plan"]
        )
        return {
            "dry_run": True,
            "writes_performed": False,
            "campaign_root": str(args.campaign_root.resolve()),
            "campaign_identity_sha256": _canonical_hash(core),
            "plan": core["plan"],
            "invocation_plan": invocation_plan,
            "commands": [
                _command(
                    args,
                    item,
                    args.campaign_root.resolve()
                    / "tasks"
                    / item["task_id"]
                    / "pair",
                )
                for item in invocation_plan
            ],
        }

    requested_root = args.campaign_root.expanduser()
    if requested_root.is_symlink():
        raise BenchmarkError("campaign root may not be a symlink")
    root = requested_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    requested_lock = args.host_lock.expanduser().absolute()
    with _exclusive_host_lock(requested_lock):
        manifest = _load_or_create_manifest(root, core)
        state_path = root / "campaign-state.jsonl"
        events = _read_journal(state_path) if state_path.exists() else []
        _sync_summaries(root, manifest, events)
        if not events:
            _record_event(
                root,
                manifest,
                {"event_type": "CAMPAIGN_STARTED", "outcome": "RUNNING"},
            )
            events = _read_journal(state_path)
        terminals = _terminal_by_task(events)
        started = {
            event.get("task_id")
            for event in events
            if event.get("event_type") == "TASK_STARTED"
        }

        terminalized_this_invocation = 0
        for item in core["plan"]:
            task_id = item["task_id"]
            if task_id in terminals:
                continue
            if (
                max_new_tasks is not None
                and terminalized_this_invocation >= max_new_tasks
            ):
                break
            task_root = root / "tasks" / task_id
            pair_root = task_root / "pair"
            # A started event or an existing output tree means a paid call may
            # already have occurred.  Reconcile it; never silently rerun it.
            if task_id in started or pair_root.exists() or pair_root.is_symlink():
                outcome, details = _pair_status(pair_root, task_id)
                _record_event(
                    root,
                    manifest,
                    {
                        "event_type": (
                            "TASK_RECOVERED_COMPLETED"
                            if outcome == "COMPLETED"
                            else "TASK_RECOVERED_INCIDENT"
                        ),
                        "task_id": task_id,
                        "stratum": item["stratum"],
                        "outcome": outcome,
                        "details": details,
                    },
                )
                terminals = _terminal_by_task(_read_journal(state_path))
                terminalized_this_invocation += 1
                continue

            task_root.mkdir(parents=True, mode=0o700)
            command = _command(args, item, pair_root)
            _record_event(
                root,
                manifest,
                {
                    "event_type": "TASK_STARTED",
                    "task_id": task_id,
                    "stratum": item["stratum"],
                    "condition_order": item["condition_order"],
                    "command": command,
                    "outcome": "RUNNING",
                },
            )
            stdout_path = task_root / "runner.stdout.log"
            stderr_path = task_root / "runner.stderr.log"
            try:
                with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                    result = process_runner(command, stdout=stdout, stderr=stderr, check=False)
                return_code = int(result.returncode)
            except Exception as error:
                return_code = None
                process_error = {"type": type(error).__name__, "message": str(error)}
            else:
                process_error = None
            outcome, details = _pair_status(pair_root, task_id)
            details.update(
                {
                    "runner_return_code": return_code,
                    "process_error": process_error,
                    "stdout_sha256": sha256_file(stdout_path),
                    "stderr_sha256": sha256_file(stderr_path),
                }
            )
            if return_code != 0 or process_error is not None:
                outcome = "INCIDENT"
            _record_event(
                root,
                manifest,
                {
                    "event_type": "TASK_COMPLETED" if outcome == "COMPLETED" else "TASK_INCIDENT",
                    "task_id": task_id,
                    "stratum": item["stratum"],
                    "outcome": outcome,
                    "details": details,
                },
            )
            terminals = _terminal_by_task(_read_journal(state_path))
            terminalized_this_invocation += 1

        events = _read_journal(state_path)
        terminals = _terminal_by_task(events)
        if set(terminals) == set(EXPECTED_TASKS) and not any(
            event.get("event_type") == "CAMPAIGN_COMPLETED" for event in events
        ):
            incident_count = sum(
                event.get("outcome") == "INCIDENT" for event in terminals.values()
            )
            _record_event(
                root,
                manifest,
                {
                    "event_type": "CAMPAIGN_COMPLETED",
                    "outcome": "COMPLETE" if incident_count == 0 else "COMPLETE_WITH_INCIDENTS",
                    "completed_task_count": len(EXPECTED_TASKS) - incident_count,
                    "incident_task_count": incident_count,
                },
            )
        final_events = _read_journal(state_path)
        return _summary_payload(manifest=manifest, events=final_events)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--campaign-root", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--runner-commit", required=True)
    parser.add_argument("--runner-sha256", required=True)
    parser.add_argument(
        "--config", type=Path, default=ROOT / "config.json"
    )
    parser.add_argument(
        "--readiness",
        type=Path,
        default=ROOT / "design16" / "higham13_readiness.json",
    )
    parser.add_argument(
        "--host-lock",
        type=Path,
        default=Path("/tmp/highambench-design16-timed-contestant.lock"),
    )
    parser.add_argument("--model", default="gpt-5.6-sol")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--time-limit-seconds", type=int, default=18000)
    parser.add_argument("--validation-timeout-seconds", type=int, default=600)
    parser.add_argument("--root-limit", type=int, default=3)
    parser.add_argument("--dependency-limit", type=int, default=5)
    parser.add_argument("--maximum-packet-bytes", type=int, default=48 * 1024)
    parser.add_argument(
        "--max-new-tasks",
        type=int,
        help="stop after this many previously nonterminal tasks; resume later",
    )
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    result = run_campaign(make_parser().parse_args())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Design-16 campaign error: {error}", file=sys.stderr)
        raise SystemExit(2)
