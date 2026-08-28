#!/usr/bin/env python3
"""Create or verify an authenticated report for one completed paper shard aggregate.

This is deliberately a scratch-only, read-only consumer of the permanent pair
shards.  It first asks ``aggregate_highambench_pair_shards`` to rebuild and
verify the sealed aggregate index, then projects the authenticated final records
into compact JSON, CSV, and Markdown artifacts.  The output manifest binds every
report byte; ``verify`` reauthenticates the source aggregate and reproduces every
artifact before accepting an existing report.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from decimal import Decimal
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import shutil
import statistics
import sys
from typing import Any, Mapping, Sequence

import aggregate_highambench_pair_shards as aggregate
import manage_highambench_pair_shard as shard


SCHEMA_VERSION = 1
SUMMARY_KIND = "highambench-private-paper-shard-report-summary"
RUNS_KIND = "highambench-private-paper-shard-run-results"
PAIRS_KIND = "highambench-private-paper-shard-pair-results"
FAILURES_KIND = "highambench-private-paper-shard-failed-attempts"
MANIFEST_KIND = "highambench-private-paper-shard-report-manifest"
DATASET_HASH_FIELD = "dataset_sha256"
SUMMARY_HASH_FIELD = "report_summary_sha256"
MANIFEST_HASH_FIELD = "report_manifest_sha256"
MANIFEST_NAME = "report_manifest.json"
ARTIFACT_NAMES = (
    "summary.json",
    "runs.json",
    "runs.csv",
    "pairs.json",
    "pairs.csv",
    "failed_attempts.json",
    "report.md",
)
HEX64_RE = re.compile(r"[0-9a-f]{64}")
SAFE_OUTPUT_NAME_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")

RUN_CSV_FIELDS = (
    "run_id",
    "pair_id",
    "paper_id",
    "task_id",
    "tier",
    "repetition_id",
    "condition",
    "condition_order",
    "order_index",
    "scored",
    "pass",
    "failure_code",
    "failure_note",
    "actual_stop_seconds",
    "scored_elapsed_seconds",
    "first_valid_seconds",
    "model_tokens",
    "input_tokens",
    "cached_input_tokens",
    "output_tokens",
    "thread_count",
    "response_count",
    "appserver_response_count",
    "library_use",
    "library_use_status",
    "library_declaration_count",
    "library_declarations_csv",
    "protocol_complete",
    "agent_id",
    "agent_version",
    "model",
    "reasoning_effort",
    "started_at_utc",
    "finished_at_utc",
    "submission_sha256",
    "allocation_job_id",
    "allocation_hostname",
    "allocation_host_class_sha256",
    "allocation_file_sha256",
    "allocation_record_sha256",
    "freeze_check_sha256",
    "final_record_path",
    "final_file_sha256",
    "matrix_record_sha256",
    "pair_commit_sha256",
    "shard_index_file_sha256",
    "shard_campaign_index_sha256",
)

PAIR_CSV_FIELDS = (
    "pair_id",
    "task_id",
    "tier",
    "repetition_id",
    "condition_order",
    "n_pass",
    "l_pass",
    "l_minus_n_pass",
    "n_scored_seconds",
    "l_scored_seconds",
    "l_minus_n_scored_seconds",
    "n_actual_stop_seconds",
    "l_actual_stop_seconds",
    "l_minus_n_actual_stop_seconds",
    "n_model_tokens",
    "l_model_tokens",
    "l_minus_n_model_tokens",
    "n_failure_code",
    "l_failure_code",
    "allocation_job_id",
    "allocation_hostname",
    "allocation_hardware_path",
    "allocation_file_sha256",
    "allocation_record_sha256",
    "host_class_sha256",
    "scheduler_exclusive",
    "scheduler_sharing_policy",
    "same_authenticated_allocation",
    "prior_failed_attempt_count",
    "prior_failed_attempt_ids",
    "committed_attempt_id",
    "committed_slurm_job_id",
    "committed_at_utc",
    "pair_commit_path",
    "pair_commit_file_sha256",
    "pair_commit_sha256",
)


class ReportError(RuntimeError):
    """The source aggregate or derived report failed closed."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def validate_utc(value: Any, label: str) -> str:
    text = string(value, label)
    if not text.endswith("Z"):
        raise ReportError(f"{label} is not a canonical UTC timestamp")
    try:
        parsed = datetime.fromisoformat(text[:-1] + "+00:00")
    except ValueError as error:
        raise ReportError(f"{label} is not a valid UTC timestamp") from error
    if parsed.utcoffset() != timezone.utc.utcoffset(parsed):
        raise ReportError(f"{label} is not UTC")
    return text


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def bind_hash(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = canonical_sha256(result)
    return result


def verify_bound_hash(value: Mapping[str, Any], field: str, label: str) -> str:
    unsigned = dict(value)
    observed = unsigned.pop(field, None)
    if (
        not isinstance(observed, str)
        or HEX64_RE.fullmatch(observed) is None
        or canonical_sha256(unsigned) != observed
    ):
        raise ReportError(f"{label} self-hash is stale")
    return observed


def mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ReportError(f"{label} is not a JSON object")
    return value


def sequence(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReportError(f"{label} is not a JSON list")
    return value


def string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ReportError(f"{label} is not a nonempty string")
    return value


def optional_string(value: Any, label: str) -> str | None:
    if value is None:
        return None
    return string(value, label)


def integer(value: Any, label: str, *, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ReportError(f"{label} is not an integer >= {minimum}")
    return value


def number(value: Any, label: str, *, minimum: float = 0.0) -> int | float:
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(value)
        or value < minimum
    ):
        raise ReportError(f"{label} is not a number >= {minimum}")
    return value


def optional_number(value: Any, label: str) -> int | float | None:
    if value is None:
        return None
    return number(value, label)


def boolean(value: Any, label: str) -> bool:
    if not isinstance(value, bool):
        raise ReportError(f"{label} is not boolean")
    return value


def hex64(value: Any, label: str) -> str:
    text = string(value, label)
    if HEX64_RE.fullmatch(text) is None:
        raise ReportError(f"{label} is not a lowercase SHA-256")
    return text


def optional_hex64(value: Any, label: str) -> str | None:
    if value is None:
        return None
    return hex64(value, label)


def library_use_projection(
    record: Mapping[str, Any], condition: str, passed: bool, run_id: str
) -> tuple[bool | None, list[str], str]:
    """Preserve the runner's authenticated tri-state library classification.

    ``None`` is not equivalent to ``False``: for a failed L run it records that
    no hidden-validation result existed from which to perform a library audit.
    This mirrors the production report validator's invariants while exposing an
    explicit status for CSV/Markdown consumers.
    """

    library_use = record.get("library_use")
    raw_declarations = record.get("library_declarations")
    if not isinstance(raw_declarations, list) or not all(
        isinstance(item, str) and item for item in raw_declarations
    ):
        raise ReportError(f"{run_id} has incomplete library-use evidence")
    declarations = list(raw_declarations)
    if library_use is not True and library_use is not False and library_use is not None:
        raise ReportError(f"{run_id} has an invalid library-use classification")
    if isinstance(library_use, bool) and (library_use is True) != bool(declarations):
        raise ReportError(f"{run_id} library-use Boolean disagrees with declarations")
    if library_use is None and declarations:
        raise ReportError(f"{run_id} has declarations without a completed library audit")
    if condition == "N":
        if library_use is not False or declarations:
            raise ReportError(f"{run_id} does not preserve condition-N library absence")
    elif condition != "L":
        raise ReportError(f"{run_id} has an invalid condition for library-use evidence")
    elif passed and not isinstance(library_use, bool):
        raise ReportError(f"passing L record lacks a library-use classification: {run_id}")
    status = (
        "used"
        if library_use is True
        else "not_used"
        if library_use is False
        else "not_audited_failed_l_run"
    )
    return library_use, declarations, status


def read_json(path: Path, label: str) -> Mapping[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise ReportError(f"{label} is missing or unsafe: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReportError(f"cannot read {label}: {error}") from error
    return mapping(value, label)


def below(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def validate_output_path(
    output_dir: Path, benchmark_root: Path, shards_root: Path
) -> tuple[Path, Path]:
    """Require one nonlinked direct child of the ignored project scratch area."""

    benchmark = benchmark_root.resolve()
    try:
        project = benchmark.parents[1]
    except IndexError as error:
        raise ReportError("benchmark root has no canonical project parent") from error
    if benchmark != project / "paper_bencmark/highambench":
        raise ReportError("benchmark root is not at its canonical project path")
    scratch = (project / "paper_bencmark/scratch_pad").resolve()
    output = output_dir.absolute()
    if (
        SAFE_OUTPUT_NAME_RE.fullmatch(output.name) is None
        or output.parent.resolve() != scratch
    ):
        raise ReportError(
            "output directory must be one direct, safely named child of "
            "paper_bencmark/scratch_pad"
        )
    shard_resolved = shards_root.resolve()
    output_resolved = output.resolve()
    if below(output_resolved, shard_resolved) or below(shard_resolved, output_resolved):
        raise ReportError("report output must be disjoint from the source shard root")
    if below(output_resolved, benchmark) or below(benchmark, output_resolved):
        raise ReportError("report output must be disjoint from the benchmark release tree")
    return output, scratch


def decimal_delta(left: int | float, right: int | float) -> int | float:
    result = Decimal(str(left)) - Decimal(str(right))
    return int(result) if result == result.to_integral_value() else float(result)


def decimal_sum(values: Sequence[int | float]) -> int | float:
    result = sum((Decimal(str(value)) for value in values), Decimal(0))
    return int(result) if result == result.to_integral_value() else float(result)


def decimal_median(values: Sequence[int | float]) -> int | float | None:
    if not values:
        return None
    result = statistics.median(Decimal(str(value)) for value in values)
    return int(result) if result == result.to_integral_value() else float(result)


def source_relative(project: Path, path: Path, label: str) -> str:
    try:
        return path.resolve().relative_to(project).as_posix()
    except ValueError as error:
        raise ReportError(f"{label} escapes the project") from error


def load_allocation(
    attempt_root: Path,
    descriptor: Mapping[str, Any],
    expected_node: str,
    expected_job: str,
) -> dict[str, Any]:
    relative = shard.safe_relative_path(descriptor.get("path"), "allocation path")
    path = attempt_root / relative
    if path.is_symlink() or not path.is_file():
        raise ReportError("authenticated allocation record is missing or unsafe")
    file_sha = shard.file_sha256(path)
    if file_sha != hex64(descriptor.get("sha256"), "allocation file SHA-256"):
        raise ReportError("allocation descriptor has a stale file SHA-256")
    record = read_json(path, "allocation record")
    try:
        self_hash = shard.verify_self_hash(
            record, "record_sha256", "allocation record"
        )
    except shard.CampaignError as error:
        raise ReportError(str(error)) from error
    if (
        self_hash
        != hex64(descriptor.get("record_sha256"), "allocation record SHA-256")
        or record.get("job_id") != expected_job
        or record.get("hostname") != expected_node
    ):
        raise ReportError("allocation record identity differs from its pair commit")
    scheduler = mapping(record.get("scheduler_sharing"), "scheduler sharing")
    return {
        "path": relative.as_posix(),
        "sha256": file_sha,
        "record_sha256": self_hash,
        "job_id": expected_job,
        "hostname": expected_node,
        "host_class_sha256": hex64(
            record.get("host_class_sha256"), "allocation host-class SHA-256"
        ),
        "scheduler_exclusive": boolean(
            scheduler.get("exclusive"), "scheduler exclusive flag"
        ),
        "scheduler_sharing_policy": string(
            scheduler.get("sharing_policy"), "scheduler sharing policy"
        ),
    }


def project_run(
    record: Mapping[str, Any],
    *,
    paper_id: str,
    pair: Mapping[str, Any],
    condition: str,
    final_descriptor: Mapping[str, Any],
    final_path: Path,
    final_campaign_path: str,
    commit: Mapping[str, Any],
    shard_descriptor: Mapping[str, Any],
    allocation: Mapping[str, Any],
) -> dict[str, Any]:
    pair_id = string(pair.get("pair_id"), "canonical pair ID")
    run_id = f"{pair_id}-{condition}"
    condition_order = sequence(pair.get("condition_order"), "condition order")
    if condition_order not in (["N", "L"], ["L", "N"]):
        raise ReportError(f"{pair_id} has an invalid condition order")
    if (
        record.get("run_id") != run_id
        or record.get("pair_id") != pair_id
        or record.get("paper_id") != paper_id
        or record.get("task_id") != pair.get("task_id")
        or record.get("repetition_id") != pair.get("repetition_id")
        or record.get("condition") != condition
        or record.get("tier") != string(pair.get("task_id"), "pair task ID").rsplit("-", 1)[-1]
    ):
        raise ReportError(f"final record identity is stale: {run_id}")
    if record.get("order_index") != condition_order.index(condition) + 1:
        raise ReportError(f"final record order index is stale: {run_id}")
    expected_pair_order = f"{condition_order[0]}-first"
    if record.get("pair_order") != expected_pair_order:
        raise ReportError(f"final record pair order is stale: {run_id}")
    if record.get("scored") is not True:
        raise ReportError(f"final record is not scored: {run_id}")
    passed = boolean(record.get("pass"), f"{run_id} pass")
    failure_code = optional_string(record.get("failure_code"), f"{run_id} failure code")
    failure_note_raw = record.get("failure_note")
    if not isinstance(failure_note_raw, str):
        raise ReportError(f"{run_id} failure note is not a string")
    if passed and failure_code is not None:
        raise ReportError(f"passing record has a failure code: {run_id}")
    if not passed and failure_code is None:
        raise ReportError(f"failing record lacks a failure code: {run_id}")
    usage = mapping(record.get("token_usage"), f"{run_id} token usage")
    agent = mapping(record.get("agent"), f"{run_id} agent")
    record_allocation = mapping(
        record.get("allocation_hardware"), f"{run_id} allocation descriptor"
    )
    committed_allocation = mapping(
        commit.get("allocation_hardware"), f"{pair_id} committed allocation"
    )
    if dict(record_allocation) != dict(committed_allocation):
        raise ReportError(f"{run_id} does not use the committed pair allocation")
    final_file_sha = shard.file_sha256(final_path)
    if final_file_sha != hex64(
        final_descriptor.get("sha256"), f"{run_id} final file SHA-256"
    ):
        raise ReportError(f"final record file SHA-256 is stale: {run_id}")
    try:
        matrix_hash = shard.verify_self_hash(
            record, "matrix_record_sha256", f"{run_id} matrix record"
        )
    except shard.CampaignError as error:
        raise ReportError(str(error)) from error
    if matrix_hash != hex64(
        final_descriptor.get("matrix_record_sha256"),
        f"{run_id} descriptor matrix SHA-256",
    ):
        raise ReportError(f"final record matrix SHA-256 is stale: {run_id}")
    protocol = mapping(record.get("protocol"), f"{run_id} protocol")
    if boolean(protocol.get("complete"), f"{run_id} protocol complete") is not True:
        raise ReportError(f"final record has an incomplete protocol: {run_id}")
    index_descriptor = mapping(
        shard_descriptor.get("shard_index"), f"{pair_id} shard index"
    )
    library_use, library_declarations, library_use_status = library_use_projection(
        record, condition, passed, run_id
    )
    return {
        "run_id": run_id,
        "pair_id": pair_id,
        "paper_id": paper_id,
        "task_id": string(pair.get("task_id"), "pair task ID"),
        "tier": string(record.get("tier"), f"{run_id} tier"),
        "repetition_id": string(
            pair.get("repetition_id"), "pair repetition ID"
        ),
        "condition": condition,
        "condition_order": "".join(condition_order),
        "order_index": integer(record.get("order_index"), f"{run_id} order index"),
        "scored": True,
        "pass": passed,
        "failure_code": failure_code,
        "failure_note": failure_note_raw,
        "actual_stop_seconds": number(
            record.get("actual_stop_seconds"), f"{run_id} actual stop seconds"
        ),
        "scored_elapsed_seconds": number(
            record.get("scored_elapsed_seconds"), f"{run_id} scored seconds"
        ),
        "first_valid_seconds": optional_number(
            record.get("first_valid_seconds"), f"{run_id} first-valid seconds"
        ),
        "model_tokens": integer(usage.get("model_tokens"), f"{run_id} model tokens"),
        "input_tokens": integer(usage.get("input_tokens"), f"{run_id} input tokens"),
        "cached_input_tokens": integer(
            usage.get("cached_input_tokens"), f"{run_id} cached-input tokens"
        ),
        "output_tokens": integer(
            usage.get("output_tokens"), f"{run_id} output tokens"
        ),
        "thread_count": integer(usage.get("thread_count"), f"{run_id} thread count", minimum=1),
        "response_count": integer(
            usage.get("response_count"), f"{run_id} response count", minimum=1
        ),
        "appserver_response_count": integer(
            usage.get("appserver_response_count"),
            f"{run_id} app-server response count",
            minimum=1,
        ),
        "library_use": library_use,
        "library_use_status": library_use_status,
        "library_declaration_count": len(library_declarations),
        "library_declarations": library_declarations,
        "library_declarations_csv": ";".join(library_declarations),
        "protocol_complete": True,
        "agent_id": string(agent.get("id"), f"{run_id} agent ID"),
        "agent_version": string(agent.get("version"), f"{run_id} agent version"),
        "model": string(agent.get("model"), f"{run_id} model"),
        "reasoning_effort": string(
            agent.get("reasoning_effort"), f"{run_id} reasoning effort"
        ),
        "started_at_utc": string(record.get("started_at_utc"), f"{run_id} start"),
        "finished_at_utc": string(record.get("finished_at_utc"), f"{run_id} finish"),
        "allocation_job_id": string(allocation.get("job_id"), "allocation job ID"),
        "allocation_hostname": string(allocation.get("hostname"), "allocation hostname"),
        "allocation_host_class_sha256": hex64(
            allocation.get("host_class_sha256"), "allocation host-class SHA-256"
        ),
        "allocation_file_sha256": hex64(
            allocation.get("sha256"), "allocation file SHA-256"
        ),
        "allocation_record_sha256": hex64(
            allocation.get("record_sha256"), "allocation record SHA-256"
        ),
        "freeze_check_sha256": hex64(
            commit.get("freeze_check_sha256"), f"{pair_id} freeze-check SHA-256"
        ),
        "submission_sha256": optional_hex64(
            record.get("final_submission_sha256", record.get("submission_sha256")),
            f"{run_id} submission SHA-256",
        ),
        "final_record_path": final_campaign_path,
        "final_file_sha256": final_file_sha,
        "matrix_record_sha256": matrix_hash,
        "pair_commit_sha256": hex64(
            mapping(commit.get("pair_commit"), f"{pair_id} pair commit").get(
                "pair_commit_sha256"
            ),
            f"{pair_id} pair-commit SHA-256",
        ),
        "shard_index_file_sha256": hex64(
            index_descriptor.get("sha256"), f"{pair_id} shard-index file SHA-256"
        ),
        "shard_campaign_index_sha256": hex64(
            index_descriptor.get("campaign_index_sha256"),
            f"{pair_id} campaign-index SHA-256",
        ),
    }


def pair_row(
    pair: Mapping[str, Any],
    runs: Mapping[str, Mapping[str, Any]],
    commit: Mapping[str, Any],
    allocation: Mapping[str, Any],
    failed_attempts: Sequence[Mapping[str, Any]],
    allocation_campaign_path: str,
) -> dict[str, Any]:
    pair_id = string(pair.get("pair_id"), "pair ID")
    n = runs["N"]
    l = runs["L"]
    exact_fields = (
        "allocation_job_id",
        "allocation_hostname",
        "allocation_host_class_sha256",
        "allocation_file_sha256",
        "allocation_record_sha256",
        "freeze_check_sha256",
    )
    if any(n[field] != l[field] for field in exact_fields):
        raise ReportError(f"{pair_id} N/L hardware identities differ")
    if n["allocation_job_id"] != commit.get("slurm_job_id"):
        raise ReportError(f"{pair_id} allocation job differs from committed attempt")
    commit_descriptor = mapping(commit.get("pair_commit"), f"{pair_id} pair commit")
    return {
        "pair_id": pair_id,
        "task_id": string(pair.get("task_id"), f"{pair_id} task ID"),
        "tier": string(pair.get("task_id"), f"{pair_id} task ID").rsplit("-", 1)[-1],
        "repetition_id": string(
            pair.get("repetition_id"), f"{pair_id} repetition ID"
        ),
        "condition_order": "".join(sequence(pair.get("condition_order"), f"{pair_id} order")),
        "n_pass": n["pass"],
        "l_pass": l["pass"],
        "l_minus_n_pass": int(l["pass"]) - int(n["pass"]),
        "n_scored_seconds": n["scored_elapsed_seconds"],
        "l_scored_seconds": l["scored_elapsed_seconds"],
        "l_minus_n_scored_seconds": decimal_delta(
            l["scored_elapsed_seconds"], n["scored_elapsed_seconds"]
        ),
        "n_actual_stop_seconds": n["actual_stop_seconds"],
        "l_actual_stop_seconds": l["actual_stop_seconds"],
        "l_minus_n_actual_stop_seconds": decimal_delta(
            l["actual_stop_seconds"], n["actual_stop_seconds"]
        ),
        "n_model_tokens": n["model_tokens"],
        "l_model_tokens": l["model_tokens"],
        "l_minus_n_model_tokens": l["model_tokens"] - n["model_tokens"],
        "n_failure_code": n["failure_code"],
        "l_failure_code": l["failure_code"],
        "allocation_job_id": n["allocation_job_id"],
        "allocation_hostname": n["allocation_hostname"],
        "allocation_hardware_path": allocation_campaign_path,
        "allocation_file_sha256": n["allocation_file_sha256"],
        "allocation_record_sha256": n["allocation_record_sha256"],
        "host_class_sha256": n["allocation_host_class_sha256"],
        "scheduler_exclusive": allocation["scheduler_exclusive"],
        "scheduler_sharing_policy": allocation["scheduler_sharing_policy"],
        "same_authenticated_allocation": True,
        "prior_failed_attempt_count": len(failed_attempts),
        "prior_failed_attempt_ids": ";".join(
            string(item.get("attempt_id"), f"{pair_id} failed attempt ID")
            for item in failed_attempts
        ),
        "committed_attempt_id": string(
            commit.get("attempt_id"), f"{pair_id} committed attempt ID"
        ),
        "committed_slurm_job_id": string(
            commit.get("slurm_job_id"), f"{pair_id} committed Slurm job ID"
        ),
        "committed_at_utc": string(
            commit.get("committed_at_utc"), f"{pair_id} commit time"
        ),
        "pair_commit_path": string(
            commit_descriptor.get("path"), f"{pair_id} pair-commit path"
        ),
        "pair_commit_file_sha256": hex64(
            commit_descriptor.get("sha256"), f"{pair_id} pair-commit file SHA-256"
        ),
        "pair_commit_sha256": hex64(
            commit_descriptor.get("pair_commit_sha256"),
            f"{pair_id} pair-commit SHA-256",
        ),
    }


def condition_summary(rows: Sequence[Mapping[str, Any]], condition: str) -> dict[str, Any]:
    selected = [row for row in rows if row["condition"] == condition]
    times = [row["scored_elapsed_seconds"] for row in selected]
    actual = [row["actual_stop_seconds"] for row in selected]
    tokens = [row["model_tokens"] for row in selected]
    failure_counts: dict[str, int] = {}
    for row in selected:
        code = row["failure_code"]
        if code is not None:
            failure_counts[str(code)] = failure_counts.get(str(code), 0) + 1
    return {
        "condition": condition,
        "run_count": len(selected),
        "pass_count": sum(row["pass"] is True for row in selected),
        "failure_count": sum(row["pass"] is False for row in selected),
        "pass_rate": sum(row["pass"] is True for row in selected) / len(selected),
        "total_scored_seconds": decimal_sum(times),
        "median_scored_seconds": decimal_median(times),
        "total_actual_stop_seconds": decimal_sum(actual),
        "median_actual_stop_seconds": decimal_median(actual),
        "total_model_tokens": sum(tokens),
        "median_model_tokens": decimal_median(tokens),
        "failure_code_counts": failure_counts,
    }


def report_analysis(
    runs: Sequence[Mapping[str, Any]], pairs: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    pass_deltas = [pair["l_minus_n_pass"] for pair in pairs]
    time_deltas = [pair["l_minus_n_scored_seconds"] for pair in pairs]
    actual_deltas = [pair["l_minus_n_actual_stop_seconds"] for pair in pairs]
    token_deltas = [pair["l_minus_n_model_tokens"] for pair in pairs]
    hosts = sorted({str(pair["allocation_hostname"]) for pair in pairs})
    jobs = sorted({str(pair["allocation_job_id"]) for pair in pairs})
    host_classes = sorted({str(pair["host_class_sha256"]) for pair in pairs})
    passing_l = [run for run in runs if run["condition"] == "L" and run["pass"]]
    return {
        "run_count": len(runs),
        "pair_count": len(pairs),
        "all_final_records_scored": all(run["scored"] is True for run in runs),
        "all_pairs_share_exact_n_l_allocation": all(
            pair["same_authenticated_allocation"] is True for pair in pairs
        ),
        "by_condition": {
            condition: condition_summary(runs, condition) for condition in ("N", "L")
        },
        "paired_l_minus_n": {
            "pass_delta_sum": sum(pass_deltas),
            "pass_rate_delta": sum(pass_deltas) / len(pass_deltas),
            "total_scored_seconds_delta": decimal_sum(time_deltas),
            "median_scored_seconds_delta": decimal_median(time_deltas),
            "total_actual_stop_seconds_delta": decimal_sum(actual_deltas),
            "median_actual_stop_seconds_delta": decimal_median(actual_deltas),
            "total_model_tokens_delta": sum(token_deltas),
            "median_model_tokens_delta": decimal_median(token_deltas),
        },
        "hardware": {
            "distinct_allocation_job_count": len(jobs),
            "allocation_job_ids": jobs,
            "distinct_hostname_count": len(hosts),
            "hostnames": hosts,
            "distinct_host_class_count": len(host_classes),
            "host_class_sha256s": host_classes,
            "scheduler_exclusive_pair_count": sum(
                pair["scheduler_exclusive"] is True for pair in pairs
            ),
        },
        "library_use": {
            "passing_l_run_count": len(passing_l),
            "passing_l_run_with_completed_audit_count": sum(
                isinstance(run["library_use"], bool) for run in passing_l
            ),
            "passing_l_run_using_library_count": sum(
                run["library_use"] is True for run in passing_l
            ),
            "failed_l_run_without_completed_audit_count": sum(
                run["condition"] == "L"
                and run["pass"] is False
                and run["library_use"] is None
                for run in runs
            ),
        },
        "estimand": {
            "principal_elapsed_estimand": "within_pair_l_minus_n_scored_seconds",
            "paired_delta_definition": "L minus N",
            "pooled_absolute_elapsed_summaries": "descriptive_only",
        },
    }


def csv_bytes(rows: Sequence[Mapping[str, Any]], fields: Sequence[str]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=list(fields), extrasaction="ignore")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def markdown_escape(value: Any) -> str:
    if value is None:
        return "—"
    return str(value).replace("|", "\\|").replace("\n", " ")


def fmt_seconds(value: int | float) -> str:
    return f"{float(value):.6f}"


def render_markdown(summary: Mapping[str, Any], pairs: Sequence[Mapping[str, Any]]) -> bytes:
    paper_id = summary["paper_id"]
    analysis = mapping(summary.get("analysis"), "report analysis")
    by_condition = mapping(analysis.get("by_condition"), "condition analysis")
    delta = mapping(analysis.get("paired_l_minus_n"), "paired delta analysis")
    library = mapping(analysis.get("library_use"), "library-use analysis")
    provenance = mapping(summary.get("provenance"), "report provenance")
    failure_history = sequence(summary.get("failed_attempts"), "failed attempts")
    lines = [
        f"# HighamBench {paper_id} authenticated measurements",
        "",
        f"Status: **authenticated actual measurements** ({analysis['run_count']} scored runs, {analysis['pair_count']} N/L pairs).",
        "",
        "The principal comparison is the within-pair difference **L minus N**. Each N/L pair used one exact authenticated Slurm allocation descriptor and job ID. Hardware, host class, allocation, and concurrent scheduler load may differ across pairs; pooled absolute times are descriptive only.",
        "",
        "A scored failure may carry the benchmark's fixed failure charge, so `scored seconds` and `actual stop seconds` are reported separately.",
        "",
        "Library use is tri-state: `true`/`false` is an audited classification, while `null` means that a failed L run had no completed library audit and is reported as `not_audited_failed_l_run` (never as `false`). "
        f"This matrix contains {library['failed_l_run_without_completed_audit_count']} such failed L run(s).",
        "",
        "## Condition totals",
        "",
        "| Condition | Passes / runs | Pass rate | Total scored s | Median scored s | Total model tokens | Median model tokens |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for condition in ("N", "L"):
        row = mapping(by_condition[condition], f"{condition} summary")
        lines.append(
            "| "
            + " | ".join(
                (
                    condition,
                    f"{row['pass_count']} / {row['run_count']}",
                    f"{100 * float(row['pass_rate']):.1f}%",
                    fmt_seconds(row["total_scored_seconds"]),
                    fmt_seconds(row["median_scored_seconds"]),
                    f"{int(row['total_model_tokens']):,}",
                    f"{float(row['median_model_tokens']):,.1f}",
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "Paired L−N summary: "
            f"pass-rate change {100 * float(delta['pass_rate_delta']):+.1f} percentage points; "
            f"median scored-time change {float(delta['median_scored_seconds_delta']):+.6f} s; "
            f"median token change {float(delta['median_model_tokens_delta']):+,.1f}.",
            "",
            "## Exact paired measurements",
            "",
            "| Pair | Order | N pass | L pass | N scored s | L scored s | L−N s | N tokens | L tokens | L−N tokens | Node / job | Prior failed attempts |",
            "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|",
        ]
    )
    for pair in pairs:
        lines.append(
            "| "
            + " | ".join(
                (
                    markdown_escape(pair["pair_id"]),
                    markdown_escape(pair["condition_order"]),
                    markdown_escape(pair["n_pass"]),
                    markdown_escape(pair["l_pass"]),
                    fmt_seconds(pair["n_scored_seconds"]),
                    fmt_seconds(pair["l_scored_seconds"]),
                    f"{float(pair['l_minus_n_scored_seconds']):+.6f}",
                    f"{int(pair['n_model_tokens']):,}",
                    f"{int(pair['l_model_tokens']):,}",
                    f"{int(pair['l_minus_n_model_tokens']):+,}",
                    f"{markdown_escape(pair['allocation_hostname'])} / {markdown_escape(pair['allocation_job_id'])}",
                    str(pair["prior_failed_attempt_count"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Failure and provenance notes",
            "",
            f"Retained failed whole-pair attempts before the selected first successes: **{len(failure_history)}**. These attempts are provenance, not additional scored observations.",
            "",
        ]
    )
    if failure_history:
        lines.extend(
            [
                "| Pair | Attempt | Outcome | Matrix exit | Final records | Incidents | Node / job |",
                "|---|---|---|---:|---:|---:|---|",
            ]
        )
        for failure in failure_history:
            lines.append(
                "| "
                + " | ".join(
                    (
                        markdown_escape(failure["pair_id"]),
                        markdown_escape(failure["attempt_id"]),
                        markdown_escape(failure["outcome"]),
                        markdown_escape(failure["matrix_exit_code"]),
                        markdown_escape(failure["final_record_count"]),
                        markdown_escape(failure["incident_count"]),
                        f"{markdown_escape(failure['allocation_node'])} / {markdown_escape(failure['slurm_job_id'])}",
                    )
                )
                + " |"
            )
        lines.append("")
    aggregate_source = mapping(provenance.get("aggregate_index"), "aggregate source")
    lines.extend(
        [
            f"Source aggregate self-hash: `{aggregate_source['aggregate_index_sha256']}`.",
            "",
            f"Source aggregate file SHA-256: `{aggregate_source['sha256']}`.",
            "",
            f"Environment bundle SHA-256: `{provenance['environment_bundle_sha256']}`.",
            "",
            "Machine-readable exact values and hashes are in `runs.json`, `pairs.json`, `runs.csv`, and `pairs.csv`; `report_manifest.json` authenticates every generated artifact.",
            "",
        ]
    )
    return "\n".join(lines).encode("utf-8")


def reporter_sha256() -> str:
    return shard.file_sha256(Path(__file__).resolve())


def collect_report(
    shards_root: Path,
    benchmark_root: Path,
    paper_id: str,
    aggregate_index: Mapping[str, Any],
    *,
    created_at_utc: str,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Project an already authenticated aggregate without writing any source path."""

    created_at_utc = validate_utc(created_at_utc, "report creation time")
    pair_ids = aggregate.canonical_pair_ids(paper_id)
    if (
        aggregate_index.get("paper_id") != paper_id
        or aggregate_index.get("pair_ids") != pair_ids
    ):
        raise ReportError("aggregate paper/pair identity is stale")
    pair_specs = sequence(aggregate_index.get("canonical_pairs"), "canonical pairs")
    if [mapping(item, "canonical pair").get("pair_id") for item in pair_specs] != pair_ids:
        raise ReportError("aggregate canonical pair order is stale")
    descriptors = sequence(aggregate_index.get("pair_shards"), "pair shards")
    if [mapping(item, "pair shard").get("pair_id") for item in descriptors] != pair_ids:
        raise ReportError("aggregate pair-shard order is stale")
    project = benchmark_root.resolve().parents[1]
    aggregate_path = shards_root / aggregate.INDEX_NAME
    if aggregate_path.is_symlink() or not aggregate_path.is_file():
        raise ReportError("aggregate index file is missing or unsafe")
    aggregate_file_sha = shard.file_sha256(aggregate_path)
    aggregate_self_hash = hex64(
        aggregate_index.get(aggregate.HASH_FIELD), "aggregate self-hash"
    )
    runs: list[dict[str, Any]] = []
    pairs: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []

    for pair_spec_raw, shard_descriptor_raw in zip(pair_specs, descriptors):
        pair_spec = mapping(pair_spec_raw, "canonical pair")
        shard_descriptor = mapping(shard_descriptor_raw, "pair shard descriptor")
        pair_id = string(pair_spec.get("pair_id"), "pair ID")
        if shard_descriptor.get("pair_id") != pair_id:
            raise ReportError("pair shard descriptor order is stale")
        pair_root = shards_root / pair_id
        index_descriptor = mapping(
            shard_descriptor.get("shard_index"), f"{pair_id} shard index"
        )
        shard_index_path = pair_root / "campaign_index.json"
        if shard.file_sha256(shard_index_path) != hex64(
            index_descriptor.get("sha256"), f"{pair_id} shard index file SHA-256"
        ):
            raise ReportError(f"{pair_id} shard index changed after aggregate authentication")
        commit = mapping(
            shard_descriptor.get("committed_attempt"), f"{pair_id} committed attempt"
        )
        if commit.get("pair_id") != pair_id:
            raise ReportError(f"{pair_id} committed attempt identity is stale")
        attempt_relative = shard.safe_relative_path(
            commit.get("path"), f"{pair_id} committed attempt path"
        )
        attempt_root = pair_root / attempt_relative
        allocation_descriptor = mapping(
            commit.get("allocation_hardware"), f"{pair_id} allocation descriptor"
        )
        allocation = load_allocation(
            attempt_root,
            allocation_descriptor,
            string(commit.get("allocation_node"), f"{pair_id} allocation node"),
            string(commit.get("slurm_job_id"), f"{pair_id} Slurm job ID"),
        )
        if dict(allocation_descriptor) != {
            key: allocation[key] for key in ("path", "sha256", "record_sha256", "job_id")
        }:
            raise ReportError(f"{pair_id} committed allocation descriptor is stale")
        failed_raw = sequence(
            shard_descriptor.get("failed_pair_attempts"), f"{pair_id} failed attempts"
        )
        if shard_descriptor.get("failed_pair_attempt_count") != len(failed_raw):
            raise ReportError(f"{pair_id} failed-attempt count is stale")
        normalized_failures: list[dict[str, Any]] = []
        for attempt_number, failure_raw in enumerate(failed_raw, start=1):
            failure = mapping(failure_raw, f"{pair_id} failed attempt")
            if failure.get("pair_id") != pair_id:
                raise ReportError(f"{pair_id} failure history aliases another pair")
            incidents = sequence(
                failure.get("incidents"), f"{pair_id} failed-attempt incidents"
            )
            normalized = {
                "pair_id": pair_id,
                "attempt_number": attempt_number,
                "attempt_id": string(
                    failure.get("attempt_id"), f"{pair_id} failed attempt ID"
                ),
                "outcome": string(
                    failure.get("outcome"), f"{pair_id} failed attempt outcome"
                ),
                "matrix_exit_code": failure.get("matrix_exit_code"),
                "final_record_count": integer(
                    failure.get("final_record_count"),
                    f"{pair_id} failed final-record count",
                ),
                "incident_count": len(incidents),
                "incidents": json.loads(json.dumps(incidents)),
                "allocation_node": string(
                    failure.get("allocation_node"), f"{pair_id} failed allocation node"
                ),
                "slurm_job_id": string(
                    failure.get("slurm_job_id"), f"{pair_id} failed Slurm job ID"
                ),
                "started_at_utc": string(
                    failure.get("started_at_utc"), f"{pair_id} failed start time"
                ),
                "archived_at_utc": string(
                    failure.get("archived_at_utc"), f"{pair_id} failed archive time"
                ),
                "path": string(failure.get("path"), f"{pair_id} failed path"),
                "file_count": integer(
                    failure.get("file_count"), f"{pair_id} failed file count"
                ),
                "total_bytes": integer(
                    failure.get("total_bytes"), f"{pair_id} failed byte count"
                ),
                "tree_sha256": hex64(
                    failure.get("tree_sha256"), f"{pair_id} failed tree SHA-256"
                ),
                "last_chunk_status": json.loads(
                    json.dumps(failure.get("last_chunk_status"))
                ),
            }
            normalized_failures.append(normalized)
            failures.append(normalized)

        final_descriptors = mapping(
            commit.get("final_records"), f"{pair_id} final descriptors"
        )
        if set(final_descriptors) != {"N", "L"}:
            raise ReportError(f"{pair_id} lacks exact N/L final descriptors")
        per_condition: dict[str, dict[str, Any]] = {}
        for condition in sequence(pair_spec.get("condition_order"), f"{pair_id} order"):
            if condition not in {"N", "L"}:
                raise ReportError(f"{pair_id} has an invalid condition")
            final_descriptor = mapping(
                final_descriptors[condition], f"{pair_id}-{condition} final descriptor"
            )
            final_relative = shard.safe_relative_path(
                final_descriptor.get("path"), f"{pair_id}-{condition} final path"
            )
            final_path = attempt_root / final_relative
            final_campaign_path = (
                Path(pair_id) / attempt_relative / final_relative
            ).as_posix()
            record = read_json(final_path, f"{pair_id}-{condition} final record")
            row = project_run(
                record,
                paper_id=paper_id,
                pair=pair_spec,
                condition=condition,
                final_descriptor=final_descriptor,
                final_path=final_path,
                final_campaign_path=final_campaign_path,
                commit=commit,
                shard_descriptor=shard_descriptor,
                allocation=allocation,
            )
            per_condition[condition] = row
            runs.append(row)
        allocation_campaign_path = (
            Path(pair_id) / attempt_relative / allocation["path"]
        ).as_posix()
        pairs.append(
            pair_row(
                pair_spec,
                per_condition,
                commit,
                allocation,
                normalized_failures,
                allocation_campaign_path,
            )
        )

    if len(runs) != 18 or len(pairs) != 9 or len({run["run_id"] for run in runs}) != 18:
        raise ReportError("report input is not exactly nine N/L pairs and 18 unique finals")
    analysis = report_analysis(runs, pairs)
    provenance = {
        "authentication": {
            "existing_aggregate_index_verified_and_rebuilt": True,
            "all_nine_shard_indexes_reauthenticated": True,
            "all_eighteen_final_records_reauthenticated": True,
            "all_pair_commits_reauthenticated": True,
            "failed_attempt_history_reauthenticated": True,
        },
        "aggregate_index": {
            "path": source_relative(project, aggregate_path, "aggregate index"),
            "sha256": aggregate_file_sha,
            "aggregate_index_sha256": aggregate_self_hash,
            "created_at_utc": string(
                aggregate_index.get("created_at_utc"), "aggregate creation time"
            ),
        },
        "benchmark_id": string(aggregate_index.get("benchmark_id"), "benchmark ID"),
        "environment_id": string(
            mapping(aggregate_index.get("environment"), "environment descriptor").get(
                "environment_id"
            ),
            "environment ID",
        ),
        "environment_bundle_sha256": hex64(
            mapping(aggregate_index.get("environment"), "environment descriptor").get(
                "environment_bundle_sha256"
            ),
            "environment bundle SHA-256",
        ),
        "manifest": json.loads(json.dumps(aggregate_index.get("manifest"))),
        "run_order": json.loads(json.dumps(aggregate_index.get("run_order"))),
        "hardware_matching_policy": json.loads(
            json.dumps(aggregate_index.get("hardware_matching_policy"))
        ),
        "hardware_matching_policy_sha256": hex64(
            aggregate_index.get("hardware_matching_policy_sha256"),
            "hardware-policy SHA-256",
        ),
        "common_initial_task_ledger_sha256": hex64(
            aggregate_index.get("common_initial_task_ledger_sha256"),
            "common task-ledger SHA-256",
        ),
        "manager_sha256": hex64(
            aggregate_index.get("manager_sha256"), "manager SHA-256"
        ),
        "launcher_sha256": hex64(
            aggregate_index.get("launcher_sha256"), "launcher SHA-256"
        ),
        "aggregator_sha256": shard.file_sha256(Path(aggregate.__file__).resolve()),
        "reporter_sha256": reporter_sha256(),
    }
    caveats = {
        "within_pair_hardware": (
            "Each N/L pair shares one exact authenticated allocation descriptor, "
            "Slurm job, node, host class, and frozen transport provenance."
        ),
        "cross_pair_hardware": (
            "Hardware, host class, allocation identity, and concurrent scheduler load "
            "may differ across pairs; no same-hardware requirement is claimed across pairs."
        ),
        "elapsed_interpretation": (
            "The principal elapsed estimand is within-pair L minus N scored seconds; "
            "pooled absolute elapsed summaries are descriptive only."
        ),
        "failure_charge": (
            "A scored failure may use the frozen failure-time charge, so scored elapsed "
            "seconds and actual stop seconds are reported separately."
        ),
        "library_use": (
            "library_use is tri-state: true/false is audited; null is valid only for "
            "a failed L run with no completed library audit and no declarations, and "
            "is reported as not_audited_failed_l_run rather than coerced to false."
        ),
        "failed_attempts": (
            "Retained failed whole-pair attempts are provenance and are not extra scored runs."
        ),
    }
    runs_dataset = bind_hash(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RUNS_KIND,
            "paper_id": paper_id,
            "source_aggregate_index_sha256": aggregate_self_hash,
            "run_count": len(runs),
            "runs": runs,
        },
        DATASET_HASH_FIELD,
    )
    pairs_dataset = bind_hash(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": PAIRS_KIND,
            "paper_id": paper_id,
            "source_aggregate_index_sha256": aggregate_self_hash,
            "pair_count": len(pairs),
            "pairs": pairs,
        },
        DATASET_HASH_FIELD,
    )
    failures_dataset = bind_hash(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": FAILURES_KIND,
            "paper_id": paper_id,
            "source_aggregate_index_sha256": aggregate_self_hash,
            "failed_attempt_count": len(failures),
            "failed_attempts": failures,
        },
        DATASET_HASH_FIELD,
    )
    summary = bind_hash(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": SUMMARY_KIND,
            "status": "authenticated_actual_measurements",
            "public_release": False,
            "paper_id": paper_id,
            "created_at_utc": created_at_utc,
            "analysis": analysis,
            "failed_attempt_count": len(failures),
            "failed_attempts": failures,
            "datasets": {
                "runs": {
                    "path": "runs.json",
                    "dataset_sha256": runs_dataset[DATASET_HASH_FIELD],
                },
                "pairs": {
                    "path": "pairs.json",
                    "dataset_sha256": pairs_dataset[DATASET_HASH_FIELD],
                },
                "failed_attempts": {
                    "path": "failed_attempts.json",
                    "dataset_sha256": failures_dataset[DATASET_HASH_FIELD],
                },
            },
            "caveats": caveats,
            "provenance": provenance,
        },
        SUMMARY_HASH_FIELD,
    )
    artifacts = {
        "summary.json": pretty_json_bytes(summary),
        "runs.json": pretty_json_bytes(runs_dataset),
        "runs.csv": csv_bytes(runs, RUN_CSV_FIELDS),
        "pairs.json": pretty_json_bytes(pairs_dataset),
        "pairs.csv": csv_bytes(pairs, PAIR_CSV_FIELDS),
        "failed_attempts.json": pretty_json_bytes(failures_dataset),
        "report.md": render_markdown(summary, pairs),
    }
    if tuple(artifacts) != ARTIFACT_NAMES:
        raise ReportError("internal report artifact order is stale")
    manifest = bind_hash(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": MANIFEST_KIND,
            "paper_id": paper_id,
            "created_at_utc": created_at_utc,
            "source_aggregate_index_sha256": aggregate_self_hash,
            "source_aggregate_file_sha256": aggregate_file_sha,
            "report_summary_sha256": summary[SUMMARY_HASH_FIELD],
            "files": [
                {
                    "path": name,
                    "size_bytes": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                }
                for name, payload in artifacts.items()
            ],
        },
        MANIFEST_HASH_FIELD,
    )
    return manifest, artifacts


def authenticate_and_collect(
    shards_root: Path,
    benchmark_root: Path,
    paper_id: str,
    *,
    created_at_utc: str,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    try:
        source = aggregate.verify_existing(shards_root, benchmark_root, paper_id)
    except (aggregate.AggregateError, shard.CampaignError) as error:
        raise ReportError(f"source aggregate authentication failed: {error}") from error
    return collect_report(
        shards_root,
        benchmark_root,
        paper_id,
        source,
        created_at_utc=created_at_utc,
    )


def fsync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def write_sealed(path: Path, payload: bytes) -> None:
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as stream:
        stream.write(payload)
        stream.flush()
        os.fchmod(stream.fileno(), 0o444)
        os.fsync(stream.fileno())


def publish(
    output_dir: Path, manifest: Mapping[str, Any], artifacts: Mapping[str, bytes]
) -> None:
    temporary = output_dir.with_name(f".{output_dir.name}.tmp-{os.getpid()}")
    if output_dir.exists() or output_dir.is_symlink():
        raise ReportError(f"report output already exists: {output_dir}")
    if temporary.exists() or temporary.is_symlink():
        raise ReportError(f"report temporary already exists: {temporary}")
    temporary.mkdir(mode=0o700)
    try:
        for name in ARTIFACT_NAMES:
            write_sealed(temporary / name, artifacts[name])
        write_sealed(temporary / MANIFEST_NAME, pretty_json_bytes(manifest))
        fsync_directory(temporary)
        temporary.chmod(0o555)
        os.rename(temporary, output_dir)
        fsync_directory(output_dir.parent)
    except BaseException:
        if temporary.exists() and not temporary.is_symlink():
            temporary.chmod(0o700)
            for path in temporary.iterdir():
                if path.is_file() and not path.is_symlink():
                    path.chmod(0o600)
            shutil.rmtree(temporary)
        raise


def verify_existing_report(
    output_dir: Path,
    shards_root: Path,
    benchmark_root: Path,
    paper_id: str,
) -> dict[str, Any]:
    if output_dir.is_symlink() or not output_dir.is_dir():
        raise ReportError("report output is missing, linked, or not a directory")
    if output_dir.stat().st_mode & 0o777 != 0o555:
        raise ReportError("report output directory is not sealed mode 0555")
    expected_names = set(ARTIFACT_NAMES) | {MANIFEST_NAME}
    entries = {path.name: path for path in output_dir.iterdir()}
    if set(entries) != expected_names:
        raise ReportError("report output has unexpected or missing artifacts")
    for path in entries.values():
        if (
            path.is_symlink()
            or not path.is_file()
            or path.stat().st_mode & 0o777 != 0o444
        ):
            raise ReportError(f"report artifact is unsafe or not sealed 0444: {path}")
    manifest = dict(read_json(output_dir / MANIFEST_NAME, "report manifest"))
    verify_bound_hash(manifest, MANIFEST_HASH_FIELD, "report manifest")
    if (
        manifest.get("schema_version") != SCHEMA_VERSION
        or manifest.get("kind") != MANIFEST_KIND
        or manifest.get("paper_id") != paper_id
    ):
        raise ReportError("report manifest identity is invalid")
    file_descriptors = sequence(manifest.get("files"), "report manifest files")
    if [mapping(item, "report file descriptor").get("path") for item in file_descriptors] != list(
        ARTIFACT_NAMES
    ):
        raise ReportError("report manifest artifact order is stale")
    for descriptor_raw in file_descriptors:
        descriptor = mapping(descriptor_raw, "report file descriptor")
        name = string(descriptor.get("path"), "report artifact path")
        payload = entries[name].read_bytes()
        if (
            descriptor.get("size_bytes") != len(payload)
            or descriptor.get("sha256") != hashlib.sha256(payload).hexdigest()
        ):
            raise ReportError(f"report artifact digest is stale: {name}")
    created = validate_utc(manifest.get("created_at_utc"), "report creation time")
    expected_manifest, expected_artifacts = authenticate_and_collect(
        shards_root,
        benchmark_root,
        paper_id,
        created_at_utc=created,
    )
    if dict(manifest) != expected_manifest:
        raise ReportError("report manifest differs from the authenticated source aggregate")
    for name, expected in expected_artifacts.items():
        if entries[name].read_bytes() != expected:
            raise ReportError(f"report artifact is not the exact reproducible projection: {name}")
    return manifest


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--paper-id", choices=shard.SUPPORTED_PAPER_IDS, required=True)
    result.add_argument("--shards-root", type=Path, required=True)
    result.add_argument("--benchmark-root", type=Path, required=True)
    result.add_argument("--output-dir", type=Path, required=True)
    result.add_argument("command", choices=("create", "verify"))
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    shards_root = args.shards_root.absolute()
    benchmark_root = args.benchmark_root.resolve()
    try:
        output_dir, _scratch = validate_output_path(
            args.output_dir, benchmark_root, shards_root
        )
        if args.command == "create":
            if output_dir.exists() or output_dir.is_symlink():
                manifest = verify_existing_report(
                    output_dir, shards_root, benchmark_root, args.paper_id
                )
            else:
                manifest, artifacts = authenticate_and_collect(
                    shards_root,
                    benchmark_root,
                    args.paper_id,
                    created_at_utc=utc_now(),
                )
                publish(output_dir, manifest, artifacts)
        else:
            manifest = verify_existing_report(
                output_dir, shards_root, benchmark_root, args.paper_id
            )
        print(
            json.dumps(
                {
                    "status": "authenticated",
                    "paper_id": args.paper_id,
                    "output_dir": str(output_dir),
                    "report_manifest_sha256": manifest[MANIFEST_HASH_FIELD],
                    "source_aggregate_index_sha256": manifest[
                        "source_aggregate_index_sha256"
                    ],
                    "artifacts": list(ARTIFACT_NAMES) + [MANIFEST_NAME],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    except (
        ReportError,
        aggregate.AggregateError,
        shard.CampaignError,
        shard.run_matrix.BenchmarkToolError,
        OSError,
        ValueError,
    ) as error:
        print(f"pair-shard report error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
