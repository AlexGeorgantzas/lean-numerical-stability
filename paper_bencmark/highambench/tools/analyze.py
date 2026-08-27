#!/usr/bin/env python3
"""Aggregate HighamBench JSONL runs into JSON, CSV, and LaTeX tables."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import json
from pathlib import Path
import random
import statistics
from typing import Any, Iterable, Mapping, Sequence

try:
    from .common import BenchmarkToolError, FAILURE_CODES, SCHEMA_VERSION, read_json, write_json
    from .result_set import check_result_set, require_complete_result_set
    from .task_tags import validate_t4_task_metadata
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, FAILURE_CODES, SCHEMA_VERSION, read_json, write_json  # type: ignore
    from result_set import check_result_set, require_complete_result_set  # type: ignore
    from task_tags import validate_t4_task_metadata  # type: ignore


SELECTED_TIERS = ("T1", "T2", "T3")
WHOLE_PAPER_SCOPE = "whole-paper"
TIER_ORDER = {"overall": 0, "T1": 1, "T2": 2, "T3": 3, WHOLE_PAPER_SCOPE: 4}


def load_runs(paths: Sequence[Path]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    runs: list[dict[str, Any]] = []
    malformed: list[dict[str, Any]] = []
    for path in paths:
        try:
            stream = path.open(encoding="utf-8")
        except OSError as error:
            raise BenchmarkToolError(f"cannot open raw results {path}: {error}") from error
        with stream:
            for line_number, line in enumerate(stream, start=1):
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except json.JSONDecodeError as error:
                    malformed.append(
                        {"path": str(path), "line": line_number, "error": str(error)}
                    )
                    continue
                if not isinstance(value, dict) or value.get("kind") != "highambench-run":
                    malformed.append(
                        {
                            "path": str(path),
                            "line": line_number,
                            "error": "not a highambench-run object",
                        }
                    )
                    continue
                runs.append(value)
    return runs, malformed


def agent_key(run: Mapping[str, Any]) -> tuple[str, str, str]:
    agent = run.get("agent")
    if not isinstance(agent, dict):
        return ("unknown", "unknown", "unknown")
    return (
        str(agent.get("id", "unknown")),
        str(agent.get("version", "unknown")),
        str(agent.get("model", "unknown")),
    )


def numeric(value: Any) -> float | None:
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return float(value)
    return None


def median_or_none(values: Iterable[float | int | None]) -> float | None:
    present = [float(value) for value in values if value is not None]
    return float(statistics.median(present)) if present else None


def token_count(run: Mapping[str, Any]) -> int | None:
    usage = run.get("token_usage")
    if not isinstance(usage, dict):
        return None
    value = usage.get("model_tokens")
    return value if isinstance(value, int) and not isinstance(value, bool) else None


def summarize_condition(
    key: tuple[str, str, str], scope: str, condition: str, runs: Sequence[dict[str, Any]]
) -> dict[str, Any]:
    failures = Counter(
        str(run.get("failure_code"))
        for run in runs
        if not bool(run.get("pass")) and run.get("failure_code") is not None
    )
    passes = sum(bool(run.get("pass")) for run in runs)
    return {
        "agent_id": key[0],
        "agent_version": key[1],
        "model": key[2],
        "scope": scope,
        "condition": condition,
        "scored_runs": len(runs),
        "passes": passes,
        "pass_rate": passes / len(runs) if runs else None,
        "median_scored_seconds": median_or_none(
            numeric(run.get("scored_elapsed_seconds")) for run in runs
        ),
        "median_model_tokens": median_or_none(token_count(run) for run in runs),
        "runs_with_token_measurement": sum(token_count(run) is not None for run in runs),
        "passed_library_use": (
            sum(bool(run.get("pass")) and run.get("library_use") is True for run in runs)
            if condition == "L"
            else 0
        ),
        "failure_counts": {code: failures.get(code, 0) for code in FAILURE_CODES},
    }


def flatten_run(run: Mapping[str, Any]) -> dict[str, Any]:
    """Return the stable, reportable part of one raw run or system incident."""

    key = agent_key(run)
    protocol = run.get("protocol")
    return {
        "agent_id": key[0],
        "agent_version": key[1],
        "model": key[2],
        "run_id": run.get("run_id"),
        "pair_id": run.get("pair_id"),
        "paper_id": run.get("paper_id"),
        "task_id": run.get("task_id"),
        "tier": run.get("tier"),
        "repetition_id": run.get("repetition_id"),
        "backend_seed": run.get("backend_seed", run.get("seed")),
        "condition": run.get("condition"),
        "pair_order": run.get("pair_order"),
        "order_index": run.get("order_index"),
        "scored": run.get("scored") is True,
        "pass": run.get("pass") is True,
        "actual_stop_seconds": numeric(run.get("actual_stop_seconds")),
        "scored_elapsed_seconds": numeric(run.get("scored_elapsed_seconds")),
        "model_tokens": token_count(run),
        "library_use": run.get("library_use"),
        "library_declarations": run.get("library_declarations", []),
        "failure_code": run.get("failure_code"),
        "failure_note": run.get("failure_note", ""),
        "protocol_complete": (
            protocol.get("complete") is True if isinstance(protocol, Mapping) else False
        ),
        "submission_sha256": run.get("submission_sha256"),
        "started_at_utc": run.get("started_at_utc"),
        "finished_at_utc": run.get("finished_at_utc"),
    }


def _observational_condition_row(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        **{
            key: value
            for key, value in row.items()
            if key
            not in {
                "scored_runs",
                "passes",
                "pass_rate",
                "median_scored_seconds",
                "median_model_tokens",
                "passed_library_use",
            }
        },
        "result_status": "observational_not_reference_score",
        "official_scored_runs": 0,
        "observational_runs": row.get("scored_runs"),
        "observed_passes": row.get("passes"),
        "observed_pass_rate": row.get("pass_rate"),
        "median_observed_seconds": row.get("median_scored_seconds"),
        "median_observed_model_tokens": row.get("median_model_tokens"),
        "observed_passed_library_use": row.get("passed_library_use"),
    }


def _observational_comparison_row(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        **{
            key: value
            for key, value in row.items()
            if key
            not in {
                "pass_rate_change",
                "median_paired_time_change",
                "median_paired_token_change",
            }
        },
        "result_status": "observational_not_reference_score",
        "observed_pass_rate_change": row.get("pass_rate_change"),
        "median_observed_paired_time_change": row.get("median_paired_time_change"),
        "median_observed_paired_token_change": row.get("median_paired_token_change"),
    }


def pair_runs(runs: Sequence[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[str]]:
    buckets: dict[tuple[tuple[str, str, str], str], dict[str, dict[str, Any]]] = {}
    problems: list[str] = []
    for run in runs:
        pair_id = run.get("pair_id")
        condition = run.get("condition")
        if not isinstance(pair_id, str) or condition not in ("N", "L"):
            problems.append(f"run {run.get('run_id')} lacks pair_id or condition")
            continue
        key = (agent_key(run), pair_id)
        bucket = buckets.setdefault(key, {})
        if condition in bucket:
            problems.append(f"duplicate scored {condition} run for pair {pair_id}")
            continue
        bucket[condition] = run
    pairs: list[dict[str, Any]] = []
    for (key, pair_id), bucket in sorted(buckets.items()):
        if set(bucket) != {"N", "L"}:
            problems.append(f"incomplete scored pair {pair_id}: {sorted(bucket)}")
            continue
        n_run = bucket["N"]
        l_run = bucket["L"]
        n_seed = n_run.get("backend_seed", n_run.get("seed"))
        l_seed = l_run.get("backend_seed", l_run.get("seed"))
        if (
            n_run.get("task_id") != l_run.get("task_id")
            or n_run.get("repetition_id") != l_run.get("repetition_id")
            or n_seed != l_seed
        ):
            problems.append(f"mismatched task/repetition/backend seed in pair {pair_id}")
            continue
        if n_run.get("tier") != l_run.get("tier") or n_run.get("paper_id") != l_run.get(
            "paper_id"
        ):
            problems.append(f"mismatched tier/paper in pair {pair_id}")
            continue
        n_time = numeric(n_run.get("scored_elapsed_seconds"))
        l_time = numeric(l_run.get("scored_elapsed_seconds"))
        n_tokens = token_count(n_run)
        l_tokens = token_count(l_run)
        pairs.append(
            {
                "agent": key,
                "pair_id": pair_id,
                "paper_id": str(n_run.get("paper_id")),
                "task_id": str(n_run.get("task_id")),
                "tier": str(n_run.get("tier")),
                "repetition_id": n_run.get("repetition_id"),
                "backend_seed": n_seed,
                "pass_change": int(bool(l_run.get("pass"))) - int(bool(n_run.get("pass"))),
                "time_change": l_time - n_time if l_time is not None and n_time is not None else None,
                "token_change": (
                    l_tokens - n_tokens if l_tokens is not None and n_tokens is not None else None
                ),
            }
        )
    return pairs, problems


def quantile(values: Sequence[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = (len(ordered) - 1) * probability
    lower = int(position)
    upper = min(lower + 1, len(ordered) - 1)
    fraction = position - lower
    return ordered[lower] * (1 - fraction) + ordered[upper] * fraction


def _metric(pairs: Sequence[dict[str, Any]], field: str) -> float | None:
    values = [numeric(pair.get(field)) for pair in pairs]
    present = [value for value in values if value is not None]
    if not present:
        return None
    if field == "pass_change":
        return sum(present) / len(present)
    return float(statistics.median(present))


def bootstrap_whole_papers(
    pairs: Sequence[dict[str, Any]],
    *,
    resamples: int,
    seed: int,
) -> dict[str, Any]:
    by_paper: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for pair in pairs:
        by_paper[pair["paper_id"]].append(pair)
    papers = sorted(by_paper)
    result: dict[str, Any] = {
        "method": "percentile bootstrap resampling whole papers",
        "confidence": 0.95,
        "resamples": resamples,
        "seed": seed,
        "paper_count": len(papers),
        "informative": len(papers) >= 2,
        "note": (
            "one-paper resampling is degenerate and does not estimate corpus uncertainty"
            if len(papers) == 1
            else ""
        ),
    }
    if not papers or resamples <= 0:
        result["ranges"] = {}
        return result
    generator = random.Random(seed)
    samples: dict[str, list[float]] = {
        "pass_rate_change": [],
        "median_paired_time_change": [],
        "median_paired_token_change": [],
    }
    field_map = {
        "pass_rate_change": "pass_change",
        "median_paired_time_change": "time_change",
        "median_paired_token_change": "token_change",
    }
    for _ in range(resamples):
        sampled: list[dict[str, Any]] = []
        for paper in generator.choices(papers, k=len(papers)):
            sampled.extend(by_paper[paper])
        for output_name, field in field_map.items():
            value = _metric(sampled, field)
            if value is not None:
                samples[output_name].append(value)
    result["ranges"] = {
        name: {
            "low": quantile(values, 0.025),
            "high": quantile(values, 0.975),
        }
        for name, values in samples.items()
    }
    return result


def summarize_pairs(
    key: tuple[str, str, str],
    scope: str,
    pairs: Sequence[dict[str, Any]],
    *,
    resamples: int,
    bootstrap_seed: int,
) -> dict[str, Any]:
    return {
        "agent_id": key[0],
        "agent_version": key[1],
        "model": key[2],
        "scope": scope,
        "condition": "L-N",
        "pairs": len(pairs),
        "pass_rate_change": _metric(pairs, "pass_change"),
        # This is the median of within-pair L-N changes, not a difference of
        # two independently computed medians.
        "median_paired_time_change": _metric(pairs, "time_change"),
        "median_paired_token_change": _metric(pairs, "token_change"),
        "pairs_with_token_measurement": sum(pair["token_change"] is not None for pair in pairs),
        "bootstrap": bootstrap_whole_papers(
            pairs, resamples=resamples, seed=bootstrap_seed
        ),
    }


def _stratified_runs(
    runs: Sequence[dict[str, Any]],
) -> list[tuple[str, list[dict[str, Any]]]]:
    """Keep T4 whole-paper results outside the T1--T3 overall score."""

    selected = [run for run in runs if run.get("tier") in SELECTED_TIERS]
    rows: list[tuple[str, list[dict[str, Any]]]] = [("overall", selected)]
    rows.extend(
        (tier, [run for run in runs if run.get("tier") == tier])
        for tier in SELECTED_TIERS
    )
    rows.append(
        (WHOLE_PAPER_SCOPE, [run for run in runs if run.get("tier") == "T4"])
    )
    return rows


def _t4_coverage_rows(
    manifest: Mapping[str, Any] | None,
    repository_root: Path | None,
) -> list[dict[str, Any]]:
    """Authenticate and summarize final claim-scoped T4 coverage."""

    if manifest is None:
        return []
    papers = manifest.get("papers")
    if not isinstance(papers, list):
        raise BenchmarkToolError("manifest papers must be a JSON array")
    t4_targets: list[tuple[str, str]] = []
    for paper in papers:
        if not isinstance(paper, Mapping):
            raise BenchmarkToolError("manifest paper entries must be JSON objects")
        paper_id = paper.get("paper_id")
        targets = paper.get("targets")
        if not isinstance(paper_id, str) or not isinstance(targets, list):
            raise BenchmarkToolError("manifest paper identity/targets are invalid")
        for target in targets:
            if (
                isinstance(target, Mapping)
                and target.get("availability") == "available"
                and target.get("tier") == "T4"
            ):
                task_id = target.get("task_id")
                if task_id != f"{paper_id}-T4":
                    raise BenchmarkToolError("manifest T4 task identity disagrees")
                t4_targets.append((paper_id, str(task_id)))
    if not t4_targets:
        return []
    if repository_root is None:
        raise BenchmarkToolError(
            "T4 coverage reporting requires repository_root for task authentication"
        )
    project_root = repository_root.resolve()
    benchmark_root = project_root / "paper_bencmark" / "highambench"
    if not benchmark_root.is_dir() and (project_root / "tasks").is_dir():
        benchmark_root = project_root
    rows: list[dict[str, Any]] = []
    for paper_id, task_id in t4_targets:
        task_path = benchmark_root / "tasks" / paper_id / "T4" / "task.json"
        task = read_json(task_path)
        if not isinstance(task, Mapping):
            raise BenchmarkToolError(f"{task_path} must contain a JSON object")
        summary = validate_t4_task_metadata(task, label=task_id)
        if summary.get("task_id") != task_id:
            raise BenchmarkToolError(f"{task_id} metadata identity disagrees")
        review_units = int(summary["review_unit_count"])
        accepted_reviews = int(summary["review_count"])
        rows.append(
            {
                "paper_id": paper_id,
                "task_id": task_id,
                "tier": "T4",
                "stratum": WHOLE_PAPER_SCOPE,
                "source_inventory_count": int(summary["source_inventory_count"]),
                "included_source_count": int(summary["included_source_count"]),
                "excluded_source_count": int(summary["excluded_source_count"]),
                "reviewed_included_source_count": int(summary["included_source_count"]),
                "declaration_count": int(summary["declaration_count"]),
                "reviewed_declaration_count": int(summary["declaration_count"]),
                "review_unit_count": review_units,
                "accepted_review_count": accepted_reviews,
                "accepted_review_unit_coverage_rate": (
                    accepted_reviews / review_units if review_units else None
                ),
                "controlled_sorry_count": int(summary["controlled_sorry_count"]),
                "measurement_ready": summary.get("measurement_ready") is True,
            }
        )
    return rows


def analyze(
    all_runs: Sequence[dict[str, Any]],
    *,
    include_unscored: bool,
    bootstrap_resamples: int,
    bootstrap_seed: int,
    run_order: Mapping[str, Any] | None = None,
    config: Mapping[str, Any] | None = None,
    manifest: Mapping[str, Any] | None = None,
    repository_root: Path | None = None,
    require_complete: bool = False,
    observational_pilot: bool = False,
) -> dict[str, Any]:
    plan_values = (run_order, config, manifest)
    if require_complete and any(value is None for value in plan_values):
        raise BenchmarkToolError(
            "complete analysis requires run_order, config, and manifest"
        )
    if any(value is not None for value in plan_values) and any(
        value is None for value in plan_values
    ):
        raise BenchmarkToolError(
            "run_order, config, and manifest must be supplied together"
        )
    result_set_check: dict[str, Any] | None = None
    if all(value is not None for value in plan_values):
        assert run_order is not None and config is not None and manifest is not None
        result_set_check = check_result_set(
            all_runs,
            run_order=run_order,
            config=config,
            manifest=manifest,
            repository_root=repository_root,
            allow_observational_unscored=observational_pilot,
        )
        if require_complete:
            require_complete_result_set(result_set_check)
            if include_unscored:
                raise BenchmarkToolError(
                    "final complete analysis cannot include unscored system incidents in scores"
                )
            if not observational_pilot and not result_set_check.get("reference_compliant"):
                raise BenchmarkToolError(
                    "official analysis requires a reference-compliant result set"
                )
    official_scores_valid = bool(
        result_set_check is None or result_set_check.get("reference_compliant")
    )
    runs = (
        list(all_runs)
        if include_unscored
        else [run for run in all_runs if run.get("scored")]
    )
    if result_set_check is not None and not official_scores_valid:
        # Never publish a partial subset as official scores.  The complete set is
        # summarized separately below as explicitly observational data.
        runs = []
    excluded = len(all_runs) - len(runs)
    condition_rows: list[dict[str, Any]] = []
    task_rows: list[dict[str, Any]] = []
    keys = sorted({agent_key(run) for run in runs})
    for key in keys:
        agent_runs = [run for run in runs if agent_key(run) == key]
        for scope, scoped in _stratified_runs(agent_runs):
            if not scoped:
                continue
            for condition in ("N", "L"):
                selected = [run for run in scoped if run.get("condition") == condition]
                if selected:
                    condition_rows.append(summarize_condition(key, scope, condition, selected))
        task_ids = sorted({str(run.get("task_id")) for run in agent_runs})
        for task_id in task_ids:
            selected_task = [run for run in agent_runs if run.get("task_id") == task_id]
            if not selected_task:
                continue
            paper_id = str(selected_task[0].get("paper_id"))
            tier = str(selected_task[0].get("tier"))
            for condition in ("N", "L"):
                selected = [run for run in selected_task if run.get("condition") == condition]
                if selected:
                    task_rows.append(
                        {
                            **summarize_condition(key, task_id, condition, selected),
                            "paper_id": paper_id,
                            "task_id": task_id,
                            "tier": tier,
                        }
                    )

    pairs, pair_problems = pair_runs(runs)
    comparison_rows: list[dict[str, Any]] = []
    task_comparison_rows: list[dict[str, Any]] = []
    for key in keys:
        agent_pairs = [pair for pair in pairs if pair["agent"] == key]
        for scope, scoped_pairs in _stratified_runs(agent_pairs):
            if scoped_pairs:
                comparison_rows.append(
                    summarize_pairs(
                        key,
                        scope,
                        scoped_pairs,
                        resamples=bootstrap_resamples,
                        bootstrap_seed=bootstrap_seed,
                    )
                )
        task_ids = sorted({pair["task_id"] for pair in agent_pairs})
        for task_id in task_ids:
            scoped_pairs = [pair for pair in agent_pairs if pair["task_id"] == task_id]
            if scoped_pairs:
                row = summarize_pairs(
                    key,
                    task_id,
                    scoped_pairs,
                    resamples=bootstrap_resamples,
                    bootstrap_seed=bootstrap_seed,
                )
                row.update(
                    {
                        "paper_id": scoped_pairs[0]["paper_id"],
                        "task_id": task_id,
                        "tier": scoped_pairs[0]["tier"],
                    }
                )
                task_comparison_rows.append(row)
    observational_results: dict[str, Any] | None = None
    if (
        observational_pilot
        and result_set_check is not None
        and not result_set_check.get("reference_compliant")
        and result_set_check.get("ok")
    ):
        selected = set(result_set_check.get("selected_final_run_ids", []))
        observational_runs = [run for run in all_runs if run.get("run_id") in selected]
        pilot = analyze(
            observational_runs,
            include_unscored=True,
            bootstrap_resamples=bootstrap_resamples,
            bootstrap_seed=bootstrap_seed,
        )
        observational_results = {
            "label": "observational pilot; not a reference-compliant HighamBench score",
            "official_scores_valid": False,
            "nonreference_reasons": result_set_check.get("nonreference_reasons", []),
            "run_count": len(observational_runs),
            "condition_summaries": [
                _observational_condition_row(row)
                for row in pilot["condition_summaries"]
            ],
            "per_task_summaries": [
                _observational_condition_row(row)
                for row in pilot["per_task_summaries"]
            ],
            "paired_comparisons": [
                _observational_comparison_row(row)
                for row in pilot["paired_comparisons"]
            ],
            "per_task_paired_comparisons": [
                _observational_comparison_row(row)
                for row in pilot["per_task_paired_comparisons"]
            ],
        }
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-analysis",
        "included_unscored": include_unscored,
        "input_run_count": len(all_runs),
        "analyzed_run_count": len(runs),
        "excluded_run_count": excluded,
        "official_scores_valid": official_scores_valid,
        "result_set_check": result_set_check,
        "observational_pilot_results": observational_results,
        "per_run_results": [flatten_run(run) for run in all_runs],
        "condition_summaries": condition_rows,
        "per_task_summaries": task_rows,
        "paired_comparisons": comparison_rows,
        "per_task_paired_comparisons": task_comparison_rows,
        "whole_paper_t4_coverage": _t4_coverage_rows(manifest, repository_root),
        "pair_problems": pair_problems,
        "paired_change_definition": "median of per-pair (L minus N) changes",
        "combined_score": None,
        "note": "Pass rate, time, tokens, and library use are intentionally separate.",
    }


def _flat_condition_row(row: Mapping[str, Any]) -> dict[str, Any]:
    flat = {key: value for key, value in row.items() if key != "failure_counts"}
    failures = row.get("failure_counts", {})
    for code in FAILURE_CODES:
        flat[code] = failures.get(code, 0) if isinstance(failures, dict) else 0
    return flat


def _flat_comparison_row(row: Mapping[str, Any]) -> dict[str, Any]:
    ranges = row["bootstrap"].get("ranges", {})
    return {
        **{key: value for key, value in row.items() if key != "bootstrap"},
        "pass_rate_change_95_low": ranges.get("pass_rate_change", {}).get("low"),
        "pass_rate_change_95_high": ranges.get("pass_rate_change", {}).get("high"),
        "time_change_95_low": ranges.get("median_paired_time_change", {}).get("low"),
        "time_change_95_high": ranges.get("median_paired_time_change", {}).get("high"),
        "token_change_95_low": ranges.get("median_paired_token_change", {}).get("low"),
        "token_change_95_high": ranges.get("median_paired_token_change", {}).get("high"),
        "bootstrap_informative": row["bootstrap"].get("informative"),
        "bootstrap_note": row["bootstrap"].get("note", ""),
    }


def _flat_observational_comparison_row(row: Mapping[str, Any]) -> dict[str, Any]:
    flat = _flat_comparison_row(row)
    renames = {
        "pass_rate_change_95_low": "observed_pass_rate_change_95_low",
        "pass_rate_change_95_high": "observed_pass_rate_change_95_high",
        "time_change_95_low": "observed_time_change_95_low",
        "time_change_95_high": "observed_time_change_95_high",
        "token_change_95_low": "observed_token_change_95_low",
        "token_change_95_high": "observed_token_change_95_high",
    }
    for old, new in renames.items():
        flat[new] = flat.pop(old)
    return flat


def write_csv_tables(output_dir: Path, analysis: Mapping[str, Any]) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    condition_rows = [_flat_condition_row(row) for row in analysis["condition_summaries"]]
    condition_fields = [
        "agent_id",
        "agent_version",
        "model",
        "scope",
        "condition",
        "scored_runs",
        "passes",
        "pass_rate",
        "median_scored_seconds",
        "median_model_tokens",
        "runs_with_token_measurement",
        "passed_library_use",
        *FAILURE_CODES,
    ]
    with (output_dir / "condition_summary.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=condition_fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(condition_rows)

    comparison_fields = [
        "agent_id",
        "agent_version",
        "model",
        "scope",
        "condition",
        "pairs",
        "pass_rate_change",
        "median_paired_time_change",
        "median_paired_token_change",
        "pairs_with_token_measurement",
        "pass_rate_change_95_low",
        "pass_rate_change_95_high",
        "time_change_95_low",
        "time_change_95_high",
        "token_change_95_low",
        "token_change_95_high",
        "bootstrap_informative",
        "bootstrap_note",
    ]
    comparison_rows = [_flat_comparison_row(row) for row in analysis["paired_comparisons"]]
    with (output_dir / "paired_summary.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=comparison_fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(comparison_rows)

    task_fields = [
        "agent_id",
        "agent_version",
        "model",
        "paper_id",
        "task_id",
        "tier",
        "condition",
        "scored_runs",
        "passes",
        "pass_rate",
        "median_scored_seconds",
        "median_model_tokens",
        "runs_with_token_measurement",
        "passed_library_use",
        *FAILURE_CODES,
    ]
    with (output_dir / "task_summary.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=task_fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(_flat_condition_row(row) for row in analysis["per_task_summaries"])

    task_comparison_fields = [
        "agent_id",
        "agent_version",
        "model",
        "paper_id",
        "task_id",
        "tier",
        "condition",
        "pairs",
        "pass_rate_change",
        "median_paired_time_change",
        "median_paired_token_change",
        "pairs_with_token_measurement",
        "pass_rate_change_95_low",
        "pass_rate_change_95_high",
        "time_change_95_low",
        "time_change_95_high",
        "token_change_95_low",
        "token_change_95_high",
        "bootstrap_informative",
        "bootstrap_note",
    ]
    with (output_dir / "task_paired_summary.csv").open(
        "w", encoding="utf-8", newline=""
    ) as stream:
        writer = csv.DictWriter(
            stream, fieldnames=task_comparison_fields, extrasaction="ignore"
        )
        writer.writeheader()
        writer.writerows(
            _flat_comparison_row(row) for row in analysis["per_task_paired_comparisons"]
        )

    run_fields = [
        "agent_id",
        "agent_version",
        "model",
        "run_id",
        "pair_id",
        "paper_id",
        "task_id",
        "tier",
        "repetition_id",
        "backend_seed",
        "condition",
        "pair_order",
        "order_index",
        "scored",
        "pass",
        "actual_stop_seconds",
        "scored_elapsed_seconds",
        "model_tokens",
        "library_use",
        "failure_code",
        "failure_note",
        "protocol_complete",
        "submission_sha256",
        "started_at_utc",
        "finished_at_utc",
    ]
    with (output_dir / "run_results.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=run_fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(analysis["per_run_results"])

    t4_coverage_fields = [
        "paper_id",
        "task_id",
        "tier",
        "stratum",
        "source_inventory_count",
        "included_source_count",
        "excluded_source_count",
        "reviewed_included_source_count",
        "declaration_count",
        "reviewed_declaration_count",
        "review_unit_count",
        "accepted_review_count",
        "accepted_review_unit_coverage_rate",
        "controlled_sorry_count",
        "measurement_ready",
    ]
    with (output_dir / "t4_whole_paper_coverage.csv").open(
        "w", encoding="utf-8", newline=""
    ) as stream:
        writer = csv.DictWriter(
            stream, fieldnames=t4_coverage_fields, extrasaction="ignore"
        )
        writer.writeheader()
        writer.writerows(analysis.get("whole_paper_t4_coverage", []))

    observational = analysis.get("observational_pilot_results")
    if isinstance(observational, Mapping):
        observational_condition_fields = [
            "result_status",
            "agent_id",
            "agent_version",
            "model",
            "scope",
            "condition",
            "official_scored_runs",
            "observational_runs",
            "observed_passes",
            "observed_pass_rate",
            "median_observed_seconds",
            "median_observed_model_tokens",
            "runs_with_token_measurement",
            "observed_passed_library_use",
            *FAILURE_CODES,
        ]
        with (output_dir / "observational_condition_summary.csv").open(
            "w", encoding="utf-8", newline=""
        ) as stream:
            writer = csv.DictWriter(
                stream, fieldnames=observational_condition_fields, extrasaction="ignore"
            )
            writer.writeheader()
            writer.writerows(
                _flat_condition_row(row)
                for row in observational["condition_summaries"]
            )
        observational_task_fields = [
            "result_status",
            "agent_id",
            "agent_version",
            "model",
            "paper_id",
            "task_id",
            "tier",
            "condition",
            "official_scored_runs",
            "observational_runs",
            "observed_passes",
            "observed_pass_rate",
            "median_observed_seconds",
            "median_observed_model_tokens",
            "runs_with_token_measurement",
            "observed_passed_library_use",
            *FAILURE_CODES,
        ]
        with (output_dir / "observational_task_summary.csv").open(
            "w", encoding="utf-8", newline=""
        ) as stream:
            writer = csv.DictWriter(
                stream, fieldnames=observational_task_fields, extrasaction="ignore"
            )
            writer.writeheader()
            writer.writerows(
                _flat_condition_row(row) for row in observational["per_task_summaries"]
            )
        observational_pair_fields = [
            "result_status",
            "agent_id",
            "agent_version",
            "model",
            "scope",
            "condition",
            "pairs",
            "observed_pass_rate_change",
            "median_observed_paired_time_change",
            "median_observed_paired_token_change",
            "pairs_with_token_measurement",
            "observed_pass_rate_change_95_low",
            "observed_pass_rate_change_95_high",
            "observed_time_change_95_low",
            "observed_time_change_95_high",
            "observed_token_change_95_low",
            "observed_token_change_95_high",
            "bootstrap_informative",
            "bootstrap_note",
        ]
        with (output_dir / "observational_paired_summary.csv").open(
            "w", encoding="utf-8", newline=""
        ) as stream:
            writer = csv.DictWriter(
                stream, fieldnames=observational_pair_fields, extrasaction="ignore"
            )
            writer.writeheader()
            writer.writerows(
                _flat_observational_comparison_row(row)
                for row in observational["paired_comparisons"]
            )
        observational_task_pair_fields = [
            "result_status",
            "agent_id",
            "agent_version",
            "model",
            "paper_id",
            "task_id",
            "tier",
            "condition",
            "pairs",
            "observed_pass_rate_change",
            "median_observed_paired_time_change",
            "median_observed_paired_token_change",
            "pairs_with_token_measurement",
            "observed_pass_rate_change_95_low",
            "observed_pass_rate_change_95_high",
            "observed_time_change_95_low",
            "observed_time_change_95_high",
            "observed_token_change_95_low",
            "observed_token_change_95_high",
            "bootstrap_informative",
            "bootstrap_note",
        ]
        with (output_dir / "observational_task_paired_summary.csv").open(
            "w", encoding="utf-8", newline=""
        ) as stream:
            writer = csv.DictWriter(
                stream,
                fieldnames=observational_task_pair_fields,
                extrasaction="ignore",
            )
            writer.writeheader()
            writer.writerows(
                _flat_observational_comparison_row(row)
                for row in observational["per_task_paired_comparisons"]
            )


def latex_escape(value: Any) -> str:
    if value is None:
        return "--"
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def fmt(value: Any, digits: int = 3) -> str:
    if value is None:
        return "--"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def _range_text(row: Mapping[str, Any], metric: str, digits: int = 3) -> str:
    bootstrap = row.get("bootstrap")
    ranges = bootstrap.get("ranges", {}) if isinstance(bootstrap, Mapping) else {}
    interval = ranges.get(metric, {}) if isinstance(ranges, Mapping) else {}
    if not isinstance(interval, Mapping):
        return "--"
    low = interval.get("low")
    high = interval.get("high")
    if low is None or high is None:
        return "--"
    return f"[{fmt(low, digits)}, {fmt(high, digits)}]"


def render_latex(analysis: Mapping[str, Any]) -> str:
    check = analysis.get("result_set_check")
    check_ok = check.get("ok") if isinstance(check, Mapping) else None
    incident_count = (
        check.get("system_error_incident_count", 0) if isinstance(check, Mapping) else 0
    )
    official_valid = analysis.get("official_scores_valid") is True
    observational = analysis.get("observational_pilot_results")
    lines = [
        r"\documentclass[10pt]{article}",
        r"\usepackage[margin=0.55in]{geometry}",
        r"\usepackage{booktabs}",
        r"\usepackage{longtable}",
        r"\begin{document}",
        r"\section*{HighamBench result tables}",
        (
            "Official reference-score runs analyzed: "
            + str(analysis["analyzed_run_count"])
            + "; raw records excluded from official scores: "
            + str(analysis["excluded_run_count"])
            + ". Official scores are "
            + ("valid." if official_valid else "invalid and intentionally left empty.")
        ),
        (
            "Result-set completeness: "
            + (
                "passed"
                if check_ok is True
                else "failed"
                if check_ok is False
                else "not checked"
            )
            + "; recorded system-error incidents: "
            + str(incident_count)
            + "."
        ),
    ]
    if isinstance(observational, Mapping):
        lines.extend(
            [
                r"\section*{Observational pilot results---not official scores}",
                r"\textbf{These tables describe a complete pilot matrix, but the runs failed one or more reference-protocol controls. They must not be reported as HighamBench scores.}",
                "Reasons: "
                + latex_escape("; ".join(observational.get("nonreference_reasons", []))),
                r"\subsection*{Observed condition results}",
                r"\small",
                r"\begin{longtable}{llllrrrrrr}",
                r"\toprule",
                r"Agent & Scope & Cond. & Official & Runs & Pass & Rate & Med. s & Med. tokens & L-use \\",
                r"\midrule",
                r"\endfirsthead",
                r"\toprule",
                r"Agent & Scope & Cond. & Official & Runs & Pass & Rate & Med. s & Med. tokens & L-use \\",
                r"\midrule",
                r"\endhead",
            ]
        )
        for row in observational["condition_summaries"]:
            lines.append(
                " & ".join(
                    latex_escape(value)
                    for value in (
                        row["agent_id"],
                        row["scope"],
                        row["condition"],
                        row["official_scored_runs"],
                        row["observational_runs"],
                        row["observed_passes"],
                        fmt(row["observed_pass_rate"]),
                        fmt(row["median_observed_seconds"]),
                        fmt(row["median_observed_model_tokens"], 1),
                        row["observed_passed_library_use"],
                    )
                )
                + r" \\"
            )
        lines.extend(
            [
                r"\bottomrule",
                r"\end{longtable}",
                r"\subsection*{Observed per-task results}",
                r"\small",
                r"\begin{longtable}{llllrrrrr}",
                r"\toprule",
                r"Task & Tier & Cond. & Official & Runs & Pass & Rate & Med. s & Med. tokens \\",
                r"\midrule",
                r"\endfirsthead",
                r"\toprule",
                r"Task & Tier & Cond. & Official & Runs & Pass & Rate & Med. s & Med. tokens \\",
                r"\midrule",
                r"\endhead",
            ]
        )
        for row in observational["per_task_summaries"]:
            lines.append(
                " & ".join(
                    latex_escape(value)
                    for value in (
                        row["task_id"],
                        row["tier"],
                        row["condition"],
                        row["official_scored_runs"],
                        row["observational_runs"],
                        row["observed_passes"],
                        fmt(row["observed_pass_rate"]),
                        fmt(row["median_observed_seconds"]),
                        fmt(row["median_observed_model_tokens"], 1),
                    )
                )
                + r" \\"
            )
        lines.extend(
            [
                r"\bottomrule",
                r"\end{longtable}",
                r"\subsection*{Observed paired changes (L minus N)}",
                r"\scriptsize",
                r"\begin{longtable}{llrrrrrrr}",
                r"\toprule",
                r"Scope & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% & Informative \\",
                r"\midrule",
                r"\endfirsthead",
                r"\toprule",
                r"Scope & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% & Informative \\",
                r"\midrule",
                r"\endhead",
            ]
        )
        for row in observational["paired_comparisons"]:
            lines.append(
                " & ".join(
                    latex_escape(value)
                    for value in (
                        row["scope"],
                        row["pairs"],
                        fmt(row["observed_pass_rate_change"]),
                        _range_text(row, "pass_rate_change"),
                        fmt(row["median_observed_paired_time_change"]),
                        _range_text(row, "median_paired_time_change"),
                        fmt(row["median_observed_paired_token_change"], 1),
                        _range_text(row, "median_paired_token_change", 1),
                        row["bootstrap"].get("informative"),
                    )
                )
                + r" \\"
            )
        observational_notes = sorted(
            {
                str(row.get("bootstrap", {}).get("note", ""))
                for row in observational["paired_comparisons"]
                if row.get("bootstrap", {}).get("note")
            }
        )
        lines.extend(
            [
                r"\bottomrule",
                r"\end{longtable}",
                (
                    "The ranges above are 95 percent ranges made by resampling whole papers. "
                    + (" ".join(observational_notes) if observational_notes else "")
                ),
                r"\subsection*{Observed per-task paired changes (L minus N)}",
                r"\scriptsize",
                r"\begin{longtable}{llrrrrrrr}",
                r"\toprule",
                r"Task & Tier & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% \\",
                r"\midrule",
                r"\endfirsthead",
                r"\toprule",
                r"Task & Tier & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% \\",
                r"\midrule",
                r"\endhead",
            ]
        )
        for row in observational["per_task_paired_comparisons"]:
            lines.append(
                " & ".join(
                    latex_escape(value)
                    for value in (
                        row["task_id"],
                        row["tier"],
                        row["pairs"],
                        fmt(row["observed_pass_rate_change"]),
                        _range_text(row, "pass_rate_change"),
                        fmt(row["median_observed_paired_time_change"]),
                        _range_text(row, "median_paired_time_change"),
                        fmt(row["median_observed_paired_token_change"], 1),
                        _range_text(row, "median_paired_token_change", 1),
                    )
                )
                + r" \\"
            )
        lines.extend([r"\bottomrule", r"\end{longtable}"])
    t4_coverage = analysis.get("whole_paper_t4_coverage")
    if isinstance(t4_coverage, list) and t4_coverage:
        lines.extend(
            [
                r"\section*{T4 whole-paper formalization coverage}",
                (
                    "T4 is reported as a separate whole-paper stratum, not as a "
                    "fourth difficulty tier and not inside the T1--T3 overall score."
                ),
                r"\small",
                r"\begin{longtable}{lrrrrrrrr}",
                r"\toprule",
                r"Task & Inventory & Included & Excluded & Decls. & Review units & Accepted & Holes & Ready \\",
                r"\midrule",
                r"\endfirsthead",
                r"\toprule",
                r"Task & Inventory & Included & Excluded & Decls. & Review units & Accepted & Holes & Ready \\",
                r"\midrule",
                r"\endhead",
            ]
        )
        for row in t4_coverage:
            lines.append(
                " & ".join(
                    latex_escape(value)
                    for value in (
                        row["task_id"],
                        row["source_inventory_count"],
                        row["included_source_count"],
                        row["excluded_source_count"],
                        row["declaration_count"],
                        row["review_unit_count"],
                        row["accepted_review_count"],
                        row["controlled_sorry_count"],
                        row["measurement_ready"],
                    )
                )
                + r" \\"
            )
        lines.extend([r"\bottomrule", r"\end{longtable}"])

    lines.extend(
        [
        r"\section*{Official reference scores}",
        r"\subsection*{Condition results}",
        r"\small",
        r"\begin{longtable}{llllrrrrrr}",
        r"\toprule",
        r"Agent & Model & Scope & Cond. & Scored & Pass & Rate & Med. s & Med. tokens & L-use \\",
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        r"Agent & Model & Scope & Cond. & Scored & Pass & Rate & Med. s & Med. tokens & L-use \\",
        r"\midrule",
        r"\endhead",
        ]
    )
    for row in analysis["condition_summaries"]:
        lines.append(
            " & ".join(
                latex_escape(value)
                for value in (
                    row["agent_id"],
                    row["model"],
                    row["scope"],
                    row["condition"],
                    row["scored_runs"],
                    row["passes"],
                    fmt(row["pass_rate"]),
                    fmt(row["median_scored_seconds"]),
                    fmt(row["median_model_tokens"], 1),
                    row["passed_library_use"],
                )
            )
            + r" \\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{longtable}",
            r"\subsection*{Failure-code counts}",
            r"\scriptsize",
            r"\begin{longtable}{lllrrrrrrr}",
            r"\toprule",
            r"Agent & Scope & Cond. & TIME & TOKEN & NONE & RULE & SYNTAX & PROOF & SYSTEM \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"Agent & Scope & Cond. & TIME & TOKEN & NONE & RULE & SYNTAX & PROOF & SYSTEM \\",
            r"\midrule",
            r"\endhead",
        ]
    )
    for row in analysis["condition_summaries"]:
        failures = row["failure_counts"]
        lines.append(
            " & ".join(
                latex_escape(value)
                for value in (
                    row["agent_id"],
                    row["scope"],
                    row["condition"],
                    *(failures[code] for code in FAILURE_CODES),
                )
            )
            + r" \\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{longtable}",
            r"\subsection*{Per-task condition results}",
            r"\small",
            r"\begin{longtable}{llllrrrrrr}",
            r"\toprule",
            r"Task & Tier & Cond. & Agent & Scored & Pass & Rate & Med. s & Med. tokens & L-use \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"Task & Tier & Cond. & Agent & Scored & Pass & Rate & Med. s & Med. tokens & L-use \\",
            r"\midrule",
            r"\endhead",
        ]
    )
    for row in analysis["per_task_summaries"]:
        lines.append(
            " & ".join(
                latex_escape(value)
                for value in (
                    row["task_id"],
                    row["tier"],
                    row["condition"],
                    row["agent_id"],
                    row["scored_runs"],
                    row["passes"],
                    fmt(row["pass_rate"]),
                    fmt(row["median_scored_seconds"]),
                    fmt(row["median_model_tokens"], 1),
                    row["passed_library_use"],
                )
            )
            + r" \\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{longtable}",
            r"\subsection*{Paired changes (L minus N)}",
            r"\scriptsize",
            r"\begin{longtable}{lllrrrrrr}",
            r"\toprule",
            r"Agent & Scope & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"Agent & Scope & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% \\",
            r"\midrule",
            r"\endhead",
        ]
    )
    for row in analysis["paired_comparisons"]:
        lines.append(
            " & ".join(
                latex_escape(value)
                for value in (
                    row["agent_id"],
                    row["scope"],
                    row["pairs"],
                    fmt(row["pass_rate_change"]),
                    _range_text(row, "pass_rate_change"),
                    fmt(row["median_paired_time_change"]),
                    _range_text(row, "median_paired_time_change"),
                    fmt(row["median_paired_token_change"], 1),
                    _range_text(row, "median_paired_token_change", 1),
                )
            )
            + r" \\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{longtable}",
            r"\subsection*{Per-task paired changes (L minus N)}",
            r"\scriptsize",
            r"\begin{longtable}{lllrrrrrr}",
            r"\toprule",
            r"Task & Tier & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"Task & Tier & Pairs & Pass $\Delta$ & 95\% & Time $\Delta$ & 95\% & Token $\Delta$ & 95\% \\",
            r"\midrule",
            r"\endhead",
        ]
    )
    for row in analysis["per_task_paired_comparisons"]:
        lines.append(
            " & ".join(
                latex_escape(value)
                for value in (
                    row["task_id"],
                    row["tier"],
                    row["pairs"],
                    fmt(row["pass_rate_change"]),
                    _range_text(row, "pass_rate_change"),
                    fmt(row["median_paired_time_change"]),
                    _range_text(row, "median_paired_time_change"),
                    fmt(row["median_paired_token_change"], 1),
                    _range_text(row, "median_paired_token_change", 1),
                )
            )
            + r" \\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{longtable}",
            r"\subsection*{Every raw run and system incident}",
            r"\scriptsize",
            r"\begin{longtable}{llllrrrrll}",
            r"\toprule",
            r"Run & Task & Tier & Cond. & Scored & Pass & Seconds & Tokens & L-use & Failure \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"Run & Task & Tier & Cond. & Scored & Pass & Seconds & Tokens & L-use & Failure \\",
            r"\midrule",
            r"\endhead",
        ]
    )
    for row in analysis["per_run_results"]:
        lines.append(
            " & ".join(
                latex_escape(value)
                for value in (
                    row["run_id"],
                    row["task_id"],
                    row["tier"],
                    row["condition"],
                    row["scored"],
                    row["pass"],
                    fmt(row["scored_elapsed_seconds"]),
                    row["model_tokens"],
                    row["library_use"],
                    row["failure_code"],
                )
            )
            + r" \\"
        )
    bootstrap_notes = sorted(
        {
            str(row.get("bootstrap", {}).get("note", ""))
            for row in analysis["paired_comparisons"]
            if row.get("bootstrap", {}).get("note")
        }
    )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{longtable}",
            (
                "Paired changes are the median of each matched run's L minus N difference. "
                "Ranges are 95 percent percentile bootstrap ranges made by resampling whole papers. "
                + (" ".join(bootstrap_notes) if bootstrap_notes else "")
            ),
            r"\end{document}",
            "",
        ]
    )
    return "\n".join(lines)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw_jsonl", type=Path, nargs="+")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--run-order", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--repository-root", type=Path, required=True)
    parser.add_argument("--include-unscored", action="store_true")
    parser.add_argument(
        "--observational-pilot",
        action="store_true",
        help=(
            "allow a complete matrix of explicitly unscored runs and emit clearly "
            "labeled observational tables while leaving official scores invalid"
        ),
    )
    parser.add_argument("--bootstrap-resamples", type=int, default=10_000)
    parser.add_argument("--bootstrap-seed", type=int, default=20260725)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        if args.bootstrap_resamples < 0:
            raise BenchmarkToolError("bootstrap resample count must be nonnegative")
        runs, malformed = load_runs(args.raw_jsonl)
        if malformed:
            raise BenchmarkToolError(
                f"raw result input contains {len(malformed)} malformed lines"
            )
        run_order = read_json(args.run_order)
        config = read_json(args.config)
        manifest = read_json(args.manifest)
        if not all(isinstance(value, dict) for value in (run_order, config, manifest)):
            raise BenchmarkToolError("run order, config, and manifest must be JSON objects")
        analysis = analyze(
            runs,
            include_unscored=args.include_unscored,
            bootstrap_resamples=args.bootstrap_resamples,
            bootstrap_seed=args.bootstrap_seed,
            run_order=run_order,
            config=config,
            manifest=manifest,
            repository_root=args.repository_root,
            require_complete=True,
            observational_pilot=args.observational_pilot,
        )
        analysis["malformed_input_lines"] = malformed
        args.output_dir.mkdir(parents=True, exist_ok=True)
        write_json(args.output_dir / "summary.json", analysis)
        write_json(args.output_dir / "result_set_check.json", analysis["result_set_check"])
        write_csv_tables(args.output_dir, analysis)
        (args.output_dir / "summary.tex").write_text(
            render_latex(analysis), encoding="utf-8"
        )
        print(json.dumps({
            "summary": str(args.output_dir / "summary.json"),
            "condition_csv": str(args.output_dir / "condition_summary.csv"),
            "paired_csv": str(args.output_dir / "paired_summary.csv"),
            "task_csv": str(args.output_dir / "task_summary.csv"),
            "task_paired_csv": str(args.output_dir / "task_paired_summary.csv"),
            "run_csv": str(args.output_dir / "run_results.csv"),
            "t4_coverage_csv": str(
                args.output_dir / "t4_whole_paper_coverage.csv"
            ),
            "observational_condition_csv": (
                str(args.output_dir / "observational_condition_summary.csv")
                if analysis["observational_pilot_results"] is not None
                else None
            ),
            "observational_task_csv": (
                str(args.output_dir / "observational_task_summary.csv")
                if analysis["observational_pilot_results"] is not None
                else None
            ),
            "observational_paired_csv": (
                str(args.output_dir / "observational_paired_summary.csv")
                if analysis["observational_pilot_results"] is not None
                else None
            ),
            "observational_task_paired_csv": (
                str(args.output_dir / "observational_task_paired_summary.csv")
                if analysis["observational_pilot_results"] is not None
                else None
            ),
            "latex": str(args.output_dir / "summary.tex"),
            "runs": analysis["analyzed_run_count"],
            "official_scores_valid": analysis["official_scores_valid"],
        }, indent=2, sort_keys=True))
        return 0 if not analysis["pair_problems"] else 1
    except BenchmarkToolError as error:
        print(f"error: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
