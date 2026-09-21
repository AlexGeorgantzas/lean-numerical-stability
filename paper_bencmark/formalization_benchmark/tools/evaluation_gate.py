"""Evaluate the frozen Pilot-15 effect gate from authenticated pair states."""

from __future__ import annotations

from statistics import median
from typing import Any, Mapping

from common import BenchmarkError, utc_now


def _number(value: Any, label: str) -> float:
    if not isinstance(value, (int, float)) or isinstance(value, bool) or value < 0:
        raise BenchmarkError(f"evaluation gate has malformed {label}")
    return float(value)


def evaluate_gate(controller: Any, config: Mapping[str, Any]) -> dict[str, Any]:
    policy = config.get("evaluation_gate")
    if not isinstance(policy, Mapping):
        raise BenchmarkError("evaluation gate policy is missing")
    rows: list[dict[str, Any]] = []
    pending: list[str] = []
    for task_id in policy["primary_task_ids"]:
        state = controller.status(task_id)
        if state.get("status") != "COMPLETE":
            pending.append(task_id)
            rows.append({"task_id": task_id, "status": state.get("status")})
            continue
        conditions = state.get("conditions")
        if not isinstance(conditions, Mapping) or set(conditions) != {"N", "L"}:
            raise BenchmarkError(f"{task_id} has malformed condition summaries")
        n = conditions["N"]
        l = conditions["L"]
        faithful = all(
            isinstance(item, Mapping) and item.get("status") == "ACCEPTED_FAITHFUL"
            for item in (n, l)
        )
        n_time = _number(n.get("active_seconds"), f"{task_id} N active time")
        l_time = _number(l.get("active_seconds"), f"{task_id} L active time")
        n_tokens = _number(
            n.get("contestant_net_new_usage", {}).get("net_new_tokens"),
            f"{task_id} N net-new tokens",
        )
        l_tokens = _number(
            l.get("contestant_net_new_usage", {}).get("net_new_tokens"),
            f"{task_id} L net-new tokens",
        )
        time_reduction = (n_time - l_time) / n_time if n_time else 0.0
        token_reduction = (n_tokens - l_tokens) / n_tokens if n_tokens else 0.0
        rows.append(
            {
                "task_id": task_id,
                "status": "COMPLETE",
                "both_faithful": faithful,
                "N_active_seconds": n_time,
                "L_active_seconds": l_time,
                "time_reduction_fraction": time_reduction,
                "N_net_new_tokens": int(n_tokens),
                "L_net_new_tokens": int(l_tokens),
                "net_new_token_reduction_fraction": token_reduction,
                "L_library_uptake": l.get("library_uptake"),
            }
        )
    complete_rows = [row for row in rows if row.get("status") == "COMPLETE"]
    time_reductions = [float(row["time_reduction_fraction"]) for row in complete_rows]
    token_reductions = [
        float(row["net_new_token_reduction_fraction"]) for row in complete_rows
    ]
    time_positive_pairs = sum(value > 0 for value in time_reductions)
    all_faithful = bool(complete_rows) and all(
        row.get("both_faithful") is True for row in complete_rows
    )
    median_time = median(time_reductions) if time_reductions else None
    median_tokens = median(token_reductions) if token_reductions else None
    passed = (
        not pending
        and len(complete_rows) == len(policy["primary_task_ids"])
        and (
            not policy["require_both_conditions_faithful"] or all_faithful
        )
        and time_positive_pairs >= policy["minimum_time_positive_pairs"]
        and median_time is not None
        and median_time >= policy["minimum_median_time_reduction_fraction"]
        and median_tokens is not None
        and median_tokens
        >= policy["minimum_median_net_new_token_reduction_fraction"]
    )
    return {
        "schema_version": "formalization-evaluation-gate-1",
        "pilot_id": config["pilot_id"],
        "evaluated_at_utc": utc_now(),
        "status": "PASSED" if passed else ("PENDING" if pending else "FAILED"),
        "scientific_task_ids": list(policy["primary_task_ids"]),
        "canary_task_id": policy["canary_task_id"],
        "canary_excluded": policy["canary_excluded_from_scientific_results"],
        "pending_task_ids": pending,
        "time_positive_pairs": time_positive_pairs,
        "median_time_reduction_fraction": median_time,
        "median_net_new_token_reduction_fraction": median_tokens,
        "all_pairs_both_faithful": all_faithful,
        "policy": dict(policy),
        "tasks": rows,
    }
