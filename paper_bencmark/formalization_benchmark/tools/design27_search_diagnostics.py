#!/usr/bin/env python3
"""Post-hoc, read-only tool-time diagnostics for frozen Pilot 27 turns.

This is not a replacement for the contestant clock. Model reasoning between
search calls cannot be attributed cleanly to retrieval, and command durations
may overlap. The report therefore labels only explicit tool-wall intervals.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from common import BenchmarkError, load_json, write_json_atomic


SCHEMA = "pilot-27-search-diagnostic-1"


def _category(command: str) -> str:
    lowered = command.lower()
    if any(marker in lowered for marker in (
        "lean --root", "lake env lean", "lean candidate.lean",
        "candidate.lean -o", "-o candidate.olean",
    )):
        return "candidate_compile"
    if "source/paper.pdf" in lowered or "source/task.md" in lowered:
        return "paper_or_task_read"
    library = any(marker in lowered for marker in (
        "/library/", "/library-olean/", "/packages/mathlib/",
        "numstability.", "#check", "library_api.md",
    ))
    search = any(marker in lowered for marker in (
        "rg ", "grep ", "find ", "sed ", "head ", "#check",
        "#print", "#source", "ls ", "cat ",
    ))
    if library and search:
        return "explicit_library_search_or_type_probe"
    return "other_command"


def inspect_events(path: Path) -> dict[str, Any]:
    if not path.is_file() or path.is_symlink():
        raise BenchmarkError(f"missing/unsafe event log: {path}")
    started: dict[str, tuple[int, str]] = {}
    intervals: list[dict[str, Any]] = []
    turn_started: int | None = None
    first_edit: int | None = None
    for line in path.read_text(encoding="utf-8").splitlines():
        event = json.loads(line)
        method = event.get("method")
        timestamp = event.get("emittedAtMs")
        if not isinstance(timestamp, int):
            continue
        if method == "turn/started" and turn_started is None:
            turn_started = timestamp
        if method not in {"item/started", "item/completed"}:
            continue
        item = event.get("params", {}).get("item", {})
        kind, item_id = item.get("type"), item.get("id")
        if kind == "fileChange" and method == "item/started" and first_edit is None:
            first_edit = timestamp
        if kind != "commandExecution" or not isinstance(item_id, str):
            continue
        if method == "item/started":
            started[item_id] = (timestamp, _category(str(item.get("command", ""))))
        elif item_id in started:
            begin, category = started.pop(item_id)
            if timestamp >= begin:
                intervals.append({
                    "start_ms": begin, "end_ms": timestamp,
                    "seconds": (timestamp - begin) / 1000,
                    "category": category,
                })
    by_category: dict[str, float] = {}
    for item in intervals:
        category = item["category"]
        by_category[category] = by_category.get(category, 0.0) + item["seconds"]
    return {
        "schema_version": SCHEMA,
        "event_path": str(path),
        "command_count": len(intervals),
        "incomplete_command_count": len(started),
        "tool_wall_seconds_by_category_not_deduplicated": by_category,
        "pre_first_file_change_seconds_includes_paper_and_reasoning": (
            (first_edit - turn_started) / 1000
            if first_edit is not None and turn_started is not None
            and first_edit >= turn_started else None
        ),
        "interpretation": (
            "Explicit command wall only. Search-related model reasoning and "
            "overlap are not isolated; do not subtract this from headline time "
            "or claim a no-search counterfactual."
        ),
    }


def inspect_pair(root: Path) -> dict[str, Any]:
    pair_path = root / "pair-report.json"
    pair = load_json(pair_path)
    result: dict[str, Any] = {
        "schema_version": SCHEMA,
        "task_id": pair["task_id"],
        "pair_status": pair["status"],
        "conditions": {},
    }
    for condition in ("R0", "R1"):
        turns: list[dict[str, Any]] = []
        line_metrics: dict[str, Any] = {}
        for stage in ("submissions", "proof-submissions"):
            for path in sorted((root / condition / stage).glob("*/formalizer/events.jsonl")):
                turns.append({"stage": stage, **inspect_events(path)})
            validations = sorted((root / condition / stage).glob("*/validation.json"))
            if validations:
                final = load_json(validations[-1])
                line_metrics[stage] = {
                    "final_validation_path": str(validations[-1]),
                    "validation_pass": final.get("pass") is True,
                    "raw_lines": (final.get("candidate") or {}).get("lines"),
                    "nonblank_code_lines": (
                        final.get("source_check") or {}
                    ).get("nonblank_code_lines"),
                }
        result["conditions"][condition] = {
            "turns": turns,
            "line_metrics": line_metrics,
        }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pair_root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = inspect_pair(args.pair_root)
    if args.output is not None:
        if args.output.exists():
            raise BenchmarkError("diagnostic output already exists")
        write_json_atomic(args.output, result, mode=0o400)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
