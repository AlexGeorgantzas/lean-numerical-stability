#!/usr/bin/env python3
"""Validate the source-presentation tags assigned to HighamBench tasks."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json  # type: ignore


ALLOWED_SOURCE_TAGS = ("THM", "LEM", "PROP", "COR", "EQN", "TXT", "UNL")
TASK_SCHEMA_VERSION = "highambench-task-0.3"
NAMED_SOURCE_TAGS = {
    "THM": "Theorem",
    "LEM": "Lemma",
    "PROP": "Proposition",
    "COR": "Corollary",
}


def _label(task: Mapping[str, Any], fallback: str) -> str:
    task_id = task.get("task_id")
    return task_id if isinstance(task_id, str) and task_id else fallback


def validate_task_source_tags(
    task: Mapping[str, Any], *, label: str = "task"
) -> dict[str, Any]:
    """Validate one task record and return its normalized tag summary."""

    task_label = _label(task, label)
    if task.get("schema_version") != TASK_SCHEMA_VERSION:
        raise BenchmarkToolError(
            f"{task_label} schema_version must be {TASK_SCHEMA_VERSION!r}"
        )
    raw_tags = task.get("source_tags")
    if not isinstance(raw_tags, list) or not raw_tags:
        raise BenchmarkToolError(f"{task_label} source_tags must be a nonempty list")
    if any(not isinstance(tag, str) or not tag for tag in raw_tags):
        raise BenchmarkToolError(f"{task_label} source_tags must contain strings")
    tags = list(raw_tags)
    unknown = [tag for tag in tags if tag not in ALLOWED_SOURCE_TAGS]
    if unknown:
        raise BenchmarkToolError(
            f"{task_label} has unknown source tags: {', '.join(unknown)}"
        )
    if len(set(tags)) != len(tags):
        raise BenchmarkToolError(f"{task_label} repeats a source tag")
    expected_order = sorted(tags, key=ALLOWED_SOURCE_TAGS.index)
    if tags != expected_order:
        raise BenchmarkToolError(
            f"{task_label} source_tags must use canonical order: {expected_order}"
        )

    named = [tag for tag in tags if tag in NAMED_SOURCE_TAGS]
    author_label = task.get("author_label")
    if named:
        if len(named) != 1 or len(tags) != 1:
            raise BenchmarkToolError(
                f"{task_label} must use exactly one named source tag"
            )
        if not isinstance(author_label, str) or not author_label.strip():
            raise BenchmarkToolError(
                f"{task_label} {named[0]} tag requires an exact author_label"
            )
        printed_kind = NAMED_SOURCE_TAGS[named[0]]
        if (
            re.match(
                rf"^{re.escape(printed_kind)}(?:\s|$)",
                author_label,
                flags=re.IGNORECASE,
            )
            is None
        ):
            raise BenchmarkToolError(
                f"{task_label} author_label must begin with {printed_kind!r}"
            )
    elif author_label is not None:
        raise BenchmarkToolError(
            f"{task_label} author_label must be null for non-named source tags"
        )

    if "EQN" in tags and "UNL" in tags:
        raise BenchmarkToolError(
            f"{task_label} cannot be both a numbered equation and an unnumbered display"
        )
    measurement_ready = task.get("classification_frozen_before_runs")
    if not isinstance(measurement_ready, bool):
        raise BenchmarkToolError(
            f"{task_label} classification_frozen_before_runs must be a boolean"
        )
    locations = task.get("source_locations")
    if not isinstance(locations, list) or not locations:
        raise BenchmarkToolError(f"{task_label} must record source_locations evidence")

    return {
        "task_id": task.get("task_id"),
        "source_tags": tags,
        "author_label": author_label,
        "measurement_ready": measurement_ready,
    }


def task_record_paths(benchmark_root: Path) -> list[Path]:
    """Return every canonical ``tasks/P*/T*/task.json`` path."""

    root = benchmark_root.resolve()
    paths: list[Path] = []
    for path in sorted((root / "tasks").glob("P*/T*/task.json")):
        relative = path.relative_to(root)
        if len(relative.parts) != 4:
            continue
        paper_id, tier = relative.parts[1:3]
        if re.fullmatch(r"P[0-9]+", paper_id) is None:
            continue
        if re.fullmatch(r"T[0-9]+", tier) is None:
            continue
        paths.append(path)
    return paths


def validate_task_catalog(benchmark_root: Path) -> dict[str, Any]:
    """Validate all task records below a benchmark root."""

    root = benchmark_root.resolve()
    paths = task_record_paths(root)
    if not paths:
        raise BenchmarkToolError(f"no task records found below {root / 'tasks'}")
    records: list[dict[str, Any]] = []
    errors: list[str] = []
    for path in paths:
        relative = path.relative_to(root)
        expected_task_id = f"{relative.parts[1]}-{relative.parts[2]}"
        try:
            value = read_json(path)
            if not isinstance(value, Mapping):
                raise BenchmarkToolError(f"{expected_task_id} task record must be an object")
            if value.get("task_id") != expected_task_id:
                raise BenchmarkToolError(
                    f"{relative.as_posix()} has task_id={value.get('task_id')!r}, "
                    f"expected {expected_task_id!r}"
                )
            records.append(
                {
                    **validate_task_source_tags(value, label=expected_task_id),
                    "path": relative.as_posix(),
                }
            )
        except BenchmarkToolError as error:
            errors.append(str(error))
    if errors:
        raise BenchmarkToolError("task source-tag validation failed:\n- " + "\n- ".join(errors))
    return {
        "ok": True,
        "allowed_source_tags": list(ALLOWED_SOURCE_TAGS),
        "task_count": len(records),
        "tasks": records,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--json", action="store_true", help="print the full JSON result")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = validate_task_catalog(args.benchmark_root)
    except BenchmarkToolError as error:
        print(f"task-tags error: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"task source tags valid: {result['task_count']} tasks")
        for task in result["tasks"]:
            tags = "+".join(task["source_tags"])
            author = task["author_label"] or "no author label"
            state = "measurement-ready" if task["measurement_ready"] else "construction"
            print(f"  {task['task_id']}: {tags} ({author}; {state})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
