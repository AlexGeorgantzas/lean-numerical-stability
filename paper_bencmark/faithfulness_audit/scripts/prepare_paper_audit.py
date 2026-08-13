#!/usr/bin/env python3
"""Prepare all three tasks for one paper and attach a shared source locator."""

from __future__ import annotations

import argparse
import json
import re
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

try:
    from .common import AUDIT_SCHEMA_VERSION, sha256_file
    from .prepare_audit import HIGHAMBENCH_ROOT, REPOSITORY_ROOT, prepare
    from .validate_audit import validate
except ImportError:  # Direct script execution.
    from common import AUDIT_SCHEMA_VERSION, sha256_file  # type: ignore
    from prepare_audit import HIGHAMBENCH_ROOT, REPOSITORY_ROOT, prepare  # type: ignore
    from validate_audit import validate  # type: ignore


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object in {path}")
    return value


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def paper_task_ids(paper_id: str) -> list[str]:
    normalized = paper_id.upper()
    if re.fullmatch(r"P\d{2}", normalized) is None:
        raise RuntimeError(f"invalid paper ID {paper_id!r}; expected P03")
    task_ids = [f"{normalized}-T{tier}" for tier in range(1, 4)]
    missing = [
        task_id
        for task_id in task_ids
        if not (
            HIGHAMBENCH_ROOT
            / "tasks"
            / normalized
            / task_id.rsplit("-", 1)[1]
            / "task.json"
        ).is_file()
    ]
    if missing:
        raise RuntimeError("missing paper tasks: " + ", ".join(missing))
    return task_ids


def prepare_paper(paper_id: str, *, force: bool = False) -> list[Path]:
    task_ids = paper_task_ids(paper_id)
    with ThreadPoolExecutor(max_workers=len(task_ids)) as executor:
        outputs = list(executor.map(lambda task_id: prepare(task_id, force=force), task_ids))

    locators: list[dict[str, Any]] = []
    manifests: list[tuple[Path, dict[str, Any]]] = []
    for task_id, output in zip(task_ids, outputs, strict=True):
        validate(task_id, "prepared")
        locator = load_json(output / "inputs" / "source_locator.json")
        manifest_path = output / "manifest.json"
        locators.append(locator)
        manifests.append((manifest_path, load_json(manifest_path)))

    paper_hashes = {locator.get("paper_sha256") for locator in locators}
    paper_paths = {locator.get("paper_path") for locator in locators}
    paper_versions = {locator.get("paper_version") for locator in locators}
    if len(paper_hashes) != 1 or len(paper_paths) != 1 or len(paper_versions) != 1:
        raise RuntimeError("the three tasks do not identify one paper version and file")

    combined = {
        "schema_version": AUDIT_SCHEMA_VERSION,
        "role": "paper-source-locator",
        "paper_id": paper_id.upper(),
        "paper_path": next(iter(paper_paths)),
        "paper_sha256": next(iter(paper_hashes)),
        "paper_version": next(iter(paper_versions)),
        "tasks": [
            {
                "task_id": locator["task_id"],
                "source_locations": locator["source_locations"],
            }
            for locator in locators
        ],
        "evidence_policy": (
            "Use only the referenced PDF and surrounding paper context as evidence. "
            "Produce an independent contract for every listed task."
        ),
    }

    for output, (manifest_path, manifest) in zip(outputs, manifests, strict=True):
        locator_path = output / "inputs" / "paper_source_locator.json"
        write_json(locator_path, combined)
        locator_record = {
            "path": locator_path.relative_to(REPOSITORY_ROOT).as_posix(),
            "sha256": sha256_file(locator_path),
        }
        manifest["inputs"]["paper_source_locator"] = locator_record
        manifest["paper_batch"] = {
            "paper_id": paper_id.upper(),
            "task_ids": task_ids,
            "source_locator": locator_record,
        }
        write_json(manifest_path, manifest)

    for task_id in task_ids:
        validate(task_id, "prepared")
    return outputs


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper_id", help="paper ID such as P03")
    parser.add_argument("--force", action="store_true")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        outputs = prepare_paper(args.paper_id, force=args.force)
    except Exception as error:
        print(f"paper audit preparation error: {error}", file=sys.stderr)
        return 2
    print(
        json.dumps(
            {
                "paper_id": args.paper_id.upper(),
                "task_directories": [
                    output.relative_to(REPOSITORY_ROOT).as_posix() for output in outputs
                ],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
