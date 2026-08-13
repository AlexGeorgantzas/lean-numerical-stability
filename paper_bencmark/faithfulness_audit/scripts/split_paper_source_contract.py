#!/usr/bin/env python3
"""Validate and split one paper-level source contract into task-local outputs."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

try:
    from .common import AUDIT_SCHEMA_VERSION, sha256_file
    from .prepare_audit import REPOSITORY_ROOT
    from .validate_agent_output import validate_role
    from .validate_audit import task_paths, validate_prepared
except ImportError:  # Direct script execution.
    from common import AUDIT_SCHEMA_VERSION, sha256_file  # type: ignore
    from prepare_audit import REPOSITORY_ROOT  # type: ignore
    from validate_agent_output import validate_role  # type: ignore
    from validate_audit import task_paths, validate_prepared  # type: ignore


CONTRACT_FIELDS = {
    "task_id",
    "source_evidence",
    "statement",
    "undebatable_constraints",
    "ambiguities",
    "contract_plain_english",
}

BATCH_FIELDS = {
    "schema_version",
    "role",
    "paper_id",
    "paper_sha256",
    "source_locator_sha256",
    "task_ids",
    "contracts",
}


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


def split_contract(path: Path) -> list[Path]:
    batch = load_json(path)
    if set(batch) != BATCH_FIELDS:
        raise RuntimeError("paper source contract fields are incomplete or unexpected")
    if batch.get("schema_version") != AUDIT_SCHEMA_VERSION:
        raise RuntimeError("paper source contract has the wrong schema version")
    if batch.get("role") != "paper-source-contract":
        raise RuntimeError("paper source contract has the wrong role")
    paper_id = batch.get("paper_id")
    if not isinstance(paper_id, str) or re.fullmatch(r"P\d{2}", paper_id) is None:
        raise RuntimeError("paper source contract has an invalid paper ID")
    task_ids = batch.get("task_ids")
    contracts = batch.get("contracts")
    if not isinstance(task_ids, list) or not isinstance(contracts, list):
        raise RuntimeError("paper source contract lacks task IDs or contracts")
    expected_task_ids = [f"{paper_id}-T{tier}" for tier in range(1, 4)]
    if task_ids != expected_task_ids:
        raise RuntimeError("paper source contract must contain T1, T2, and T3 in order")
    if [item.get("task_id") for item in contracts if isinstance(item, dict)] != task_ids:
        raise RuntimeError("paper source contracts are missing, duplicated, or out of order")

    canonical = json.dumps(batch, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    batch_hash = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    written: list[Path] = []
    for task_id, contract in zip(task_ids, contracts, strict=True):
        if not isinstance(contract, dict) or set(contract) != CONTRACT_FIELDS:
            raise RuntimeError(f"{task_id}: contract fields are incomplete or unexpected")
        manifest, errors = validate_prepared(task_id)
        if errors:
            raise RuntimeError(f"{task_id}: prepared audit is invalid: {'; '.join(errors)}")
        paper_batch = manifest.get("paper_batch", {})
        if paper_batch.get("task_ids") != task_ids:
            raise RuntimeError(f"{task_id}: batch task inventory mismatch")
        source_locator = paper_batch.get("source_locator", {})
        if source_locator.get("sha256") != batch.get("source_locator_sha256"):
            raise RuntimeError(f"{task_id}: paper source locator hash mismatch")
        if manifest.get("paper", {}).get("sha256") != batch.get("paper_sha256"):
            raise RuntimeError(f"{task_id}: paper hash mismatch")

        _, audit_dir = task_paths(task_id)
        output_dir = audit_dir / "agent_outputs"
        output_dir.mkdir(parents=True, exist_ok=True)
        batch_path = output_dir / "paper_source_contract.json"
        batch_path.write_text(canonical, encoding="utf-8")
        if sha256_file(batch_path) != batch_hash:
            raise RuntimeError(f"{task_id}: paper batch hash changed while writing")
        task_output = {
            "schema_version": AUDIT_SCHEMA_VERSION,
            "role": "source-contract",
            "paper_sha256": batch["paper_sha256"],
            "paper_batch_sha256": batch_hash,
            **contract,
        }
        output_path = output_dir / "source_contract.json"
        write_json(output_path, task_output)
        validate_role(task_id, "source-contract")
        written.append(output_path)
    return written


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path, help="paper-source-contract JSON returned by the agent")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        outputs = split_contract(args.file)
    except Exception as error:
        print(f"paper source contract error: {error}", file=sys.stderr)
        return 2
    print(
        json.dumps(
            [output.relative_to(REPOSITORY_ROOT).as_posix() for output in outputs],
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
