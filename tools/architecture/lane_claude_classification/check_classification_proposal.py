#!/usr/bin/env python3
"""Deterministic structural checker for the 386-row classification proposal."""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path

from check_read_only_inventory import verify as verify_inventory
from generate_classification_proposal import FIELDS
from lane_common import (
    CLASSIFICATION_ROOT,
    EVIDENCE_HEAD,
    ROOT,
    module_from_path,
    read_tsv,
    sha256_file,
    source_analysis,
)


ALLOWED_TIERS = {
    "reusable",
    "source",
    "compatibility",
    "aggregate",
    "mixed_pending_split",
    "internal",
}


def check(root: Path) -> dict[str, object]:
    input_path = root / "input-modules.tsv"
    exclusions_path = root / "exclusions.tsv"
    proposal_path = root / "modules.tsv"
    summary_path = root / "summary.json"
    partition = verify_inventory(input_path, exclusions_path)
    inputs = read_tsv(input_path)
    proposals = read_tsv(proposal_path)
    if list(proposals[0]) != FIELDS:
        raise ValueError("proposal schema differs from the required twelve columns")
    input_modules = {row["module"]: row for row in inputs}
    proposal_modules = {row["module"]: row for row in proposals}
    if len(proposal_modules) != len(proposals):
        raise ValueError("duplicate proposal module")
    if set(input_modules) != set(proposal_modules):
        raise ValueError("proposal does not exactly cover input inventory")
    if [row["module"] for row in proposals] != sorted(proposal_modules):
        raise ValueError("proposal rows are not sorted by module")

    counts: collections.Counter[str] = collections.Counter()
    for row in proposals:
        module = row["module"]
        if row["path"] != input_modules[module]["path"]:
            raise ValueError(f"{module}: proposal path changed")
        if module_from_path(row["path"]) != module:
            raise ValueError(f"{module}: path mismatch")
        tier = row["proposed_tier"]
        if tier not in ALLOWED_TIERS:
            raise ValueError(f"{module}: invalid tier {tier}")
        if row["confidence"] not in {"high", "medium", "low"}:
            raise ValueError(f"{module}: invalid confidence")
        for required in FIELDS[4:]:
            if not row[required].strip():
                raise ValueError(f"{module}: empty {required}")
        analysis = source_analysis(ROOT / row["path"])
        actual_imports = ";".join(analysis["imports"]) or "NONE"
        if actual_imports != row["direct_project_imports"]:
            raise ValueError(f"{module}: direct imports drifted from proposal evidence")
        if tier == "aggregate" and analysis["declarations"]:
            raise ValueError(f"{module}: aggregate owns declarations")
        if tier == "mixed_pending_split" and "Split " not in row["required_action"]:
            raise ValueError(f"{module}: mixed row lacks a concrete split action")
        counts[tier] += 1

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    if summary["review_evidence_head"] != EVIDENCE_HEAD:
        raise ValueError("summary evidence head drift")
    if summary["proposal_rows"] != len(proposals):
        raise ValueError("summary row count drift")
    if summary["hashes"]["modules_sha256"] != sha256_file(proposal_path):
        raise ValueError("summary proposal hash drift")
    for tier in ALLOWED_TIERS:
        if summary["tier_counts"].get(tier, 0) != counts[tier]:
            raise ValueError(f"summary tier count drift: {tier}")
    return {
        "status": "PASS",
        "proposal_rows": len(proposals),
        "tier_counts": {tier: counts[tier] for tier in sorted(ALLOWED_TIERS)},
        "partition": partition,
        "proposal_sha256": sha256_file(proposal_path),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proposal-root", type=Path, default=CLASSIFICATION_ROOT)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        assert len(FIELDS) == 12
        assert ALLOWED_TIERS == {
            "reusable",
            "source",
            "compatibility",
            "aggregate",
            "mixed_pending_split",
            "internal",
        }
        print("check_classification_proposal self-test: PASS")
        return
    if not args.check:
        parser.error("use --check or --self-test")
    print(json.dumps(check(args.proposal_root.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
