#!/usr/bin/env python3
"""Verify the packet's frozen 386 + 217 classification partition."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from lane_common import (
    BASE_SHA,
    CLASSIFICATION_ROOT,
    git,
    git_show_bytes,
    module_from_path,
    read_tsv,
    sha256_file,
)


EXPECTED_INPUT_SHA = "C0B1C88F34461A44305D269C880F7581BDD7F1D9CC69CF9A144EA099C6A6DF54"
EXPECTED_EXCLUSIONS_SHA = "8CCBFA4191741B37BD3DD5748079A7505AF008A515077A25BABE9E23825B73C8"


def classified_at_base(module: str, manifest: dict[str, object]) -> bool:
    exact = manifest["exact"]
    if module in exact:
        return True
    rules = sorted(
        ((str(item["prefix"]), str(item["tier"])) for item in manifest["prefixes"]),
        key=lambda item: (-len(item[0]), item[0]),
    )
    return any(module == prefix or module.startswith(prefix + ".") for prefix, _ in rules)


def verify(input_path, exclusions_path) -> dict[str, object]:
    inventory = read_tsv(input_path)
    exclusions = read_tsv(exclusions_path)
    if sha256_file(input_path) != EXPECTED_INPUT_SHA:
        raise ValueError("input queue hash differs from the frozen packet")
    if sha256_file(exclusions_path) != EXPECTED_EXCLUSIONS_SHA:
        raise ValueError("exclusion queue hash differs from the frozen packet")

    def modules(rows: list[dict[str, str]], label: str) -> set[str]:
        result: set[str] = set()
        for row in rows:
            module, path = row["module"], row["path"]
            if module_from_path(path) != module:
                raise ValueError(f"{label}: module/path mismatch: {module} / {path}")
            if module in result:
                raise ValueError(f"{label}: duplicate module: {module}")
            result.add(module)
        return result

    queued = modules(inventory, "input")
    excluded = modules(exclusions, "exclusions")
    overlap = sorted(queued & excluded)
    if overlap:
        raise ValueError(f"inventories overlap: {overlap[:5]}")

    manifest = json.loads(git_show_bytes(BASE_SHA, "docs/architecture/tiers.json"))
    paths = [
        line
        for line in git("ls-tree", "-r", "--name-only", BASE_SHA, "--", "NumStability").splitlines()
        if line.endswith(".lean")
    ]
    base_modules = {module_from_path(path) for path in paths}
    unclassified = {
        module for module in base_modules if not classified_at_base(module, manifest)
    }
    union = queued | excluded
    missing = sorted(unclassified - union)
    extra = sorted(union - unclassified)
    if missing or extra:
        raise ValueError(
            f"not an exact base partition: missing={missing[:5]} extra={extra[:5]}"
        )
    result = {
        "base_sha": BASE_SHA,
        "input_count": len(queued),
        "exclusion_count": len(excluded),
        "intersection_count": len(overlap),
        "union_count": len(union),
        "authoritative_unclassified_count": len(unclassified),
        "partition_exact": True,
        "input_sha256": sha256_file(input_path),
        "exclusions_sha256": sha256_file(exclusions_path),
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input", type=Path, default=CLASSIFICATION_ROOT / "input-modules.tsv"
    )
    parser.add_argument(
        "--exclusions", type=Path, default=CLASSIFICATION_ROOT / "exclusions.tsv"
    )
    args = parser.parse_args()
    print(json.dumps(verify(args.input, args.exclusions), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
