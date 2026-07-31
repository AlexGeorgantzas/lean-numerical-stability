#!/usr/bin/env python3
"""Validate the frozen read-only classification inventory tracked in this proposal.

The proposal carries a byte-for-byte copy of the external handoff packet's
``READ_ONLY_MODULES.tsv`` at
``docs/architecture/lane-proposals/claude-classification/classification/input-modules.tsv``
so that the proposal and its checker stay reproducible after the packet has
been removed.  This checker proves:

* the tracked copy hashes to the frozen SHA-256 of the packet inventory;
* it has exactly 386 rows, unique and sorted by module, with the frozen header;
* every module name is derivable from its path and every path exists;
* every listed module is still unclassified in ``docs/architecture/tiers.json``;
* the inventory is disjoint from the packet exclusion list and, together with
  it, partitions the authoritative unclassified snapshot (when the optional
  exclusion list is supplied).

Nothing here writes to the repository.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import module_evidence as me


ROOT = Path(__file__).resolve().parents[3]
PROPOSAL = ROOT / "docs/architecture/lane-proposals/claude-classification"
INPUT_INVENTORY = PROPOSAL / "classification/input-modules.tsv"
TIERS = ROOT / "docs/architecture/tiers.json"

EXPECTED_ROWS = 386
EXPECTED_HEADER = ("module", "path", "baseline_state")
# SHA-256 of the packet file READ_ONLY_MODULES.tsv at frozen base
# 6487fc33088523b8f27ecde9ad613515b78f9977.
EXPECTED_SHA256 = "C0B1C88F34461A44305D269C880F7581BDD7F1D9CC69CF9A144EA099C6A6DF54"
EXPECTED_EXCLUSIONS = 217
EXPECTED_SNAPSHOT = 603


def sha256_upper(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def existing_tier(module: str, manifest: dict) -> str | None:
    exact = manifest["exact"]
    if module in exact:
        return exact[module]
    prefixes = sorted(
        ((rule["prefix"], rule["tier"]) for rule in manifest["prefixes"]),
        key=lambda item: (-len(item[0]), item[0]),
    )
    for prefix, tier in prefixes:
        if module == prefix or module.startswith(prefix + "."):
            return tier
    return None


def check(exclusions: Path | None) -> list[str]:
    failures: list[str] = []
    if not INPUT_INVENTORY.is_file():
        return [f"missing tracked inventory: {INPUT_INVENTORY.relative_to(ROOT)}"]

    digest = sha256_upper(INPUT_INVENTORY)
    if digest != EXPECTED_SHA256:
        failures.append(
            f"tracked inventory SHA-256 is {digest}; expected the frozen packet value "
            f"{EXPECTED_SHA256}"
        )

    header, rows = me.read_tsv(INPUT_INVENTORY)
    if header != EXPECTED_HEADER:
        failures.append(f"unexpected header {header}; expected {EXPECTED_HEADER}")
        return failures
    if len(rows) != EXPECTED_ROWS:
        failures.append(f"expected {EXPECTED_ROWS} rows, found {len(rows)}")

    modules = [row["module"] for row in rows]
    if len(set(modules)) != len(modules):
        duplicates = sorted({name for name in modules if modules.count(name) > 1})
        failures.append("duplicate modules: " + ", ".join(duplicates))
    if modules != sorted(modules):
        failures.append("rows are not sorted by module")

    for row in rows:
        derived = ".".join(Path(row["path"]).with_suffix("").parts)
        if derived != row["module"]:
            failures.append(f"{row['module']}: path {row['path']} derives {derived}")
        if not (ROOT / row["path"]).is_file():
            failures.append(f"{row['module']}: missing source {row['path']}")
        if row["baseline_state"] != "unclassified":
            failures.append(
                f"{row['module']}: baseline_state is {row['baseline_state']!r}, expected"
                " 'unclassified'"
            )

    manifest = json.loads(TIERS.read_text(encoding="utf-8"))
    classified = [
        row["module"] for row in rows if existing_tier(row["module"], manifest) is not None
    ]
    if classified:
        failures.append(
            f"{len(classified)} inventory module(s) are already classified in tiers.json: "
            + ", ".join(sorted(classified)[:8])
        )

    if exclusions is not None:
        if not exclusions.is_file():
            failures.append(f"missing exclusion list: {exclusions}")
        else:
            _, excluded_rows = me.read_tsv(exclusions)
            excluded = {row["module"] for row in excluded_rows}
            if len(excluded_rows) != EXPECTED_EXCLUSIONS:
                failures.append(
                    f"expected {EXPECTED_EXCLUSIONS} exclusion rows, found {len(excluded_rows)}"
                )
            overlap = sorted(excluded & set(modules))
            if overlap:
                failures.append("inventory overlaps the exclusion list: " + ", ".join(overlap[:8]))
            union = excluded | set(modules)
            if len(union) != EXPECTED_SNAPSHOT:
                failures.append(
                    f"inventory and exclusions cover {len(union)} modules; the authoritative "
                    f"snapshot is {EXPECTED_SNAPSHOT}"
                )
            production = {"NumStability"}
            production.update(
                ".".join(path.relative_to(ROOT).with_suffix("").parts)
                for path in (ROOT / "NumStability").rglob("*.lean")
            )
            unclassified = {
                name for name in production if existing_tier(name, manifest) is None
            }
            if unclassified != union:
                failures.append(
                    "inventory + exclusions do not equal the repository unclassified set "
                    f"(+{len(union - unclassified)} / -{len(unclassified - union)})"
                )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--exclusions",
        type=Path,
        help="optional packet CLASSIFICATION_EXCLUSIONS.tsv to prove the 386/217/603 partition",
    )
    args = parser.parse_args()
    failures = check(args.exclusions)
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    print(f"Frozen inventory verified: {EXPECTED_ROWS} modules, SHA-256 {EXPECTED_SHA256}.")
    if args.exclusions:
        print(
            f"Partition verified: {EXPECTED_ROWS} + {EXPECTED_EXCLUSIONS} = {EXPECTED_SNAPSHOT}"
            " unclassified modules, disjoint."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
