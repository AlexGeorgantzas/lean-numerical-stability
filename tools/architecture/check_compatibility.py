#!/usr/bin/env python3
"""Verify the documented old-to-new Lean module forwarding contract."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

from generate_baseline import IMPORT_RE, module_name, remove_lean_comments, source_paths


ROOT = Path(__file__).resolve().parents[2]
POLICY = ROOT / "docs" / "architecture" / "COMPATIBILITY.md"
IMPORT_LINE_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+[^\r\n]+(?:\r?\n|$)"
)

# R11 preserves Chapter19.Core byte-for-byte as a reviewed source outlier. Its
# two support imports became historical paths in the same integration. Keep the
# exception exact and fail when either edge disappears so the allowance cannot
# silently broaden or outlive the retained outlier.
RETAINED_PRODUCTION_IMPORT_EXCEPTIONS = frozenset(
    {
        (
            "NumStability.Source.Higham.Chapter19.Core",
            "NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport",
        ),
        (
            "NumStability.Source.Higham.Chapter19.Core",
            "NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport",
        ),
    }
)
RETAINED_PRODUCTION_SOURCE_SHA256 = {
    "NumStability.Source.Higham.Chapter19.Core": (
        "8599A1F13F1A241EFE90BB1059D98C09A4419BE4C2202B97F45DEC69189B3FE3"
    ),
}


def module_path(name: str) -> Path:
    return ROOT / Path(*name.split(".")).with_suffix(".lean")


def documented_mappings() -> dict[str, tuple[str, ...]]:
    mappings: dict[str, tuple[str, ...]] = {}
    for line in POLICY.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        names = re.findall(r"`(NumStability(?:\.[A-Za-z0-9_']+)+)`", line)
        if len(names) < 2:
            continue
        historical, *canonical = names
        if historical in mappings:
            raise ValueError(f"duplicate compatibility row: {historical}")
        mappings[historical] = tuple(canonical)
    if not mappings:
        raise ValueError(f"no compatibility mappings found in {POLICY}")
    return mappings


def retained_production_import_failures(
    historical_names: set[str],
    production_import_edges: set[tuple[str, str]],
    production_source_sha256: dict[str, str | None],
) -> list[str]:
    failures: list[str] = []
    invalid_exception_targets = sorted(
        target
        for _, target in RETAINED_PRODUCTION_IMPORT_EXCEPTIONS
        if target not in historical_names
    )
    if invalid_exception_targets:
        failures.append(
            "production-import exceptions target paths absent from compatibility table: "
            + ", ".join(invalid_exception_targets)
        )

    exception_sources = {
        source for source, _ in RETAINED_PRODUCTION_IMPORT_EXCEPTIONS
    }
    if exception_sources != set(RETAINED_PRODUCTION_SOURCE_SHA256):
        failures.append(
            "production-import exception sources do not match frozen source pins: "
            f"exceptions={sorted(exception_sources)!r}, "
            f"pins={sorted(RETAINED_PRODUCTION_SOURCE_SHA256)!r}"
        )
    for name, expected_sha256 in sorted(RETAINED_PRODUCTION_SOURCE_SHA256.items()):
        actual_sha256 = production_source_sha256.get(name)
        if actual_sha256 is None:
            failures.append(f"missing retained production source: {name}")
        elif actual_sha256 != expected_sha256:
            failures.append(
                f"{name}: retained source SHA-256 {actual_sha256}, "
                f"expected {expected_sha256}"
            )

    seen_exceptions = production_import_edges & RETAINED_PRODUCTION_IMPORT_EXCEPTIONS
    for name, target in sorted(production_import_edges - seen_exceptions):
        failures.append(f"{name}: production import uses historical path {target}")
    for name, target in sorted(
        RETAINED_PRODUCTION_IMPORT_EXCEPTIONS - seen_exceptions
    ):
        failures.append(f"stale production-import exception: {name} -> {target}")
    return failures


def self_test_retained_production_imports() -> None:
    historical_names = {
        target for _, target in RETAINED_PRODUCTION_IMPORT_EXCEPTIONS
    }
    valid_edges = set(RETAINED_PRODUCTION_IMPORT_EXCEPTIONS)
    valid_digests = dict(RETAINED_PRODUCTION_SOURCE_SHA256)
    assert not retained_production_import_failures(
        historical_names, valid_edges, valid_digests
    )

    missing_edge = min(valid_edges)
    missing_edge_failures = retained_production_import_failures(
        historical_names, valid_edges - {missing_edge}, valid_digests
    )
    assert any(
        "stale production-import exception" in item
        for item in missing_edge_failures
    )

    broadened_failures = retained_production_import_failures(
        historical_names,
        valid_edges
        | {
            (
                "NumStability.Source.Higham.Chapter19.Unreviewed",
                min(historical_names),
            )
        },
        valid_digests,
    )
    assert any(
        "production import uses historical path" in item
        for item in broadened_failures
    )

    changed_source_failures = retained_production_import_failures(
        historical_names,
        valid_edges,
        {name: "0" * 64 for name in valid_digests},
    )
    assert any("retained source SHA-256" in item for item in changed_source_failures)


def main() -> int:
    try:
        self_test_retained_production_imports()
    except AssertionError as error:
        print(f"error: compatibility checker self-test failed: {error}", file=sys.stderr)
        return 2

    try:
        mappings = documented_mappings()
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    failures: list[str] = []
    tier_manifest_path = ROOT / "docs" / "architecture" / "tiers.json"
    try:
        tier_manifest = json.loads(tier_manifest_path.read_text(encoding="utf-8"))
        tier_compatibility = {
            name
            for name, tier in tier_manifest.get("exact", {}).items()
            if tier == "compatibility"
        }
        if tier_compatibility != set(mappings):
            missing = sorted(tier_compatibility - set(mappings))
            extra = sorted(set(mappings) - tier_compatibility)
            if missing:
                failures.append(
                    "compatibility-tier modules absent from table: " + ", ".join(missing)
                )
            if extra:
                failures.append(
                    "tabled historical modules not in compatibility tier: "
                    + ", ".join(extra)
                )
    except (OSError, json.JSONDecodeError, AttributeError) as error:
        failures.append(f"cannot read tier manifest {tier_manifest_path}: {error}")

    for historical, canonical in sorted(mappings.items()):
        old_path = module_path(historical)
        if not old_path.is_file():
            failures.append(f"missing historical module: {historical}")
            continue
        for target in canonical:
            if not module_path(target).is_file():
                failures.append(f"missing canonical module: {target}")

        text = old_path.read_text(encoding="utf-8-sig", errors="replace")
        uncommented = remove_lean_comments(text)
        imports = tuple(
            target
            for target in IMPORT_RE.findall(uncommented)
            if target.startswith("NumStability.")
        )
        if imports != canonical:
            failures.append(
                f"{historical}: imports {imports!r}, documented {canonical!r}"
            )
        remaining = IMPORT_LINE_RE.sub("", uncommented).strip()
        if remaining:
            failures.append(f"{historical}: forwarding module contains Lean code")

    historical_names = set(mappings)
    production_source_sha256: dict[str, str | None] = {}
    for name in sorted(RETAINED_PRODUCTION_SOURCE_SHA256):
        path = module_path(name)
        production_source_sha256[name] = (
            hashlib.sha256(path.read_bytes()).hexdigest().upper()
            if path.is_file()
            else None
        )

    production_import_edges: set[tuple[str, str]] = set()
    for path in source_paths(ROOT):
        name = module_name(path.relative_to(ROOT))
        if name in historical_names:
            continue
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        for target in IMPORT_RE.findall(remove_lean_comments(text)):
            if target in historical_names:
                production_import_edges.add((name, target))
    failures.extend(
        retained_production_import_failures(
            historical_names,
            production_import_edges,
            production_source_sha256,
        )
    )

    test_imports: set[str] = set()
    test_paths = [ROOT / "NumStabilityTest.lean"]
    test_paths.extend(sorted((ROOT / "NumStabilityTest").rglob("*.lean")))
    for path in test_paths:
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        test_imports.update(IMPORT_RE.findall(remove_lean_comments(text)))
    canonical_names = {target for targets in mappings.values() for target in targets}
    missing_historical_tests = sorted(historical_names - test_imports)
    missing_canonical_tests = sorted(canonical_names - test_imports)
    if missing_historical_tests:
        failures.append(
            "historical paths without a direct test import: "
            + ", ".join(missing_historical_tests)
        )
    if missing_canonical_tests:
        failures.append(
            "canonical targets without a direct test import: "
            + ", ".join(missing_canonical_tests)
        )

    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1
    target_count = sum(len(targets) for targets in mappings.values())
    print(
        f"compatibility contract passed: {len(mappings)} forwarding modules, "
        f"{target_count} canonical targets, "
        f"{len(production_import_edges & RETAINED_PRODUCTION_IMPORT_EXCEPTIONS)} "
        "retained production-import exceptions"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
