#!/usr/bin/env python3
"""Audit the exact C0006-base-to-tree W11 path scope against active B0010."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
BRANCH = "codex/reorg-2026-08-w11-randnla"


def git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    return result.stdout


def matches(path: str, rule: dict[str, str]) -> bool:
    target = rule["path"]
    if rule["match"] == "exact":
        return path == target
    if rule["match"] == "prefix":
        return path.startswith(target)
    raise RuntimeError(f"unknown B0010 path match: {rule}")


def category(path: str, owners: set[str]) -> str:
    if path in owners:
        return "Modified historical owners"
    if path.startswith("NumStability/Algorithms/RandomizedLinearAlgebra/"):
        return "Added reusable RandNLA modules"
    if path.startswith("NumStability/Source/DrineasMahoney/RandNLA2016/"):
        return "Added reviewed source modules"
    if path.startswith("NumStabilityTest/Reorganization/W11/Canonical/"):
        return "Added canonical-only tests"
    if path.startswith("NumStabilityTest/Reorganization/W11/OldPath/"):
        return "Added old-path-only tests"
    if path.startswith("NumStabilityTest/Reorganization/W11/Focused/"):
        return "Added focused tests"
    if path.startswith("docs/architecture/deliveries/W11/"):
        return "Added delivery evidence"
    return "Unclassified"


def render_report(statuses: dict[str, str], owners: set[str], unowned: list[str], forbidden: list[str]) -> str:
    groups: dict[str, list[tuple[str, str]]] = {}
    for path in sorted(statuses):
        groups.setdefault(category(path, owners), []).append((statuses[path], path))
    order = [
        "Modified historical owners",
        "Added reusable RandNLA modules",
        "Added reviewed source modules",
        "Added canonical-only tests",
        "Added old-path-only tests",
        "Added focused tests",
        "Added delivery evidence",
        "Unclassified",
    ]
    lines = [
        "# W11 changed paths",
        "",
        "This report is generated from the exact Git inventory",
        f"`{BASE}..DELIVERY_HEAD`. Before the delivery commit, untracked",
        "worker files are classified as additions; the committed-tip replay must",
        "produce the same path/status inventory.",
        "",
        "| Category | Count |",
        "| --- | ---: |",
    ]
    for name in order:
        if name in groups:
            lines.append(f"| {name} | {len(groups[name])} |")
    lines.extend([
        f"| **Total** | **{len(statuses)}** |",
        "",
        f"B0010 scope result: **{len(unowned)} unowned paths; {len(forbidden)} forbidden paths**.",
        "",
        "All 18 exact historical owners appear as `M`. Every `A` path is below",
        "one of B0010's reviewed destination, W11-test, or delivery-evidence prefixes.",
    ])
    for name in order:
        entries = groups.get(name)
        if not entries:
            continue
        lines.extend(["", f"## {name} ({len(entries)})", ""])
        lines.extend(f"- `{status}` `{path}`" for status, path in entries)
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write-changed-paths", action="store_true")
    mode.add_argument("--check-changed-paths", action="store_true")
    args = parser.parse_args()
    root = args.repo_root.resolve()
    control = args.control_root.resolve()
    record = json.loads((
        control / "docs/architecture/phases/2026-08-repository-reorganization/branches/B0010.json"
    ).read_text(encoding="utf-8"))
    if (
        record.get("status") != "active"
        or record.get("base_checkpoint_id") != "C0006"
        or record.get("base_sha") != BASE
        or record.get("branch_name") != BRANCH
        or record.get("operator_ids") != ["codex-local"]
    ):
        raise RuntimeError("B0010 is not the expected active W11 contract")
    if git(root, "branch", "--show-current").strip() != BRANCH:
        raise RuntimeError("scope audit is not running on the W11 branch")
    if subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", BASE, "HEAD"],
        check=False,
    ).returncode:
        raise RuntimeError("C0006 W11 base is not an ancestor of HEAD")

    statuses: dict[str, str] = {}
    for line in git(root, "diff", "--name-status", "--no-renames", BASE, "--").splitlines():
        if line.strip():
            status, path = line.split("\t", 1)
            statuses[path.replace("\\", "/")] = status
    for line in git(root, "ls-files", "--others", "--exclude-standard").splitlines():
        if line.strip():
            statuses[line.strip().replace("\\", "/")] = "A"

    report_rel = "docs/architecture/deliveries/W11/CHANGED_PATHS.md"
    if args.write_changed_paths or args.check_changed_paths:
        statuses.setdefault(report_rel, "A")
    owners = record["owned_paths"]
    destinations = record["destination_prefixes"]
    forbidden_rules = record["forbidden_paths"]
    counts = Counter()
    unowned: list[str] = []
    forbidden_hits: list[str] = []
    for path in sorted(statuses):
        if any(matches(path, rule) for rule in forbidden_rules):
            forbidden_hits.append(path)
        if any(matches(path, rule) for rule in owners):
            counts["owned"] += 1
        elif any(matches(path, rule) for rule in destinations):
            counts["destination"] += 1
        else:
            counts["unowned"] += 1
            unowned.append(path)

    exact_owners = [rule["path"] for rule in owners if rule["match"] == "exact"]
    missing = sorted(path for path in exact_owners if path not in statuses)
    bad_owned = sorted(f"{path}:{statuses.get(path, 'missing')}" for path in exact_owners if statuses.get(path) != "M")
    bad_destination = sorted(
        f"{path}:{status}" for path, status in statuses.items()
        if any(matches(path, rule) for rule in destinations) and status != "A"
    )
    generated = sorted(
        path for path in statuses
        if path.startswith((".lake/", "benchmark-results/"))
        or "__pycache__" in path or path.endswith((".olean", ".ilean", ".pyc"))
    )
    result = {
        "base": BASE,
        "branch": BRANCH,
        "changed_paths": len(statuses),
        "owned_paths": counts["owned"],
        "destination_paths": counts["destination"],
        "missing_owned_paths": missing,
        "unowned_paths": unowned,
        "forbidden_paths": forbidden_hits,
        "generated_artifacts": generated,
        "bad_owned_statuses": bad_owned,
        "bad_destination_statuses": bad_destination,
    }
    if args.write_changed_paths or args.check_changed_paths:
        rendered = render_report(statuses, set(exact_owners), unowned, forbidden_hits)
        path = root / report_rel
        if args.check_changed_paths:
            if not path.is_file() or path.read_text(encoding="utf-8") != rendered:
                raise RuntimeError("CHANGED_PATHS.md is missing or stale")
        else:
            path.write_text(rendered, encoding="utf-8", newline="\n")
    print(json.dumps(result, indent=2))
    return 1 if any((
        missing, unowned, forbidden_hits, generated, bad_owned, bad_destination,
        counts["owned"] != 18,
    )) else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
