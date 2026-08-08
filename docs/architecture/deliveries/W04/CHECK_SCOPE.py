#!/usr/bin/env python3
"""Audit the exact C0006-base-to-tree W04 path scope against active B0008."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
BRANCH = "codex/reorg-2026-08-w04-ch21-underdetermined"


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
    raise RuntimeError(f"unknown B0008 path match: {rule}")


def category(path: str, owned_paths: set[str]) -> str:
    if path in owned_paths:
        return "Modified historical owners"
    if path.startswith("NumStability/Algorithms/LinearSystems/Underdetermined/"):
        return "Added reusable underdetermined modules"
    if path.startswith("NumStability/Source/Higham/Chapter21/"):
        return "Added Chapter 21 source modules"
    if path.startswith("NumStabilityTest/Reorganization/W04/Canonical/"):
        return "Added canonical-only tests"
    if path.startswith("NumStabilityTest/Reorganization/W04/OldPath/"):
        return "Added old-path-only tests"
    if path.startswith("NumStabilityTest/Reorganization/W04/Focused/"):
        return "Added focused tests"
    if path.startswith("docs/architecture/deliveries/W04/"):
        return "Added delivery evidence"
    return "Unclassified"


def render_report(
    statuses: dict[str, str],
    owned_paths: set[str],
    forbidden_hits: list[str],
    unowned: list[str],
) -> str:
    grouped = {}
    for path in sorted(statuses):
        grouped.setdefault(category(path, owned_paths), []).append((statuses[path], path))
    preferred = [
        "Modified historical owners",
        "Added reusable underdetermined modules",
        "Added Chapter 21 source modules",
        "Added canonical-only tests",
        "Added old-path-only tests",
        "Added focused tests",
        "Added delivery evidence",
        "Unclassified",
    ]
    lines = [
        "# W04 changed paths",
        "",
        "This report is generated from the exact Git path/status inventory for",
        f"`{BASE}..DELIVERY_HEAD`. Before the delivery commit, the writer mode",
        "combines the equivalent base-to-worktree diff with untracked additions;",
        "the committed-tip checker requires the identical inventory and a clean tree.",
        "",
        "| Category | Count |",
        "| --- | ---: |",
    ]
    for name in preferred:
        if name in grouped:
            lines.append(f"| {name} | {len(grouped[name])} |")
    lines.extend([
        f"| **Total** | **{len(statuses)}** |",
        "",
        f"B0008 scope result: **{len(unowned)} unowned paths; {len(forbidden_hits)} forbidden paths**.",
        "",
        (
            "All 29 exact historical owners appear as `M`. Every `A` path is beneath "
            "one of B0008's exact destination, test, or delivery prefixes."
            if not unowned and not forbidden_hits
            else "Scope did not pass; inspect the exact discrepancies below."
        ),
    ])
    for name in preferred:
        entries = grouped.get(name)
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
        control
        / "docs/architecture/phases/2026-08-repository-reorganization/branches/B0008.json"
    ).read_text(encoding="utf-8"))
    if (
        record.get("status") != "active"
        or record.get("base_checkpoint_id") != "C0006"
        or record.get("base_sha") != BASE
        or record.get("baseline_projection_id") != "P0009"
        or record.get("branch_name") != BRANCH
        or record.get("wave_id") != "W04"
        or record.get("lane_id") != "remote-lane"
        or record.get("owner_id") != "remote-human"
        or record.get("operator_ids") != ["codex-remote"]
    ):
        raise RuntimeError("B0008 is not the expected active W04 contract")
    if git(root, "branch", "--show-current").strip() != BRANCH:
        raise RuntimeError("scope audit is not running on the W04 branch")
    if subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", BASE, "HEAD"],
        check=False,
    ).returncode:
        raise RuntimeError("C0006 W04 base is not an ancestor of HEAD")

    statuses: dict[str, str] = {}
    diff_endpoints = (BASE, "HEAD") if args.check_changed_paths else (BASE,)
    for line in git(
        root, "diff", "--name-status", "--no-renames", *diff_endpoints, "--"
    ).splitlines():
        if line.strip():
            status, path = line.split("\t", 1)
            statuses[path.replace("\\", "/")] = status
    for line in git(root, "ls-files", "--others", "--exclude-standard").splitlines():
        if line.strip():
            statuses[line.strip().replace("\\", "/")] = "A"

    report_rel = "docs/architecture/deliveries/W04/CHANGED_PATHS.md"
    if args.write_changed_paths or args.check_changed_paths:
        statuses.setdefault(report_rel, "A")
    owned = record["owned_paths"]
    destinations = record["destination_prefixes"]
    forbidden = record["forbidden_paths"]
    counts = Counter()
    unowned, forbidden_hits = [], []
    for path in sorted(statuses):
        if any(matches(path, rule) for rule in forbidden):
            forbidden_hits.append(path)
        if any(matches(path, rule) for rule in owned):
            counts["owned"] += 1
        elif any(matches(path, rule) for rule in destinations):
            counts["destination"] += 1
        else:
            counts["unowned"] += 1
            unowned.append(path)
    missing_owners = sorted(
        rule["path"] for rule in owned
        if rule["match"] == "exact" and rule["path"] not in statuses
    )
    generated_artifacts = sorted(
        path for path in statuses
        if path.startswith((".lake/", "benchmark-results/"))
        or "__pycache__" in path or path.endswith((".olean", ".ilean", ".pyc"))
    )
    ignored_w04 = git(
        root,
        "ls-files",
        "--others",
        "--ignored",
        "--exclude-standard",
        "--",
        "docs/architecture/deliveries/W04",
        "NumStabilityTest/Reorganization/W04",
    ).splitlines()
    ignored_generated_artifacts = sorted(
        path.replace("\\", "/") for path in ignored_w04
        if "__pycache__" in path
        or path.endswith((".olean", ".ilean", ".pyc"))
    )
    generated_artifacts = sorted(set(generated_artifacts + ignored_generated_artifacts))
    bad_owned_statuses = sorted(
        f"{path}:{statuses.get(path, 'missing')}"
        for path in (rule["path"] for rule in owned if rule["match"] == "exact")
        if statuses.get(path) != "M"
    )
    bad_destination_statuses = sorted(
        f"{path}:{status}" for path, status in statuses.items()
        if any(matches(path, rule) for rule in destinations) and status != "A"
    )
    protected = "NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean"
    if protected in statuses:
        forbidden_hits.append(protected)
    dirty_paths = []
    if args.check_changed_paths:
        dirty_paths = [line for line in git(root, "status", "--short").splitlines() if line]
    result = {
        "base": BASE,
        "delivery_head": git(root, "rev-parse", "HEAD").strip(),
        "branch": BRANCH,
        "changed_paths": len(statuses),
        "owned_paths": counts["owned"],
        "destination_paths": counts["destination"],
        "categories": dict(Counter(category(path, {rule['path'] for rule in owned if rule['match'] == 'exact'}) for path in statuses)),
        "missing_owned_paths": missing_owners,
        "unowned_paths": unowned,
        "forbidden_paths": sorted(set(forbidden_hits)),
        "generated_artifacts": generated_artifacts,
        "bad_owned_statuses": bad_owned_statuses,
        "bad_destination_statuses": bad_destination_statuses,
        "dirty_paths": dirty_paths,
    }
    if args.write_changed_paths or args.check_changed_paths:
        owned_set = {rule["path"] for rule in owned if rule["match"] == "exact"}
        rendered = render_report(statuses, owned_set, sorted(set(forbidden_hits)), unowned)
        report_path = root / report_rel
        if args.check_changed_paths:
            if not report_path.is_file() or report_path.read_text(encoding="utf-8") != rendered:
                raise RuntimeError("CHANGED_PATHS.md is missing or stale")
        else:
            report_path.write_text(rendered, encoding="utf-8", newline="\n")
    print(json.dumps(result, indent=2))
    failures = (
        missing_owners or unowned or forbidden_hits or generated_artifacts
        or bad_owned_statuses or bad_destination_statuses or dirty_paths
        or counts["owned"] != 29
    )
    return 1 if failures else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
