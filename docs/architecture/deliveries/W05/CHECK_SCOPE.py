#!/usr/bin/env python3
"""Audit the exact base-to-tree W05 path scope against B0005."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "b56f609f3bf66b5d7d0b677567cce82fee0c275b"
BRANCH = "codex/reorg-2026-08-w05-ch16-ch18"


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
    raise RuntimeError(f"unknown B0005 path match: {rule}")


def category(path: str, owned_paths: set[str]) -> str:
    if path in owned_paths:
        return "Modified historical owners"
    if path.startswith("NumStability/Algorithms/MatrixEquations/"):
        return "Added reusable Sylvester modules"
    if path.startswith("NumStability/Analysis/LinearOperators/Schur/"):
        return "Added reusable Schur modules"
    if path.startswith("NumStability/Analysis/SingularValues/InverseBounds/"):
        return "Added reusable inverse-bound modules"
    if path.startswith("NumStability/Source/Higham/"):
        return "Added source-numbered modules"
    if path.startswith("NumStabilityTest/Reorganization/W05/Canonical/"):
        return "Added canonical-only tests"
    if path.startswith("NumStabilityTest/Reorganization/W05/Compatibility/"):
        return "Added old-path-only tests"
    if path.startswith("NumStabilityTest/Reorganization/W05/Focused/"):
        return "Added focused tests"
    if path.startswith("docs/architecture/deliveries/W05/"):
        return "Added delivery evidence"
    return "Unclassified"


def render_report(
    *,
    statuses: dict[str, str],
    owned_paths: set[str],
    forbidden_hits: list[str],
    unowned: list[str],
) -> str:
    grouped: dict[str, list[tuple[str, str]]] = {}
    for path in sorted(statuses):
        grouped.setdefault(category(path, owned_paths), []).append((statuses[path], path))
    lines = [
        "# W05 changed paths",
        "",
        "This file is generated from the exact Git diff from the frozen C0004 base",
        f"`{BASE}` to the W05 delivery tree. Untracked delivery files are treated as",
        "additions before the delivery commit; rerunning the generator on the committed",
        "tip yields the same path/status inventory.",
        "",
        "| Category | Count |",
        "| --- | ---: |",
    ]
    preferred = [
        "Modified historical owners",
        "Added reusable Sylvester modules",
        "Added reusable Schur modules",
        "Added reusable inverse-bound modules",
        "Added source-numbered modules",
        "Added canonical-only tests",
        "Added old-path-only tests",
        "Added focused tests",
        "Added delivery evidence",
        "Unclassified",
    ]
    for name in preferred:
        if name in grouped:
            lines.append(f"| {name} | {len(grouped[name])} |")
    lines.extend([
        f"| **Total** | **{len(statuses)}** |",
        "",
        f"B0005 scope result: **{len(unowned)} unowned paths; "
        f"{len(forbidden_hits)} forbidden paths**.",
        "",
        "There are no deletions or renames. `M` denotes one of B0005's exact historical",
        "owners; `A` denotes a path below an authorized destination prefix.",
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
    parser.add_argument(
        "--write-changed-paths",
        action="store_true",
        help="write CHANGED_PATHS.md from the exact base-to-tree Git inventory",
    )
    args = parser.parse_args()
    root = args.repo_root.resolve()
    control = args.control_root.resolve()
    record = json.loads((
        control
        / "docs/architecture/phases/2026-08-repository-reorganization/branches/B0005.json"
    ).read_text(encoding="utf-8"))
    if (
        record.get("status") != "active"
        or record.get("base_sha") != BASE
        or record.get("branch_name") != BRANCH
        or record.get("operator_ids") != ["codex-local"]
    ):
        raise RuntimeError("B0005 is not the expected active W05 contract")
    if git(root, "branch", "--show-current").strip() != BRANCH:
        raise RuntimeError("scope audit is not running on the W05 branch")
    ancestor = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", BASE, "HEAD"],
        check=False,
    )
    if ancestor.returncode:
        raise RuntimeError("C0004 W05 base is not an ancestor of HEAD")

    statuses: dict[str, str] = {}
    for line in git(root, "diff", "--name-status", "--no-renames", BASE, "--").splitlines():
        if not line.strip():
            continue
        status, path = line.split("\t", 1)
        statuses[path.replace("\\", "/")] = status
    untracked = {
        line.strip().replace("\\", "/")
        for line in git(root, "ls-files", "--others", "--exclude-standard").splitlines()
        if line.strip()
    }
    for path in untracked:
        statuses[path] = "A"
    paths = sorted(statuses)
    owned = record["owned_paths"]
    destinations = record["destination_prefixes"]
    forbidden = record["forbidden_paths"]
    counts = Counter()
    unowned = []
    forbidden_hits = []
    for path in paths:
        if any(matches(path, rule) for rule in forbidden):
            forbidden_hits.append(path)
        if any(matches(path, rule) for rule in owned):
            counts["owned"] += 1
        elif any(matches(path, rule) for rule in destinations):
            counts["destination"] += 1
        else:
            counts["unowned"] += 1
            unowned.append(path)
    result = {
        "base": BASE,
        "branch": BRANCH,
        "changed_paths": len(paths),
        "owned_paths": counts["owned"],
        "destination_paths": counts["destination"],
        "unowned_paths": unowned,
        "forbidden_paths": forbidden_hits,
    }
    if args.write_changed_paths:
        report_path = root / "docs/architecture/deliveries/W05/CHANGED_PATHS.md"
        # Include the report itself in its own exact inventory before rendering it.
        report_rel = report_path.relative_to(root).as_posix()
        if report_rel not in statuses:
            statuses[report_rel] = "A"
            paths = sorted(statuses)
            counts = Counter()
            unowned = []
            forbidden_hits = []
            for path in paths:
                if any(matches(path, rule) for rule in forbidden):
                    forbidden_hits.append(path)
                if any(matches(path, rule) for rule in owned):
                    counts["owned"] += 1
                elif any(matches(path, rule) for rule in destinations):
                    counts["destination"] += 1
                else:
                    counts["unowned"] += 1
                    unowned.append(path)
            result.update({
                "changed_paths": len(paths),
                "owned_paths": counts["owned"],
                "destination_paths": counts["destination"],
                "unowned_paths": unowned,
                "forbidden_paths": forbidden_hits,
            })
        owned_set = {rule["path"] for rule in owned if rule["match"] == "exact"}
        report_path.write_text(
            render_report(
                statuses=statuses,
                owned_paths=owned_set,
                forbidden_hits=forbidden_hits,
                unowned=unowned,
            ),
            encoding="utf-8",
            newline="\n",
        )
    print(json.dumps(result, indent=2))
    return 1 if unowned or forbidden_hits else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
