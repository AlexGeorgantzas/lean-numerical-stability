#!/usr/bin/env python3
"""Audit the exact W10 worker diff against active B0012."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
BRANCH = "codex/reorg-2026-08-w10-norm-estimation-ch15"
EVIDENCE = "docs/architecture/deliveries/W10/"
CHANGED_PATHS = EVIDENCE + "CHANGED_PATHS.md"
EXPECTED = {"paths": 274, "A": 247, "M": 27, "production": 123, "tests": 135, "evidence": 16}
FORBIDDEN_PARTS = {".lake", "benchmark-results", "__pycache__", ".codex"}
FORBIDDEN_SUFFIXES = {".olean", ".ilean", ".pyc", ".trace", ".c", ".o"}


class ScopeError(RuntimeError):
    pass


def git(repo: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if check and result.returncode:
        raise ScopeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def matches(path: str, rule: dict[str, str]) -> bool:
    if rule["match"] == "exact":
        return path == rule["path"]
    if rule["match"] == "prefix":
        return path.startswith(rule["path"])
    raise ScopeError(f"unknown B0012 match rule: {rule}")


def collect(repo: Path) -> dict[str, str]:
    changes: dict[str, str] = {}
    for line in git(repo, "diff", "--name-status", "--no-renames", BASE, "--").splitlines():
        status, path = line.split("\t", 1)
        if status not in {"A", "M", "D"}:
            raise ScopeError(f"unsupported status {status}: {path}")
        changes[path.replace("\\", "/")] = status
    for path in git(repo, "ls-files", "--others", "--exclude-standard", "--").splitlines():
        changes[path.replace("\\", "/")] = "A"
    changes.setdefault(CHANGED_PATHS, "A")
    return dict(sorted(changes.items()))


def render(changes: dict[str, str]) -> str:
    counts = Counter(changes.values())
    production = sum(path.startswith("NumStability/") for path in changes)
    tests = sum(path.startswith("NumStabilityTest/Reorganization/W10/") for path in changes)
    evidence = sum(path.startswith(EVIDENCE) for path in changes)
    lines = [
        "# W10 changed paths", "", f"Base: `{BASE}`", "", f"Branch: `{BRANCH}`", "",
        f"Total: **{len(changes)}** (`A` {counts['A']}, `M` {counts['M']}).", "",
        f"The exact delivery contains **{production} production paths** (27 modified owners and 96 new canonical modules), **{tests} test modules**, "
        f"and **{evidence} evidence artifacts**. Every path is an exact B0012 owner or lies below "
        "an authorized B0012 destination, test, or delivery prefix.", "",
        "No integrator-owned aggregate, tier, layout, phase-control, CI, or accepted-consumer path is in this diff.", "",
        "## Exact path ledger", "",
    ]
    lines.extend(f"- `{status}` `{path}`" for path, status in changes.items())
    return "\n".join(lines) + "\n"


def main() -> int:
    script = Path(__file__).resolve()
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=script.parents[4])
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--write-changed-paths", action="store_true")
    parser.add_argument("--check-changed-paths", action="store_true")
    args = parser.parse_args()
    if args.write_changed_paths and args.check_changed_paths:
        raise ScopeError("choose only one CHANGED_PATHS mode")
    repo, control = args.repo_root.resolve(), args.control_root.resolve()
    if repo == control or git(repo, "branch", "--show-current").strip() != BRANCH:
        raise ScopeError("wrong worker/control checkout")
    if subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", BASE, "HEAD"]).returncode:
        raise ScopeError("C0007 is not an ancestor")
    record = json.loads((control / "docs/architecture/phases/2026-08-repository-reorganization/branches/B0012.json").read_text())
    required = {
        "status": "active", "branch_id": "B0012", "wave_id": "W10",
        "base_checkpoint_id": "C0007", "base_sha": BASE, "branch_name": BRANCH,
        "lane_id": "remote-lane", "owner_id": "remote-human", "baseline_projection_id": "P0013",
    }
    for key, value in required.items():
        if record.get(key) != value:
            raise ScopeError(f"B0012 field differs: {key}")
    if record.get("operator_ids") != ["claude-remote"]:
        raise ScopeError("B0012 operator differs")
    owners, destinations, forbidden = record["owned_paths"], record["destination_prefixes"], record["forbidden_paths"]
    if len(owners) != 27 or len(destinations) != 45:
        raise ScopeError("B0012 owner/destination roster differs")
    changes = collect(repo)
    base_paths = set(git(repo, "ls-tree", "-r", "--name-only", BASE).splitlines())
    for path, status in changes.items():
        if set(Path(path).parts) & FORBIDDEN_PARTS or Path(path).suffix in FORBIDDEN_SUFFIXES:
            raise ScopeError(f"generated/private artifact in scope: {path}")
        if any(matches(path, rule) for rule in forbidden):
            raise ScopeError(f"forbidden path changed: {path}")
        if any(matches(path, rule) for rule in owners):
            if status != "M":
                raise ScopeError(f"owner is not modified: {path}")
        elif any(matches(path, rule) for rule in destinations):
            if status != "A" or path in base_paths:
                raise ScopeError(f"destination is not vacant/add-only: {path}")
        else:
            raise ScopeError(f"unowned changed path: {path}")
    owner_paths = {rule["path"] for rule in owners if rule["match"] == "exact"}
    if owner_paths != {p for p, s in changes.items() if s == "M"}:
        raise ScopeError("modified paths are not exactly the 27 owners")
    counts = Counter(changes.values())
    actual = {
        "paths": len(changes), "A": counts["A"], "M": counts["M"],
        "production": sum(p.startswith("NumStability/") for p in changes),
        "tests": sum(p.startswith("NumStabilityTest/Reorganization/W10/") for p in changes),
        "evidence": sum(p.startswith(EVIDENCE) for p in changes),
    }
    if actual != EXPECTED:
        raise ScopeError(f"scope counts differ: {actual} != {EXPECTED}")
    payload = render(changes)
    path = repo / CHANGED_PATHS
    if args.write_changed_paths:
        path.write_text(payload, encoding="utf-8", newline="\n")
    elif args.check_changed_paths and path.read_text(encoding="utf-8") != payload:
        raise ScopeError("CHANGED_PATHS.md is stale")
    print("W10 scope audit passed: 274 paths (247 added, 27 modified), 27/27 owners, 0 forbidden")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ScopeError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
