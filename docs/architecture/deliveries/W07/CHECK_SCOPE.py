#!/usr/bin/env python3
"""Audit the exact W07 worker diff against active B0011."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
BRANCH = "codex/reorg-2026-08-w07-stationary-ch17"
CHANGED_PATHS = "docs/architecture/deliveries/W07/CHANGED_PATHS.md"
EXPECTED_OWNER_BLOBS = {
    "NumStability/Algorithms/StationaryIteration.lean": "08cfea98cba754d35f7de2d620c00d0cc84300f8",
    "NumStability/Algorithms/StationaryIterationDrazin.lean": "258490a358f3991f2cc206f99c33c76033fb3c8e",
    "NumStability/Algorithms/StationaryIterationRounded.lean": "87464ba92a7339bc2560c90252f6eeb319b1376a",
    "NumStability/Algorithms/StationaryIterationSemiconvergent.lean": "38461840f7f6f4c856c1986087de86786356c0b8",
    "NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean": "5bda3a7f1f1adb2582ab6b980d78631a4541ec04",
}
FORBIDDEN_PARTS = {".lake", "benchmark-results", "__pycache__", ".codex"}
FORBIDDEN_SUFFIXES = {".olean", ".ilean", ".pyc", ".trace", ".c", ".o"}


class ScopeError(RuntimeError):
    pass


def matches(path: str, rule: dict[str, str]) -> bool:
    target = rule["path"]
    if rule["match"] == "exact":
        return path == target
    if rule["match"] == "prefix":
        return path.startswith(target)
    raise ScopeError(f"unknown B0011 path match: {rule}")


def git(repo: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if check and result.returncode:
        raise ScopeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def collect_changes(repo: Path) -> dict[str, str]:
    changes = {}
    output = git(repo, "diff", "--name-status", "--no-renames", BASE, "--")
    for line in output.splitlines():
        status, path = line.split("\t", 1)
        if status not in {"A", "M", "D"}:
            raise ScopeError(f"unsupported status {status}: {path}")
        changes[path.replace("\\", "/")] = status
    untracked = git(repo, "ls-files", "--others", "--exclude-standard", "--")
    for path in untracked.splitlines():
        changes[path.replace("\\", "/")] = "A"
    changes.setdefault(CHANGED_PATHS, "A")
    return dict(sorted(changes.items()))


def render(changes: dict[str, str]) -> str:
    counts = Counter(changes.values())
    lines = [
        "# W07 changed paths", "",
        f"Base: `{BASE}`", "",
        f"Branch: `{BRANCH}`", "",
        f"Total: **{len(changes)}** (`A` {counts['A']}, `M` {counts['M']}).", "",
        "Every path below is either an exact B0011 owner or a new file below an exact B0011 destination, test, or delivery prefix.", "",
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
    repo = args.repo_root.resolve()
    control = args.control_root.resolve()
    if repo == control:
        raise ScopeError("control and worker checkouts must be distinct")
    if git(repo, "rev-parse", f"{BASE}^{{commit}}").strip() != BASE:
        raise ScopeError("C0007 base is unavailable")
    if git(repo, "branch", "--show-current").strip() != BRANCH:
        raise ScopeError("wrong W07 branch")
    if subprocess.run(
        ["git", "-C", str(repo), "merge-base", "--is-ancestor", BASE, "HEAD"],
        check=False,
    ).returncode:
        raise ScopeError("C0007 is not an ancestor of the W07 delivery head")
    record_path = control / "docs/architecture/phases/2026-08-repository-reorganization/branches/B0011.json"
    record = json.loads(record_path.read_text(encoding="utf-8"))
    if (
        record.get("status") != "active"
        or record.get("base_checkpoint_id") != "C0007"
        or record.get("base_sha") != BASE
        or record.get("branch_name") != BRANCH
        or record.get("lane_id") != "local-lane"
        or record.get("owner_id") != "primary-human"
        or record.get("baseline_projection_id") != "P0012"
        or record.get("operator_ids") != ["codex-local"]
    ):
        raise ScopeError("active B0011 differs")
    owner_rules = record["owned_paths"]
    destination_rules = record["destination_prefixes"]
    forbidden_rules = record["forbidden_paths"]
    owners = {
        item["path"] for item in owner_rules if item.get("match") == "exact"
    }
    if owners != set(EXPECTED_OWNER_BLOBS):
        raise ScopeError("B0011 owner set differs")
    for path, expected in EXPECTED_OWNER_BLOBS.items():
        found = git(repo, "rev-parse", f"{BASE}:{path}").strip()
        if found != expected:
            raise ScopeError(f"C0007 owner blob differs for {path}: {found}")
    changes = collect_changes(repo)
    forbidden = sorted(
        path for path in changes
        if any(matches(path, rule) for rule in forbidden_rules)
    )
    if forbidden:
        raise ScopeError(f"forbidden paths changed: {forbidden}")
    for path, status in changes.items():
        parts = set(Path(path).parts)
        if parts & FORBIDDEN_PARTS or Path(path).suffix in FORBIDDEN_SUFFIXES:
            raise ScopeError(f"generated/private artifact is in scope: {path}")
        if any(matches(path, rule) for rule in owner_rules):
            if status != "M":
                raise ScopeError(f"owner must be modified, not {status}: {path}")
            continue
        if not any(matches(path, rule) for rule in destination_rules):
            raise ScopeError(f"unowned changed path: {path}")
        if status != "A":
            raise ScopeError(f"destination prefix does not authorize {status}: {path}")
        if git(repo, "cat-file", "-e", f"{BASE}:{path}", check=False) == "":
            # cat-file writes no stdout in both cases; inspect through ls-tree below.
            if git(repo, "ls-tree", "--name-only", BASE, "--", path).strip():
                raise ScopeError(f"destination file existed at C0007: {path}")
    if set(EXPECTED_OWNER_BLOBS) - set(changes):
        raise ScopeError("not every exact owner is modified")
    payload = render(changes)
    changed_path = repo / CHANGED_PATHS
    if args.write_changed_paths:
        changed_path.parent.mkdir(parents=True, exist_ok=True)
        changed_path.write_text(payload, encoding="utf-8", newline="\n")
    elif args.check_changed_paths:
        if not changed_path.is_file() or changed_path.read_text(encoding="utf-8") != payload:
            raise ScopeError("CHANGED_PATHS.md is missing or stale")
    counts = Counter(changes.values())
    print(
        f"W07 scope audit passed: {len(changes)} paths "
        f"({counts['A']} added, {counts['M']} modified), 5/5 owners, 0 forbidden"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ScopeError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
