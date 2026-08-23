#!/usr/bin/env python3
"""Fail-closed scope checker for the immutable R07 worker delivery."""

from __future__ import annotations

import csv
import hashlib
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "ad92bbfae62d538f3e52829a269a846688a8e213"
CONTROL_HEAD = "35cb1a7c5f136f291398dddd99d8012dcf38f967"
BRANCH_NAME = "codex/reorg-completion-2026-08-r07-matrix-functions-powers-ch18"
B0010_SHA256 = "007CD9A2CF7A886B0789CCD0BE3CCF42A35EFC2D310B8EA3C1A20177C21231D2"
PHASE = Path("docs/architecture/phases/2026-08-repository-reorganization-completion")
B0010 = PHASE / "branches" / "B0010.json"
DELIVERY = Path("docs/architecture/deliveries/R07")
EVIDENCE = {
    "MATERIALIZATION.json", "auditors/materialize_worker.py",
    "auditors/generate_evidence.py", "CHECK_SCOPE.py", "CHECK_STATIC.py",
    "CHECK_PROJECTION.py", "CHECK_REQUEST_REPLAY.py", "DECLARATION_ROUTES.tsv",
    "PRIVATE_CLOSURE.tsv", "PRIVATE_NORMALIZATION.tsv", "REALIZED_IMPORTS.tsv",
    "RETENTION.tsv", "TEST_MATRIX.tsv", "CHANGED_PATHS.md", "DELIVERY.md",
    "GATE_RESULTS.tsv", "INTEGRATOR_REQUESTS.md", "PRIVATE_CLOSURE.md",
    "PROJECTION.md", "ROUTING.md", "R0011-CORRECTION.patch",
}


def run(root: Path, *args: str, binary: bool = False) -> str | bytes:
    result = subprocess.run(
        list(args), cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        check=True, text=not binary,
    )
    return result.stdout


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def collect_changes(repo: Path) -> tuple[dict[str, str], list[str]]:
    problems: list[str] = []
    result: dict[str, str] = {}
    raw = run(repo, "git", "diff", "--name-status", "--no-renames", BASE)
    for line in raw.splitlines():
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != 2:
            problems.append(f"unparseable diff row: {line}")
            continue
        status, path = fields
        result[path.replace("\\", "/")] = status
    raw = run(repo, "git", "ls-files", "--others", "--exclude-standard")
    for path in raw.splitlines():
        normalized = path.replace("\\", "/")
        if normalized in result:
            problems.append(f"path appears both tracked and untracked: {normalized}")
        result[normalized] = "A"
    return result, problems


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: CHECK_SCOPE.py CONTROL_ROOT", file=sys.stderr)
        return 2
    repo = Path(__file__).resolve().parents[4]
    control = Path(sys.argv[1]).resolve()
    problems: list[str] = []

    try:
        control_head = run(control, "git", "rev-parse", "HEAD").strip()
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"cannot inspect control checkout: {error}", file=sys.stderr)
        return 2
    if control_head != CONTROL_HEAD:
        problems.append(f"control HEAD {control_head}, expected {CONTROL_HEAD}")
    record_path = control / B0010
    if not record_path.is_file() or sha(record_path) != B0010_SHA256:
        problems.append("activated B0010.json is missing or has the wrong hash")
        record = {}
    else:
        record = json.loads(record_path.read_text(encoding="utf-8"))
    refresh = record.get("refresh", {}).get("evidence", [])
    if len(refresh) != 61:
        problems.append(f"B0010 refresh evidence rows={len(refresh)}, expected 61")
    for item in refresh:
        artifact = control / item["path"]
        actual = sha(artifact) if artifact.is_file() else "MISSING"
        if actual != item["sha256"]:
            problems.append(f"control evidence mismatch {item['path']}: {actual}")

    head = run(repo, "git", "rev-parse", "HEAD").strip()
    parents = run(repo, "git", "show", "-s", "--format=%P", "HEAD").strip().split()
    if head != BASE and parents != [BASE]:
        problems.append(f"worker HEAD {head} is neither exact base nor its single-parent delivery child")
    branch = run(repo, "git", "branch", "--show-current").strip()
    if branch != BRANCH_NAME:
        problems.append(f"worker branch {branch!r}, expected {BRANCH_NAME!r}")

    changes, change_problems = collect_changes(repo)
    problems.extend(change_problems)
    invalid_status = {path: status for path, status in changes.items() if status not in {"A", "M"}}
    for path, status in sorted(invalid_status.items()):
        problems.append(f"destructive/unexpected status {status}: {path}")

    branches = control / PHASE / "branches"
    module_routes = rows(branches / "B0010-module-routes.tsv")
    owners = {row["path"] for row in module_routes}
    rewritten = {row["path"] for row in module_routes if int(row["declaration_count"]) > 0}
    unchanged = owners - rewritten
    destinations = {
        row["module"].replace(".", "/") + ".lean"
        for row in rows(branches / "B0010-destinations.tsv")
    }
    tests = {row["target"] for row in rows(branches / "B0010-test-plan.tsv")}
    evidence = {(DELIVERY / path).as_posix() for path in EVIDENCE}
    expected = rewritten | destinations | tests | evidence

    actual = set(changes)
    for path in sorted(actual - expected):
        problems.append(f"out-of-scope changed path: {path}")
    for path in sorted(expected - actual):
        problems.append(f"expected delivery path is absent from diff: {path}")
    for path in sorted(rewritten):
        if changes.get(path) != "M":
            problems.append(f"rewritten historical owner must be M: {path} ({changes.get(path)})")
    for path in sorted(destinations | tests | evidence):
        if changes.get(path) != "A":
            problems.append(f"new delivery path must be A: {path} ({changes.get(path)})")

    for path in sorted(unchanged):
        current = repo / path
        if not current.is_file():
            problems.append(f"byte-retained historical owner is missing: {path}")
            continue
        base_bytes = run(repo, "git", "show", f"{BASE}:{path}", binary=True)
        if current.read_bytes() != base_bytes:
            problems.append(f"zero-declaration owner differs from exact C0005: {path}")

    request_paths = set((branches / "B0010-shared-request-paths.txt").read_text(encoding="utf-8").splitlines())
    for path in sorted(actual & request_paths):
        problems.append(f"worker edited integrator-owned R0011 path: {path}")
    forbidden = {item["path"] for item in record.get("forbidden_paths", [])}
    for path in sorted(actual & forbidden):
        problems.append(f"worker edited frozen/forbidden path: {path}")

    base_paths = set(run(repo, "git", "ls-tree", "-r", "--name-only", BASE).splitlines())
    base_casefold = {path.casefold(): path for path in base_paths}
    for path in sorted(destinations):
        if path.casefold() in base_casefold:
            problems.append(f"destination not casefold-vacant at base: {path} vs {base_casefold[path.casefold()]}")

    counts = Counter(changes.values())
    group_counts = Counter()
    for path in actual:
        if path.startswith("NumStabilityTest/Reorganization/R07/"):
            group_counts["tests"] += 1
        elif path.startswith(DELIVERY.as_posix() + "/"):
            group_counts["evidence"] += 1
        elif path.startswith("NumStability/"):
            group_counts["production"] += 1
        else:
            group_counts["outside"] += 1
    expected_counts = Counter({"M": 13, "A": 153})
    expected_groups = Counter({"production": 43, "tests": 102, "evidence": 21})
    if len(actual) != 166 or counts != expected_counts:
        problems.append(f"changed-set shape paths={len(actual)}, statuses={dict(counts)}")
    if group_counts != expected_groups:
        problems.append(f"changed-set groups={dict(group_counts)}, expected={dict(expected_groups)}")

    delivery_dir = repo / DELIVERY
    allowed_files = {str((delivery_dir / path).resolve()).casefold() for path in EVIDENCE}
    if delivery_dir.is_dir():
        for artifact in delivery_dir.rglob("*"):
            if artifact.is_file() and str(artifact.resolve()).casefold() not in allowed_files:
                problems.append(f"unexpected delivery residue: {artifact.relative_to(repo).as_posix()}")
            if artifact.is_dir() and artifact.name == "__pycache__":
                problems.append(f"generated __pycache__ directory: {artifact.relative_to(repo).as_posix()}")

    generator = delivery_dir / "auditors" / "generate_evidence.py"
    if generator.is_file():
        check = subprocess.run(
            [sys.executable, "-B", str(generator), "--repo-root", str(repo),
             "--control-root", str(control)], cwd=repo, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if check.returncode:
            problems.append("generated-evidence replay failed:\n" + check.stdout.rstrip())

    if problems:
        print("R07 scope check FAILED")
        for problem in problems:
            print(f"- {problem}")
        return 1
    print("R07 scope check passed")
    print("paths=166 modified=13 added=153 production=43 tests=102 evidence=21")
    print("owners=45 rewritten=13 byte_identical=32 destinations=30 shared_overlap=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
