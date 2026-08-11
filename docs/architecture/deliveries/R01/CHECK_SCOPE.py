#!/usr/bin/env python3
"""Audit the exact B0001/R01 worker diff against the frozen C0000 scope."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "b1b18772d80185ec08f49c818919558645c330a1"
BRANCH = "codex/reorg-completion-2026-08-r01-stationary-semiconvergence"
ACTIVE_CONTROL = "daf5c92355e26c07ab0d219c20cd6ce6782b98f3"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion/"
BRANCH_RECORD = PHASE + "branches/B0001.json"
PROJECTION_RECORD = PHASE + "projections/P0001.json"
DELIVERY_PREFIX = "docs/architecture/deliveries/R01/"
CHANGED_PATHS = DELIVERY_PREFIX + "CHANGED_PATHS.md"
MATRIX_ALGEBRA = "NumStability/Analysis/MatrixAlgebra.lean"
MATRIX_BLOB = "06ddc3d5d2a3c19c6aff3c088f932f3e3074d279"
OWNERS = {
    "NumStability/Algorithms/StationaryIteration.lean",
    "NumStability/Algorithms/StationaryIterationDrazin.lean",
    "NumStability/Algorithms/StationaryIterationRounded.lean",
    "NumStability/Algorithms/StationaryIterationSemiconvergent.lean",
    "NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean",
    "NumStability/Analysis/SemiconvergentBlockFormExists.lean",
    "NumStability/Analysis/SemiconvergentExistenceComplete.lean",
    "NumStability/Analysis/SemiconvergentExistenceFull.lean",
    "NumStability/Analysis/SemiconvergentLimitGeneral.lean",
    "NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean",
    "NumStability/Source/Higham/Chapter17/Equation08.lean",
    "NumStability/Source/Higham/Chapter17/Equation12.lean",
    "NumStability/Source/Higham/Chapter17/Equation15.lean",
    "NumStability/Source/Higham/Chapter17/Equation16.lean",
    "NumStability/Source/Higham/Chapter17/Equation17.lean",
    "NumStability/Source/Higham/Chapter17/Equation20.lean",
}
PREFIXES = (
    "NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/",
    "NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/",
    "NumStability/Source/Higham/Chapter17/Results/",
    "NumStabilityTest/Reorganization/R01/",
    "docs/architecture/deliveries/R01/",
)
SHARED_REQUEST_PATHS = {
    "NumStability/Algorithms.lean",
    "NumStability/Analysis.lean",
    "NumStability/Algorithms/StationaryIterationSeries.lean",
    "NumStability/Source/Higham/Chapter17.lean",
    "NumStability/Source/Higham/Chapter17/Equation22.lean",
}
FORBIDDEN_PARTS = {".lake", "benchmark-results", "__pycache__", ".codex"}
FORBIDDEN_SUFFIXES = {
    ".olean", ".ilean", ".pyc", ".trace", ".c", ".o", ".obj", ".exe",
    ".dll", ".so", ".dylib", ".class",
}
FINAL_DELIVERY_FILES = {
    "CHECK_PROJECTION.py",
    "CHECK_REQUEST_REPLAY.py",
    "CHECK_SCOPE.py",
    "CHECK_STATIC.py",
    "CHANGED_PATHS.md",
    "DECLARATION_ROUTES.tsv",
    "DELIVERY.md",
    "GATE_RESULTS.tsv",
    "INTEGRATOR_POSTIMAGES.tsv",
    "INTEGRATOR_REQUEST.patch",
    "INTEGRATOR_REQUESTS.md",
    "PRIVATE_CLOSURE.md",
    "PRIVATE_CLOSURE.tsv",
    "PROJECTION.md",
    "RETENTION.tsv",
    "ROUTING.md",
    "TEST_MATRIX.tsv",
}
FINAL_COUNTS = {
    "changed": 98,
    "modified": 16,
    "added": 82,
    "owners": 16,
    "production": 40,
    "tests": 41,
    "delivery": 17,
}
EXPECTED_SELECTOR = {
    "path": PHASE + "selectors/R01.tsv",
    "sha256": "6D839B9008474CD9CBECEF5EE35FE347B91FD50541F8E347AA8648FF55EF81EB",
}
EXPECTED_PROJECTION = {
    "path": PHASE + "projections/P0001.tsv.gz",
    "sha256": "DB8ACB22219D5C0C51E3F8F8D5296170FDF92C8C1166C0FDB2598EF6E11728D2",
}
EXPECTED_CHECKER = {
    "path": "tools/architecture/check_completion_phase_projection.py",
    "sha256": "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220",
}
EXPECTED_BASELINE = {
    "path": PHASE + "baselines/C0000-combined.json",
    "sha256": "2EA9D8C24D3E4D3EEA6B3A135FE195946BB8659C7E5FBF9452DADD89D1726A2F",
}
EXPECTED_PROJECTION_COUNTS = {
    "body_edges": 1341,
    "declarations": 243,
    "signature_edges": 693,
    "union_edges": 1422,
}
PRIVATE_MAP = PHASE + "branches/B0001-private-normalization.tsv"
PRIVATE_MAP_SHA256 = "0063E4B0E9C1DAD56F0CCD0A5B9D3897D6F18BEF860482AEB609B83DF6CD4F4A"


class ScopeError(RuntimeError):
    pass


def git(*args: str, cwd: Path = ROOT, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args], cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if check and result.returncode:
        raise ScopeError(result.stdout + f"git {' '.join(args)} failed")
    return result.stdout


def read_json(root: Path, relative: str) -> dict[str, object]:
    path = root / relative
    if not path.is_file():
        raise ScopeError(f"active-control record is missing: {relative}")
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ScopeError(f"active-control record is not an object: {relative}")
    return value


def exact_rule_paths(record: dict[str, object], field: str, match: str) -> set[str]:
    rules = record.get(field)
    if not isinstance(rules, list):
        raise ScopeError(f"B0001 {field} is not a rule list")
    paths: set[str] = set()
    for rule in rules:
        if not isinstance(rule, dict) or rule.get("match") != match or not isinstance(rule.get("path"), str):
            raise ScopeError(f"B0001 {field} contains a non-{match} rule")
        path = rule["path"]
        if path in paths:
            raise ScopeError(f"B0001 {field} contains a duplicate: {path}")
        paths.add(path)
    return paths


def verify_control(control: Path) -> None:
    if not control.is_dir():
        raise ScopeError(f"active-control checkout is missing: {control}")
    if git("rev-parse", "HEAD", cwd=control).strip() != ACTIVE_CONTROL:
        raise ScopeError("active-control HEAD differs")
    if git("status", "--porcelain=v1", "--untracked-files=all", cwd=control).strip():
        raise ScopeError("active-control checkout is not clean")

    branch = read_json(control, BRANCH_RECORD)
    required_branch = {
        "status": "active",
        "branch_id": "B0001",
        "wave_id": "R01",
        "phase_id": "repository-reorganization-completion-2026-08",
        "base_checkpoint_id": "C0000",
        "base_sha": BASE,
        "branch_name": BRANCH,
        "lane_id": "codex-lane",
        "owner_id": "primary-human",
        "baseline_projection_id": "P0001",
    }
    for field, expected in required_branch.items():
        if branch.get(field) != expected:
            raise ScopeError(f"active B0001 field differs: {field}")
    if branch.get("operator_ids") != ["codex-local"]:
        raise ScopeError("active B0001 operator differs")
    if branch.get("shared_request_ids") != ["R0001"]:
        raise ScopeError("active B0001 request roster differs")
    if exact_rule_paths(branch, "owned_paths", "exact") != OWNERS:
        raise ScopeError("active B0001 owner roster differs")
    if exact_rule_paths(branch, "destination_prefixes", "prefix") != set(PREFIXES):
        raise ScopeError("active B0001 destination roster differs")
    forbidden = branch.get("forbidden_paths")
    if not isinstance(forbidden, list):
        raise ScopeError("active B0001 forbidden roster is missing")
    forbidden_exact = {
        rule.get("path") for rule in forbidden
        if isinstance(rule, dict) and rule.get("match") == "exact"
    }
    if not (SHARED_REQUEST_PATHS | {MATRIX_ALGEBRA}) <= forbidden_exact:
        raise ScopeError("active B0001 does not protect every shared/protected path")

    projection = read_json(control, PROJECTION_RECORD)
    required_projection = {
        "status": "active",
        "projection_id": "P0001",
        "wave_id": "R01",
        "phase_id": "repository-reorganization-completion-2026-08",
        "base_checkpoint_id": "C0000",
        "superseded_by": None,
    }
    for field, expected in required_projection.items():
        if projection.get(field) != expected:
            raise ScopeError(f"active P0001 field differs: {field}")
    selector = projection.get("selector")
    if not isinstance(selector, dict) or selector.get("kind") != "module_path_tsv" or selector.get("artifact") != EXPECTED_SELECTOR:
        raise ScopeError("active P0001 selector differs")
    if projection.get("projection_graph") != EXPECTED_PROJECTION:
        raise ScopeError("active P0001 projection graph differs")
    if projection.get("combined_baseline") != EXPECTED_BASELINE:
        raise ScopeError("active P0001 combined baseline differs")
    if projection.get("expected_counts") != EXPECTED_PROJECTION_COUNTS:
        raise ScopeError("active P0001 expected counts differ")
    checker = projection.get("checker")
    if not isinstance(checker, dict) or checker.get("artifact") != EXPECTED_CHECKER:
        raise ScopeError("active P0001 checker differs")
    arguments = checker.get("arguments")
    expected_arguments = {
        *("--allow-module=" + path.removesuffix(".lean").replace("/", ".") for path in OWNERS),
        *("--allow-prefix=" + prefix.rstrip("/").replace("/", ".") + "." for prefix in PREFIXES[:3]),
        "--candidate=<candidate-format2.tsv>",
        f"--private-map={PRIVATE_MAP}",
        f"--private-map-sha256={PRIVATE_MAP_SHA256}",
        f"--projection={EXPECTED_PROJECTION['path']}",
        f"--projection-sha256={EXPECTED_PROJECTION['sha256']}",
    }
    if not isinstance(arguments, list) or len(arguments) != 24 or set(arguments) != expected_arguments:
        raise ScopeError("active P0001 checker arguments differ")


def current_paths() -> tuple[set[str], dict[str, str]]:
    paths: set[str] = set()
    states: dict[str, str] = {}
    for line in git("diff", "--name-status", "--no-renames", BASE, "--").splitlines():
        fields = line.split("\t")
        if len(fields) != 2:
            raise ScopeError(f"unexpected diff row: {line}")
        state, path = fields
        path = path.replace("\\", "/")
        if state not in {"A", "M"}:
            raise ScopeError(f"only add/modify statuses are allowed: {line}")
        if path in states:
            raise ScopeError(f"duplicate changed path: {path}")
        paths.add(path)
        states[path] = state
    for path in git("ls-files", "--others", "--exclude-standard").splitlines():
        path = path.replace("\\", "/")
        if path in states:
            raise ScopeError(f"path is both diff-visible and untracked: {path}")
        paths.add(path)
        states[path] = "A"
    return paths, states


def allowed(path: str) -> bool:
    return path in OWNERS or any(path.startswith(prefix) for prefix in PREFIXES)


def verify_casefold(paths: set[str]) -> None:
    folded: dict[str, str] = {}
    for path in git("ls-files").splitlines() + git("ls-files", "--others", "--exclude-standard").splitlines():
        normalized = path.replace("\\", "/")
        key = normalized.casefold()
        previous = folded.get(key)
        if previous is not None and previous != normalized:
            raise ScopeError(f"casefold collision: {previous} <> {normalized}")
        folded[key] = normalized
    base_paths = [p.replace("\\", "/") for p in git("ls-tree", "-r", "--name-only", BASE).splitlines()]
    for prefix in PREFIXES:
        hits = [p for p in base_paths if p.casefold().startswith(prefix.casefold())]
        if hits:
            raise ScopeError(f"destination was not casefold-vacant at C0000: {prefix}: {hits[0]}")
        if not any(p.startswith(prefix) for p in paths):
            raise ScopeError(f"authorized prefix is unpopulated: {prefix}")


def changed_paths_ledger() -> dict[str, str]:
    path = ROOT / CHANGED_PATHS
    if not path.is_file():
        raise ScopeError("CHANGED_PATHS.md is missing")
    result: dict[str, str] = {}
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        match = re.fullmatch(r"- `([AM])` `(.+)`", line)
        if match:
            status, changed = match.groups()
            if changed in result:
                raise ScopeError(f"duplicate CHANGED_PATHS row at line {line_number}: {changed}")
            result[changed] = status
    return result


def scope_counts(paths: set[str], states: dict[str, str]) -> dict[str, int]:
    return {
        "changed": len(paths),
        "modified": sum(state == "M" for state in states.values()),
        "added": sum(state == "A" for state in states.values()),
        "owners": len(OWNERS),
        "production": sum(path.startswith("NumStability/") for path in paths),
        "tests": sum(path.startswith("NumStabilityTest/") for path in paths),
        "delivery": sum(path.startswith(DELIVERY_PREFIX) for path in paths),
    }


def verify_final_ledger(paths: set[str], states: dict[str, str]) -> None:
    ledger = changed_paths_ledger()
    if ledger != states:
        missing = sorted(set(states) - set(ledger))
        extra = sorted(set(ledger) - set(states))
        wrong = sorted(path for path in set(states) & set(ledger) if states[path] != ledger[path])
        raise ScopeError(
            "CHANGED_PATHS status ledger mismatch: "
            f"missing={missing[:1]} extra={extra[:1]} wrong_status={wrong[:1]}"
        )
    expected_delivery = {DELIVERY_PREFIX + name for name in FINAL_DELIVERY_FILES}
    actual_delivery = {path for path in paths if path.startswith(DELIVERY_PREFIX)}
    if actual_delivery != expected_delivery:
        missing = sorted(expected_delivery - actual_delivery)
        extra = sorted(actual_delivery - expected_delivery)
        raise ScopeError(f"final delivery roster differs: missing={missing[:1]} extra={extra[:1]}")
    counts = scope_counts(paths, states)
    if counts != FINAL_COUNTS:
        raise ScopeError(f"final scope counts differ: {counts} != {FINAL_COUNTS}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--control-root", type=Path, default=ROOT.parent / "final-main-audit")
    parser.add_argument("--check-changed-paths", action="store_true")
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    control = args.control_root.resolve()

    if git("branch", "--show-current").strip() != BRANCH:
        raise ScopeError("worker branch name differs")
    if subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT).returncode:
        raise ScopeError("C0000 is not an ancestor of HEAD")
    if git("rev-parse", f"{BASE}:{MATRIX_ALGEBRA}").strip() != MATRIX_BLOB:
        raise ScopeError("frozen MatrixAlgebra base blob differs")
    if git("hash-object", MATRIX_ALGEBRA).strip() != MATRIX_BLOB:
        raise ScopeError("protected MatrixAlgebra changed")
    verify_control(control)
    if args.require_clean and git("status", "--porcelain=v1", "--untracked-files=all").strip():
        raise ScopeError("worker checkout is not clean")

    paths, states = current_paths()
    generated = sorted(
        path for path in paths
        if {part.casefold() for part in Path(path).parts} & FORBIDDEN_PARTS
        or Path(path).suffix.casefold() in FORBIDDEN_SUFFIXES
    )
    if generated:
        raise ScopeError(f"generated/private artifact in scope: {generated[0]}")
    forbidden = sorted(path for path in paths if not allowed(path))
    if forbidden:
        raise ScopeError(f"out-of-scope path: {forbidden[0]}")
    if paths & SHARED_REQUEST_PATHS:
        raise ScopeError(f"integrator-owned request path was edited: {sorted(paths & SHARED_REQUEST_PATHS)[0]}")
    if not OWNERS <= paths:
        raise ScopeError(f"owned historical paths missing from diff: {sorted(OWNERS - paths)}")
    if any(states[path] != "M" for path in OWNERS):
        raise ScopeError("every historical owner must be modified in place, never added/deleted/renamed")
    verify_casefold(paths)

    if args.check_changed_paths:
        verify_final_ledger(paths, states)

    counts = scope_counts(paths, states)
    print("R01 scope passed: " + ", ".join(f"{key}={value}" for key, value in counts.items()))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (json.JSONDecodeError, OSError, ScopeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
