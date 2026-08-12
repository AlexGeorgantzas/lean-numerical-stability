#!/usr/bin/env python3
"""Audit the exact B0004/R12 worker diff against frozen C0001 scope."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
CONTROL = "5e075b947a63e84c784afecd00e1f130e21ea659"
BRANCH = "codex/reorg-completion-2026-08-r12-ch13-equations-table"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion"
B_PATH = f"{PHASE}/branches/B0004.json"
P_PATH = f"{PHASE}/projections/P0004.json"
R_PATH = f"{PHASE}/requests/R0004.json"
DELIVERY = "docs/architecture/deliveries/R12/"
SUBJECT = "Split Chapter 13 equations and table umbrellas (R12)"
B_SHA256 = "B01C260B74848516E491B51FC6416E1C4B871B1F8B152CB44B98BE4127B1E2B0"
P_SHA256 = "EC9F4E6FDC55081BDCCED0B4AE41B553EA8D455EC9576EF27F4F8AB987393A8E"
R_SHA256 = "C2AC9E79A9B6937C4E155A7A50D6E4A74F1FAE45CCF698995359B171941A1701"
MATRIX = "NumStability/Analysis/MatrixAlgebra.lean"
MATRIX_OID = "06ddc3d5d2a3c19c6aff3c088f932f3e3074d279"
SHARED = {
    "NumStabilityTest.lean",
    "docs/architecture/layout-exceptions.json",
    "docs/architecture/tiers.json",
}
DESTINATIONS = {
    "NumStability/Source/Higham/Chapter13/Equation23/ProductBounds/PointRow.lean",
    "NumStability/Source/Higham/Chapter13/Equation25/BackwardError/Bounds.lean",
    "NumStability/Source/Higham/Chapter13/Equation25/PartitionedComputation/Implementation1.lean",
    "NumStability/Source/Higham/Chapter13/Table01/BackwardErrorBounds/Endpoints.lean",
    "NumStability/Source/Higham/Chapter13/Table01/DiagonalDominance/Bounds.lean",
    "NumStability/Source/Higham/Chapter13/Table01/ProductTransfers/Families.lean",
}
DELIVERY_FILES = {
    "CHANGED_PATHS.md", "CHECK_PROJECTION.py", "CHECK_REQUEST_REPLAY.py",
    "CHECK_SCOPE.py", "CHECK_STATIC.py", "DECLARATION_ROUTES.tsv",
    "DELIVERY.md", "GATE_RESULTS.tsv", "INTEGRATOR_REQUESTS.md",
    "PRIVATE_CLOSURE.md", "PRIVATE_CLOSURE.tsv", "PROJECTION.md",
    "RETENTION.tsv", "ROUTING.md", "TEST_MATRIX.tsv",
}
FORBIDDEN_SUFFIXES = {
    ".olean", ".ilean", ".pyc", ".pyo", ".trace", ".o", ".obj", ".exe",
    ".dll", ".so", ".dylib", ".aux", ".log",
}
GATE_HEADER = [
    "phase", "gate", "command", "targets", "target_sha256", "jobs",
    "mutex", "exit_code", "seconds", "result", "notes",
]
MUTEX = r"Local\lean-reorganization-2026-08"
TEST_TARGETS = {
    "tests_canonical": ("6", "F28302E80579ED38295DE0550BAFFB29042010197CEF48B25035620BEC2C8D33"),
    "tests_focused": ("6", "BC83211408490466615CF5569C4718121F903E2AAF142990E688BC4519D0975A"),
    "tests_old_only": ("3", "63C42A0308507EBFE68D8354485230B4D6D16FC9B848995B3047948FFAD4F330"),
    "tests_protected_consumer": (
        "11", "5B0760D99BBD66F3134939A7BB6A4B74B3884F7C45DA61255CEF9A49E719C8C0"
    ),
}
INTEGRATED_GATES = {
    "integrated_compile_tools", "integrated_phase_self_test",
    "integrated_phase_projection_self_test",
    "integrated_completion_projection_self_test",
    "integrated_completion_self_test", "integrated_all_phases",
    "integrated_completion_phase", "integrated_layout",
    "integrated_compatibility", "integrated_provenance",
    "integrated_strict_source", "integrated_library_and_tests",
    "integrated_lake_test", "integrated_staged_diff_check",
}
REQUIRED_GATES = {
    "scope", "static", "r0004_replay", *TEST_TARGETS,
    "tests_all", "layout_worker", "compatibility_worker",
    "provenance_worker", "strict_source_worker", "placeholder_scan",
    "tracked_generated", "diff_check", "library_and_tests", "lake_test",
    "candidate", "deterministic_replay", "p0004_replay",
    "r0004_integrated_full", "diff_check_staged", *INTEGRATED_GATES,
}
MUTEX_GATES = {
    *TEST_TARGETS, "tests_all", "strict_source_worker", "library_and_tests",
    "lake_test", "candidate", "deterministic_replay", "p0004_replay",
    "r0004_integrated_full", *INTEGRATED_GATES,
}


class ScopeError(RuntimeError):
    pass


def run(*args: str, check: bool = True) -> str:
    result = subprocess.run(
        list(args), cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if check and result.returncode:
        raise ScopeError(result.stdout + f"command failed: {' '.join(args)}")
    return result.stdout


def git(*args: str, check: bool = True) -> str:
    return run("git", *args, check=check)


def git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def load_control(path: str, expected_sha: str) -> dict:
    payload = git_bytes(CONTROL, path)
    if digest(payload) != expected_sha:
        raise ScopeError(f"control hash differs: {path}")
    return json.loads(payload)


def verify_controls() -> tuple[dict, dict, dict]:
    branch = load_control(B_PATH, B_SHA256)
    projection = load_control(P_PATH, P_SHA256)
    request = load_control(R_PATH, R_SHA256)
    expected = {
        "branch_id": "B0004", "wave_id": "R12", "branch_name": BRANCH,
        "base_checkpoint_id": "C0001", "base_sha": BASE,
        "baseline_projection_id": "P0004", "lane_id": "claude-lane",
        "owner_id": "primary-human", "status": "active",
    }
    for key, value in expected.items():
        if branch.get(key) != value:
            raise ScopeError(f"B0004 {key} differs")
    if branch.get("operator_ids") != ["codex-local"]:
        raise ScopeError("B0004 temporary operator authorization differs")
    if branch.get("shared_request_ids") != ["R0004"]:
        raise ScopeError("B0004 shared request differs")
    if projection.get("projection_id") != "P0004" or projection.get(
        "expected_counts") != {
            "body_edges": 133, "declarations": 34,
            "signature_edges": 80, "union_edges": 139,
        }:
        raise ScopeError("P0004 identity/counts differ")
    if request.get("paths") != [
        "NumStabilityTest.lean",
        "docs/architecture/layout-exceptions.json",
        "docs/architecture/tiers.json",
    ]:
        raise ScopeError("R0004 path roster differs")
    evidence = branch.get("refresh", {}).get("evidence", [])
    if len(evidence) != 24:
        raise ScopeError("B0004 refresh evidence count differs")
    for item in evidence:
        if digest(git_bytes(CONTROL, item["path"])) != item["sha256"]:
            raise ScopeError(f"refresh evidence hash differs: {item['path']}")
    return branch, projection, request


def changes() -> dict[str, str]:
    result: dict[str, str] = {}
    for line in git("diff", "--name-status", "--no-renames", BASE, "--").splitlines():
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] not in {"A", "M"}:
            raise ScopeError(f"forbidden diff status: {line}")
        result[fields[1].replace("\\", "/")] = fields[0]
    for path in git("ls-files", "--others", "--exclude-standard").splitlines():
        path = path.replace("\\", "/")
        if path in result:
            raise ScopeError(f"duplicate tracked/untracked path: {path}")
        result[path] = "A"
    return result


def verify_ledger(changed: dict[str, str]) -> None:
    path = ROOT / DELIVERY / "CHANGED_PATHS.md"
    if not path.is_file():
        raise ScopeError("CHANGED_PATHS.md missing")
    actual: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if re.match(r"^[AM]\t", line):
            status, relative = line.split("\t", 1)
            actual[relative] = status
    if actual != dict(sorted(changed.items())):
        raise ScopeError("CHANGED_PATHS.md differs from actual diff")


def verify_gate_results() -> None:
    path = ROOT / DELIVERY / "GATE_RESULTS.tsv"
    with path.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != GATE_HEADER:
            raise ScopeError("GATE_RESULTS header differs")
        rows = list(reader)
    by_gate = {row["gate"]: row for row in rows}
    if len(by_gate) != len(rows) or set(by_gate) != REQUIRED_GATES:
        raise ScopeError("GATE_RESULTS gate roster/uniqueness differs")
    for gate, row in by_gate.items():
        if not row["phase"] or not row["command"] or not row["notes"]:
            raise ScopeError(f"GATE_RESULTS required field empty: {gate}")
        try:
            jobs = int(row["jobs"])
            exit_code = int(row["exit_code"])
            seconds = float(row["seconds"])
        except ValueError as error:
            raise ScopeError(f"GATE_RESULTS numeric field differs: {gate}") from error
        if jobs < 0 or seconds < 0:
            raise ScopeError(f"GATE_RESULTS negative metric: {gate}")
        expected_mutex = MUTEX if gate in MUTEX_GATES else "-"
        if row["mutex"] != expected_mutex:
            raise ScopeError(f"GATE_RESULTS mutex differs: {gate}")
        if gate == "layout_worker":
            if exit_code != 1 or row["result"] != "integrator_required":
                raise ScopeError("worker layout result differs")
            if not all(token in row["notes"] for token in (
                "27 R12 tests", "Equation23", "Equation25", "Table01", "R0004"
            )):
                raise ScopeError("worker layout deferred findings differ")
        elif exit_code != 0 or row["result"] != "pass":
            raise ScopeError(f"non-passing final gate: {gate}")
    for gate, (count, target_hash) in TEST_TARGETS.items():
        row = by_gate[gate]
        if row["targets"] != count or row["target_sha256"] != target_hash:
            raise ScopeError(f"test target evidence differs: {gate}")
    hash_pattern = re.compile(r"(?:tsv|json|md)=([0-9A-F]{64})/[0-9]+")
    before = hash_pattern.findall(by_gate["candidate"]["notes"])
    after = hash_pattern.findall(by_gate["deterministic_replay"]["notes"])
    if len(before) != 3 or before != after or "byte-identical" not in by_gate[
        "deterministic_replay"]["notes"]:
        raise ScopeError("candidate deterministic hash evidence differs")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--final", action="store_true")
    parser.add_argument("--check-gates", action="store_true")
    args = parser.parse_args()

    branch, _, _ = verify_controls()
    if git("branch", "--show-current").strip() != BRANCH:
        raise ScopeError("wrong worker branch")
    if git("merge-base", BASE, "HEAD").strip() != BASE:
        raise ScopeError("worker no longer descends from exact C0001")
    if git("rev-parse", f"{BASE}:{MATRIX}").strip() != MATRIX_OID:
        raise ScopeError("MatrixAlgebra C0001 blob pin differs")
    if git("hash-object", "--", MATRIX).strip() != MATRIX_OID:
        raise ScopeError("MatrixAlgebra worktree blob differs")

    changed = changes()
    owners = {item["path"] for item in branch["owned_paths"]}
    prefixes = tuple(item["path"] for item in branch["destination_prefixes"])
    forbidden_exact = {
        item["path"] for item in branch["forbidden_paths"]
        if item["match"] == "exact"
    }
    forbidden_prefixes = tuple(
        item["path"] for item in branch["forbidden_paths"]
        if item["match"] == "prefix"
    )
    for path, status in changed.items():
        if path in SHARED:
            raise ScopeError(f"integrator-owned path changed: {path}")
        if path in forbidden_exact or path.startswith(forbidden_prefixes):
            raise ScopeError(f"B0004 forbidden path changed: {path}")
        if not (path in owners or path.startswith(prefixes)):
            raise ScopeError(f"unauthorized changed path: {path}")
        parts = set(path.split("/"))
        if "__pycache__" in parts or Path(path).suffix.lower() in FORBIDDEN_SUFFIXES:
            raise ScopeError(f"generated artifact in diff: {path}")
        if path in owners and status != "M":
            raise ScopeError(f"owner is not modified in place: {path}")
        if path not in owners and status != "A":
            raise ScopeError(f"new-scope path is not added: {path}")

    if {path for path in changed if path in owners} != owners:
        raise ScopeError("owner roster differs")
    production = {path for path in changed if path.startswith("NumStability/")}
    tests = {
        path for path in changed
        if path.startswith("NumStabilityTest/Reorganization/R12/")
    }
    evidence = {path for path in changed if path.startswith(DELIVERY)}
    if production != owners | DESTINATIONS:
        raise ScopeError("production roster differs")
    if len(tests) != 27:
        raise ScopeError(f"test path count differs: {len(tests)}")
    if {Path(path).name for path in evidence} != DELIVERY_FILES:
        raise ScopeError("delivery artifact roster differs")
    if len(changed) != 51 or sum(v == "M" for v in changed.values()) != 3:
        raise ScopeError("changed path/status totals differ")

    folded: dict[str, str] = {}
    for raw in git("ls-files").splitlines() + list(changed):
        path = raw.replace("\\", "/")
        key = path.casefold()
        prior = folded.get(key)
        if prior is not None and prior != path:
            raise ScopeError(f"casefold collision: {prior} / {path}")
        folded[key] = path
    verify_ledger(changed)

    if args.check_gates or args.final:
        verify_gate_results()

    if args.final:
        if git("status", "--porcelain=v1").strip():
            raise ScopeError("final worktree is not clean")
        if git("rev-parse", "HEAD^").strip() != BASE:
            raise ScopeError("delivery parent differs from C0001")
        if git("log", "-1", "--format=%s").strip() != SUBJECT:
            raise ScopeError("delivery subject differs")
        if len(git("rev-list", f"{BASE}..HEAD").splitlines()) != 1:
            raise ScopeError("delivery is not exactly one commit after C0001")

    print(
        "R12 scope OK: 51 paths; 3 modified owners; 6 new declaration "
        "leaves; 27 tests; 15 evidence artifacts; 24 control hashes"
    )


if __name__ == "__main__":
    try:
        main()
    except ScopeError as error:
        print(f"R12 scope audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
