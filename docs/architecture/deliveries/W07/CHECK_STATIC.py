#!/usr/bin/env python3
"""Deterministic W07 route, retention, test, and import-boundary checks."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
OWNERS = {
    "NumStability.Algorithms.StationaryIteration",
    "NumStability.Algorithms.StationaryIterationDrazin",
    "NumStability.Algorithms.StationaryIterationRounded",
    "NumStability.Algorithms.StationaryIterationSemiconvergent",
    "NumStability.Algorithms.StationaryIterationSemiconvergentExistence",
}
EXPECTED_PRIVATE_HASH = "6A1B37537E0002E89B1B88F2BED03C6F7A701936A237FF33A49DFBD58E76E2B7"
IMPORT_RE = re.compile(
    r"(?m)^(?:public[ \t]+|private[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)
PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|scoped|local)[ \t]+)*"
    r"(?:axiom|constant)\b"
)


class StaticError(RuntimeError):
    pass


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def module_name(root: Path, path: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def imports(payload: str) -> tuple[str, ...]:
    return tuple(IMPORT_RE.findall(payload))


def run_generator(repo: Path, control: Path, ilean_root: Path) -> None:
    command = [
        sys.executable, "-B",
        str(repo / "docs/architecture/deliveries/W07/GENERATE_MIGRATION.py"),
        "--repo-root", str(repo), "--control-root", str(control),
        "--ilean-root", str(ilean_root), "--check",
    ]
    result = subprocess.run(command, cwd=repo, text=True, capture_output=True)
    if result.returncode:
        raise StaticError(
            "deterministic generator check failed:\n" + result.stdout + result.stderr
        )


def check_private_ledger(delivery: Path, routes, retention) -> None:
    path = delivery / "PRIVATE_CLOSURE.tsv"
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    metadata = {row[1]: row[2] for row in rows if row and row[0] == "metadata"}
    expected = {
        "base_revision": BASE,
        "projection_id": "P0012",
        "selected_declaration_count": "252",
        "command_count": "228",
        "private_declaration_count": "8",
        "graph_reverse_closure_count": "31",
        "actual_retained_declaration_count": "116",
        "private_payload_sha256": EXPECTED_PRIVATE_HASH,
    }
    for key, value in expected.items():
        if metadata.get(key) != value:
            raise StaticError(f"PRIVATE_CLOSURE metadata {key} differs")
    owner_rows = [row for row in rows if row and row[0] == "owner"]
    command_rows = [row for row in rows if row and row[0] == "command"]
    if len(owner_rows) != 5 or len(command_rows) != 228:
        raise StaticError("PRIVATE_CLOSURE owner/command counts differ")
    decisions = Counter(row[8] for row in command_rows)
    if decisions != Counter(retain_historical=116, relocate=112):
        raise StaticError(f"PRIVATE_CLOSURE decisions differ: {dict(decisions)}")
    reasons = Counter(row[9] for row in command_rows)
    if reasons != Counter(
        private_seed=8,
        depends_on_private_closure=23,
        classify_document_only_owner=85,
        reviewed_semantic_route=112,
    ):
        raise StaticError(f"PRIVATE_CLOSURE reasons differ: {dict(reasons)}")
    dependent = [row for row in command_rows if row[9] == "depends_on_private_closure"]
    if any(not all(row[index] for index in (10, 11, 12, 13, 14, 15)) for row in dependent):
        raise StaticError("private closure witness row is incomplete")
    floor = sorted(
        row["declaration"] for row in routes
        if row["disposition"] == "retained_private_closure"
    )
    if len(floor) != 31:
        raise StaticError(f"private floor has {len(floor)} declarations")
    digest = hashlib.sha256(("\n".join(floor) + "\n").encode()).hexdigest().upper()
    if digest != EXPECTED_PRIVATE_HASH:
        raise StaticError(f"private floor payload differs: {digest}")
    if len(retention) != 116 or len({row["declaration"] for row in retention}) != 116:
        raise StaticError("RETENTION.tsv must contain 116 unique declarations")
    retained_names = {row["declaration"] for row in routes if row["disposition"].startswith("retained_")}
    if retained_names != {row["declaration"] for row in retention}:
        raise StaticError("RETENTION.tsv and declaration routes disagree")
    for row in retention:
        if row["private_floor"] == "yes" and row["retention_reason"] == "depends_on_private_closure":
            if not all(row[key] for key in (
                "closure_depth", "witness_source", "witness_target", "witness_edge_kind"
            )):
                raise StaticError(f"retention witness is incomplete: {row['declaration']}")


def check_tests(repo: Path, delivery: Path, routes) -> set[str]:
    rows = read_tsv(delivery / "TEST_MATRIX.tsv")
    if len(rows) != 48 or len({row["test_module"] for row in rows}) != 48:
        raise StaticError("TEST_MATRIX must contain 48 unique test modules")
    counts = Counter(
        "canonical" if row["kind"].startswith("canonical-") else row["kind"]
        for row in rows
    )
    if counts != Counter({"canonical": 34, "old-path": 5, "focused": 9}):
        raise StaticError(f"test kind counts differ: {dict(counts)}")
    expected_paths = {module_path(row["test_module"]).as_posix() for row in rows}
    actual_paths = {
        path.relative_to(repo).as_posix()
        for path in (repo / "NumStabilityTest/Reorganization/W07").rglob("*.lean")
    }
    if expected_paths != actual_paths:
        raise StaticError(
            f"test inventory differs: missing={sorted(expected_paths-actual_paths)}, "
            f"extra={sorted(actual_paths-expected_paths)}"
        )
    canonical_modules = {
        row["destination_module"] for row in routes
        if row["disposition"] == "relocated"
    }
    canonical_imports = set()
    for row in rows:
        path = repo / module_path(row["test_module"])
        found = imports(path.read_text(encoding="utf-8"))
        expected = tuple(sorted(filter(None, row["imports"].split(","))))
        if found != expected:
            raise StaticError(f"test imports differ: {row['test_module']}")
        if not row["representatives"]:
            raise StaticError(f"test lacks representatives: {row['test_module']}")
        if row["kind"].startswith("canonical-"):
            if len(found) != 1 or found[0] not in canonical_modules:
                raise StaticError(f"canonical test is not isolated: {row['test_module']}")
            canonical_imports.add(found[0])
        if row["kind"] == "old-path" and (len(found) != 1 or found[0] not in OWNERS):
            raise StaticError(f"old-path test is not isolated: {row['test_module']}")
    if canonical_imports != canonical_modules:
        raise StaticError("canonical tests do not cover every emitted module exactly")
    required = {
        "ReusableIteration", "RoundedExecution", "SemiconvergenceProjector",
        "Drazin", "Chapter17Boundary", "PrivateRetention", "ProtectedW06",
        "AcceptedChapter17Consumers", "AcceptedSemiconvergentConsumer",
    }
    focused = {row["covers"] for row in rows if row["kind"] == "focused"}
    if focused != required:
        raise StaticError(f"focused coverage differs: {focused}")
    return canonical_modules


def check_routes(repo: Path, delivery: Path):
    routes = read_tsv(delivery / "DECLARATION_ROUTES.tsv")
    retention = read_tsv(delivery / "RETENTION.tsv")
    if len(routes) != 252 or len({row["declaration"] for row in routes}) != 252:
        raise StaticError("DECLARATION_ROUTES must contain 252 unique declarations")
    kinds = Counter(row["kind"] for row in routes)
    if kinds != Counter(theorem=192, definition=48, inductive=4, constructor=4, recursor=4):
        raise StaticError(f"declaration kinds differ: {dict(kinds)}")
    visibility = Counter(row["visibility"] for row in routes)
    if visibility != Counter(public=244, private=8):
        raise StaticError(f"visibility counts differ: {dict(visibility)}")
    disposition = Counter(row["disposition"] for row in routes)
    if disposition != Counter(relocated=136, retained_classify_only=85, retained_private_closure=31):
        raise StaticError(f"route dispositions differ: {dict(disposition)}")
    tiers = Counter(row["tier"] for row in routes)
    if tiers != Counter({
        "source": 89, "reusable": 47,
        "unclassified-review": 87, "historical-closure": 29,
    }):
        raise StaticError(f"route tiers differ: {dict(tiers)}")
    private = [row for row in routes if row["visibility"] == "private"]
    if any(row["historical_owner"] != row["destination_module"] for row in private):
        raise StaticError("a private declaration moved or was promoted")
    if any(row["disposition"] != "retained_private_closure" for row in private):
        raise StaticError("a private declaration is outside the closure")
    check_private_ledger(delivery, routes, retention)
    canonical_modules = check_tests(repo, delivery, routes)
    return routes, canonical_modules


def check_import_graph(repo: Path, canonical_modules: set[str]) -> None:
    production_root = repo / "NumStability"
    module_files = {
        module_name(repo, path): path
        for path in production_root.rglob("*.lean")
    }
    graph = {}
    for module, path in module_files.items():
        graph[module] = set(imports(path.read_text(encoding="utf-8")))
    missing = sorted({
        target for targets in graph.values() for target in targets
        if target.startswith("NumStability.") and target not in module_files
    })
    if missing:
        raise StaticError(f"unresolved project imports: {missing[:5]}")

    def closure(start: str) -> set[str]:
        seen = set()
        stack = [start]
        while stack:
            current = stack.pop()
            for target in graph.get(current, ()):
                if target in seen:
                    continue
                seen.add(target)
                if target in graph:
                    stack.append(target)
        return seen

    for module in canonical_modules:
        reached = closure(module)
        historical = reached & OWNERS
        if historical:
            raise StaticError(f"canonical-to-historical reachability: {module} -> {sorted(historical)}")
        if not module.startswith("NumStability.Source."):
            source = sorted(target for target in reached if target.startswith("NumStability.Source."))
            if source:
                raise StaticError(f"reusable-to-Source reachability: {module} -> {source[0]}")

    state = {}
    stack = []

    def visit(module):
        if state.get(module) == 2:
            return
        if state.get(module) == 1:
            raise StaticError("import cycle: " + " -> ".join(stack[stack.index(module):] + [module]))
        state[module] = 1
        stack.append(module)
        for target in sorted(graph.get(module, ())):
            if target in graph:
                visit(target)
        stack.pop()
        state[module] = 2

    for module in sorted(graph):
        visit(module)


def check_sources(repo: Path, canonical_modules: set[str]) -> None:
    sys.path.insert(0, str(repo / "tools/architecture"))
    from generate_baseline import remove_lean_comments

    changed = [repo / module_path(module) for module in canonical_modules]
    changed += [repo / module_path(module) for module in OWNERS]
    changed += list((repo / "NumStabilityTest/Reorganization/W07").rglob("*.lean"))
    for path in changed:
        payload = path.read_text(encoding="utf-8")
        uncommented = remove_lean_comments(payload)
        if PLACEHOLDER_RE.search(uncommented) or AXIOM_RE.search(uncommented):
            raise StaticError(f"placeholder/axiom command in {path.relative_to(repo)}")
        if "/-!" not in payload:
            raise StaticError(f"missing module docstring: {path.relative_to(repo)}")
    for module in canonical_modules:
        payload = (repo / module_path(module)).read_text(encoding="utf-8")
        found = imports(payload)
        if found != tuple(sorted(found)):
            raise StaticError(f"unsorted canonical imports: {module}")
        if set(found) & OWNERS:
            raise StaticError(f"canonical direct historical import: {module}")
    main = (repo / module_path("NumStability.Algorithms.StationaryIteration")).read_text(encoding="utf-8")
    if len(re.findall(r"(?m)^private theorem\b", main)) != 8:
        raise StaticError("historical StationaryIteration must retain exactly eight private commands")


def main() -> int:
    script = Path(__file__).resolve()
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=script.parents[4])
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--ilean-root", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo_root.resolve()
    control = args.control_root.resolve()
    delivery = repo / "docs/architecture/deliveries/W07"
    run_generator(repo, control, args.ilean_root.resolve())
    routes, canonical_modules = check_routes(repo, delivery)
    check_sources(repo, canonical_modules)
    check_import_graph(repo, canonical_modules)
    summary = json.loads((delivery / "ROUTE_SUMMARY.json").read_text(encoding="utf-8"))
    if summary.get("declarations") != 252 or summary.get("tests") != 48:
        raise StaticError("ROUTE_SUMMARY differs")
    print(
        "W07 static checks passed: 252 declarations, 116 retained, 136 relocated, "
        "34 canonical modules, 48 tests, zero cycles, zero reusable-to-Source, "
        "zero canonical-to-historical reachability"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (StaticError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
