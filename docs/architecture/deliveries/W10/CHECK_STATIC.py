#!/usr/bin/env python3
"""Deterministic W10 route, retention, test, and import-boundary checks."""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
IMPORT_RE = re.compile(r"(?m)^(?:public\s+|private\s+)?import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$")
PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|scoped|local)\s+)*(?:axiom|constant)\b")


class StaticError(RuntimeError):
    pass


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def candidate_modules(path: Path, selected: set[str]) -> dict[str, str]:
    found: dict[str, str] = {}
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            if not line.startswith("declaration\t"):
                continue
            fields = line.rstrip("\n").split("\t")
            if len(fields) >= 4 and fields[1] in selected:
                if fields[1] in found:
                    raise StaticError(f"duplicate candidate declaration: {fields[1]}")
                found[fields[1]] = fields[2]
    return found


def write_routes(path: Path, rows: list[dict[str, str]], physical: dict[str, str]) -> None:
    fields = list(rows[0])
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            row = dict(row)
            row["destination_module"] = physical[row["declaration"]]
            writer.writerow(row)


def check_routes(repo: Path, delivery: Path, candidate: Path, write: bool) -> tuple[list[dict[str, str]], set[str], set[str]]:
    route_path = delivery / "DECLARATION_ROUTES.tsv"
    rows = read_tsv(route_path)
    if len(rows) != 1029 or len({r["declaration"] for r in rows}) != 1029:
        raise StaticError("route ledger must contain 1,029 unique declarations")
    physical = candidate_modules(candidate, {r["declaration"] for r in rows})
    if len(physical) != 1029:
        raise StaticError(f"candidate contains only {len(physical)}/1029 selected declarations")
    if write:
        write_routes(route_path, rows, physical)
        rows = read_tsv(route_path)
    mismatches = [r["declaration"] for r in rows if r["destination_module"] != physical[r["declaration"]]]
    if mismatches:
        raise StaticError(f"{len(mismatches)} routes do not name the physical candidate module; first: {mismatches[0]}")
    if Counter(r["visibility"] for r in rows) != Counter(public=949, private=80):
        raise StaticError("route visibility counts differ")
    if Counter(r["tier"] for r in rows) != Counter(reusable=494, source=401, historical=134):
        raise StaticError("route tier counts differ")
    if Counter(r["pinned_by_private_closure"] for r in rows) != Counter(no=897, yes=132):
        raise StaticError("route private-closure pin counts differ")
    if Counter(r["demoted"] for r in rows) != Counter(no=1007, yes=22):
        raise StaticError("route demotion counts differ")
    owners = {r["owner_module"] for r in rows}
    if len(owners) != 27:
        raise StaticError("route owner count differs")
    routed_canonical = {r["destination_module"] for r in rows if r["tier"] != "historical"}
    reusable = {r["destination_module"] for r in rows if r["tier"] == "reusable"}
    source = {r["destination_module"] for r in rows if r["tier"] == "source"}
    if len(routed_canonical) != 95 or len(reusable) != 49 or len(source) != 46:
        raise StaticError(f"physical route modules differ: {len(routed_canonical)}/{len(reusable)}/{len(source)}")
    correspondence_wrappers = {
        "NumStability.Source.Higham.Chapter15.Section01.ConditionNumbers.CondEstimation"
    }
    canonical = routed_canonical | correspondence_wrappers
    if len(canonical) != 96:
        raise StaticError("canonical module roster must contain 95 declaration owners plus one Source wrapper")
    for row in rows:
        module = row["destination_module"]
        if not (repo / module_path(module)).is_file():
            raise StaticError(f"route module does not exist: {module}")
        if row["tier"] == "historical" and module != row["owner_module"]:
            raise StaticError(f"retained route left its owner: {row['declaration']}")
        if row["tier"] == "reusable" and not module.startswith("NumStability.Algorithms.NormEstimation."):
            raise StaticError(f"reusable route outside NormEstimation: {row['declaration']}")
        if row["tier"] == "source" and not module.startswith("NumStability.Source.Higham.Chapter15."):
            raise StaticError(f"source route outside Chapter15: {row['declaration']}")
    private = [r for r in rows if r["visibility"] == "private"]
    if any(r["tier"] != "historical" or r["pinned_by_private_closure"] != "yes" for r in private):
        raise StaticError("a private declaration moved or was promoted")
    reentry = {
        r["declaration"] for r in rows
        if r["tier"] == "historical" and r["pinned_by_private_closure"] == "no"
    }
    if reentry != {
        "NumStability.Higham15.H15_Algorithm15_4_condEstimate_le_kappaOne",
        "NumStability.Higham15.H15_Algorithm15_4_scaled_le_kappaOne",
    }:
        raise StaticError(f"full-graph re-entry retention differs: {sorted(reentry)}")
    return rows, canonical, reusable


def check_retention(delivery: Path, routes: list[dict[str, str]]) -> None:
    closure = read_tsv(delivery / "PRIVATE_CLOSURE.tsv")
    if len(closure) != 132 or len({r["declaration"] for r in closure}) != 132:
        raise StaticError("private closure must contain 132 unique declarations")
    if Counter((r["visibility"], r["role"]) for r in closure) != Counter({("private", "private seed"): 80, ("public", "public dependent"): 52}):
        raise StaticError("private closure 80+52 split differs")
    pinned = {r["declaration"] for r in routes if r["pinned_by_private_closure"] == "yes"}
    if pinned != {r["declaration"] for r in closure}:
        raise StaticError("private closure and route ledger disagree")
    retention = read_tsv(delivery / "RETENTION.tsv")
    if len(retention) != 27:
        raise StaticError("retention ledger must contain 27 owners")
    totals = {key: sum(int(r[key]) for r in retention) for key in ("declarations", "retained", "relocated", "private", "pinned")}
    if totals != {"declarations": 1029, "retained": 134, "relocated": 895, "private": 80, "pinned": 132}:
        raise StaticError(f"retention totals differ: {totals}")
    by_owner = defaultdict(Counter)
    for row in routes:
        by_owner[row["owner_module"]]["declarations"] += 1
        by_owner[row["owner_module"]]["private"] += row["visibility"] == "private"
        by_owner[row["owner_module"]]["pinned"] += row["pinned_by_private_closure"] == "yes"
        by_owner[row["owner_module"]]["retained"] += row["tier"] == "historical"
        by_owner[row["owner_module"]]["relocated"] += row["tier"] != "historical"
    for row in retention:
        if any(int(row[key]) != by_owner[row["owner_module"]][key] for key in ("declarations", "retained", "relocated", "private", "pinned")):
            raise StaticError(f"retention row differs: {row['owner_module']}")


def check_tests(repo: Path, delivery: Path, canonical: set[str], owners: set[str]) -> None:
    rows = read_tsv(delivery / "TEST_MATRIX.tsv")
    if len(rows) != 135 or len({r["test_module"] for r in rows}) != 135:
        raise StaticError("test matrix must contain 135 unique modules")
    if Counter(r["kind"] for r in rows) != Counter({"canonical-only": 96, "old-path-only": 27, "focused": 12}):
        raise StaticError("test kind counts differ")
    canonical_checks: list[str] = []
    old_checks: list[str] = []
    route_rows = read_tsv(delivery / "DECLARATION_ROUTES.tsv")
    relocated = {r["declaration"] for r in route_rows if r["tier"] != "historical"}
    public = {r["declaration"] for r in route_rows if r["visibility"] == "public"}
    for row in rows:
        path = repo / module_path(row["test_module"])
        if not path.is_file():
            raise StaticError(f"test file missing: {row['test_module']}")
        payload = path.read_text(encoding="utf-8")
        found = set(IMPORT_RE.findall(payload))
        checks = re.findall(r"(?m)^\s*#check\s+@?([^\s(]+)", payload)
        check_count = len(checks)
        recorded = set(filter(None, row["imported_modules"].split(";")))
        if found != recorded or len(found) != int(row["imports"]) or check_count != int(row["checks"]):
            raise StaticError(f"test import ledger differs: {row['test_module']}")
        if row["kind"] == "canonical-only" and (found & owners or not found <= canonical):
            raise StaticError(f"canonical-only test crosses boundary: {row['test_module']}")
        if row["kind"] == "old-path-only" and (len(found) != 1 or not found <= owners):
            raise StaticError(f"old-path-only test differs: {row['test_module']}")
        if row["kind"] == "canonical-only":
            canonical_checks.extend(checks)
        elif row["kind"] == "old-path-only":
            old_checks.extend(checks)
    if len(canonical_checks) != 895 or len(set(canonical_checks)) != 895:
        raise StaticError("canonical-only check names must be 895 and duplicate-free")
    if set(canonical_checks) != relocated:
        raise StaticError("canonical-only checks are not exactly the 895 relocated names")
    if len(old_checks) != 949 or len(set(old_checks)) != 949 or set(old_checks) != public:
        raise StaticError("old-path-only checks are not exactly the 949 selected public names")


def check_sources_and_graph(repo: Path, canonical: set[str], reusable: set[str], owners: set[str]) -> None:
    sys.path.insert(0, str(repo / "tools/architecture"))
    from generate_baseline import remove_lean_comments
    files = {".".join(p.relative_to(repo).with_suffix("").parts): p for p in (repo / "NumStability").rglob("*.lean")}
    graph = {m: set(IMPORT_RE.findall(p.read_text(encoding="utf-8"))) for m, p in files.items()}
    missing = sorted({t for targets in graph.values() for t in targets if t.startswith("NumStability.") and t not in files})
    if missing:
        raise StaticError(f"unresolved project import: {missing[0]}")
    state: dict[str, int] = {}
    stack: list[str] = []
    def visit(module: str) -> None:
        if state.get(module) == 2:
            return
        if state.get(module) == 1:
            raise StaticError("import cycle: " + " -> ".join(stack[stack.index(module):] + [module]))
        state[module] = 1; stack.append(module)
        for target in graph[module]:
            if target in graph: visit(target)
        stack.pop(); state[module] = 2
    for module in sorted(graph): visit(module)
    def closure(module: str) -> set[str]:
        seen: set[str] = set(); todo = [module]
        while todo:
            for target in graph.get(todo.pop(), set()):
                if target not in seen:
                    seen.add(target); todo.append(target)
        return seen
    reusable_in_place = {"NumStability.Algorithms.CondEstimation"}
    historical_facades = owners - reusable_in_place
    for module in canonical | reusable_in_place:
        reached = closure(module)
        if reached & historical_facades:
            raise StaticError(f"canonical-to-historical reachability: {module} -> {sorted(reached & historical_facades)[0]}")
    for module in reusable | reusable_in_place:
        source = sorted(x for x in closure(module) if x.startswith("NumStability.Source."))
        if source:
            raise StaticError(f"reusable-to-Source reachability: {module} -> {source[0]}")
    for module in canonical | owners:
        payload = (repo / module_path(module)).read_text(encoding="utf-8")
        uncommented = remove_lean_comments(payload)
        if PLACEHOLDER_RE.search(uncommented) or AXIOM_RE.search(uncommented):
            raise StaticError(f"placeholder/axiom in {module}")
        if "/-!" not in payload:
            raise StaticError(f"missing module docstring: {module}")


def main() -> int:
    script = Path(__file__).resolve()
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=script.parents[4])
    parser.add_argument("--candidate", type=Path, default=Path("benchmark-results/W10-candidate.tsv"))
    parser.add_argument("--write-routes", action="store_true")
    args = parser.parse_args()
    repo = args.repo_root.resolve()
    candidate = args.candidate if args.candidate.is_absolute() else repo / args.candidate
    delivery = repo / "docs/architecture/deliveries/W10"
    routes, canonical, reusable = check_routes(repo, delivery, candidate, args.write_routes)
    owners = {r["owner_module"] for r in routes}
    check_retention(delivery, routes)
    check_tests(repo, delivery, canonical, owners)
    check_sources_and_graph(repo, canonical, reusable, owners)
    print("W10 static checks passed: 1,029 declarations, 134 retained (132 private-closure plus 2 full-graph re-entry hazards), 895 relocated, 96 canonical modules (95 declaration owners plus 1 Source wrapper), 135 tests, zero cycles, zero reusable-to-Source, and zero canonical-to-historical reachability")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (StaticError, OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
