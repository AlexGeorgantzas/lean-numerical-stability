#!/usr/bin/env python3
"""Static, isolation, facade, and Source-boundary audit for W04."""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
BRANCH = "codex/reorg-2026-08-w04-ch21-underdetermined"
TEST_PREFIX = "NumStabilityTest/Reorganization/W04/"
DELIVERY_PREFIX = "docs/architecture/deliveries/W04/"
IMPORT_RE = re.compile(
    r"(?m)^(?:public\s+|private\s+)?import\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
)
DECL_RE = re.compile(
    r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom)\s+"
)
PLACEHOLDER_RE = re.compile(r"(?m)\b(?:sorry|admit)\b|^\s*axiom\s+")


class StaticError(RuntimeError):
    pass


def git(root: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        text=True,
        encoding="utf-8",
    )
    if result.returncode:
        raise StaticError(result.stderr.strip())
    return result.stdout.strip()


def module_for_path(relative: Path) -> str:
    return ".".join(relative.with_suffix("").parts)


def path_for_module(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def cycle_in(graph: dict[str, set[str]]) -> list[str] | None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(node: str):
        if state.get(node) == 2:
            return None
        if state.get(node) == 1:
            return stack[stack.index(node):] + [node]
        state[node] = 1
        stack.append(node)
        for target in sorted(graph.get(node, ())):
            if target in graph:
                found = visit(target)
                if found:
                    return found
        stack.pop()
        state[node] = 2
        return None

    for node in sorted(graph):
        found = visit(node)
        if found:
            return found
    return None


def reachability_witness(
    start: str,
    graph: dict[str, set[str]],
    target,
) -> list[str] | None:
    queue = [(start, [start])]
    seen = {start}
    while queue:
        node, path = queue.pop(0)
        for child in sorted(graph.get(node, ())):
            if target(child):
                return path + [child]
            if child not in seen:
                seen.add(child)
                queue.append((child, path + [child]))
    return None


def main() -> int:
    sys.setrecursionlimit(10_000)
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    control = args.control_root.resolve()
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    contract = json.loads((phase / "branches/B0008.json").read_text(encoding="utf-8"))
    if (
        contract.get("status") != "active"
        or contract.get("base_sha") != BASE
        or contract.get("branch_name") != BRANCH
        or contract.get("operator_ids") != ["codex-remote"]
    ):
        raise StaticError("B0008 activation differs")
    with (phase / "selectors/W04.tsv").open(encoding="utf-8", newline="") as stream:
        selector_rows = list(csv.DictReader(stream, delimiter="\t"))
    owners = {row["module"]: row["path"] for row in selector_rows}
    if len(owners) != 29:
        raise StaticError("selector owner count differs")
    production_prefixes = tuple(
        item["path"] for item in contract["destination_prefixes"]
        if item["path"].startswith("NumStability/")
    )
    reusable_prefixes = tuple(
        path for path in production_prefixes
        if path.startswith("NumStability/Algorithms/")
    )

    all_sources = sorted(
        path for path in root.rglob("*.lean")
        if ".lake" not in path.parts and ".git" not in path.parts
    )
    source_by_module = {
        module_for_path(path.relative_to(root)): path for path in all_sources
    }
    imports = {}
    unresolved = []
    for module, path in source_by_module.items():
        found = set(IMPORT_RE.findall(path.read_text(encoding="utf-8")))
        imports[module] = found
        if (
            any(path.relative_to(root).as_posix().startswith(prefix) for prefix in production_prefixes)
            or path.relative_to(root).as_posix().startswith(TEST_PREFIX)
            or path.relative_to(root).as_posix() in owners.values()
        ):
            for target in sorted(found):
                if target.startswith(("NumStability.", "NumStabilityTest.")) and target not in source_by_module:
                    unresolved.append(f"{module} -> {target}")

    canonical_paths = sorted(
        path.relative_to(root).as_posix()
        for path in all_sources
        if any(path.relative_to(root).as_posix().startswith(prefix) for prefix in production_prefixes)
    )
    canonical_modules = {module_for_path(Path(path)) for path in canonical_paths}
    matrix_path = root / DELIVERY_PREFIX / "TEST_MATRIX.tsv"
    with matrix_path.open(encoding="utf-8", newline="") as stream:
        matrix = list(csv.DictReader(stream, delimiter="\t"))
    canonical_rows = [row for row in matrix if row["kind"] == "canonical"]
    compatibility_rows = [row for row in matrix if row["kind"] == "compatibility"]
    focused_rows = [row for row in matrix if row["kind"] == "focused"]
    matrix_errors = []
    matrix_paths = [row["test_path"] for row in matrix]
    disk_tests = {
        path.relative_to(root).as_posix()
        for path in (root / "NumStabilityTest/Reorganization/W04").rglob("*.lean")
    }
    if len(matrix) != 124 or len(set(matrix_paths)) != 124:
        matrix_errors.append("TEST_MATRIX.tsv must contain 124 unique test rows")
    if set(matrix_paths) != disk_tests:
        matrix_errors.append(
            f"matrix/disk test mismatch: missing={sorted(disk_tests-set(matrix_paths))}, "
            f"stale={sorted(set(matrix_paths)-disk_tests)}"
        )
    if {row["import_modules"] for row in canonical_rows} != canonical_modules:
        matrix_errors.append("canonical matrix/module set mismatch")
    if len(canonical_rows) != len(canonical_modules):
        matrix_errors.append("canonical matrix rows are not one-to-one")
    if {row["import_modules"] for row in compatibility_rows} != set(owners):
        matrix_errors.append("compatibility owner set mismatch")
    if len(compatibility_rows) != 29:
        matrix_errors.append("compatibility row count is not 29")
    isolation_errors = []
    for row in matrix:
        test = root / Path(row["test_path"])
        if not row["test_path"].startswith(TEST_PREFIX) or not test.is_file():
            isolation_errors.append(f"missing/outside test {row['test_path']}")
            continue
        actual = IMPORT_RE.findall(test.read_text(encoding="utf-8"))
        expected = row["import_modules"].split(",") if row["import_modules"] else []
        if actual != expected:
            isolation_errors.append(
                f"{row['test_path']}: imports {actual}, expected {expected}"
            )
        if row["kind"] in {"canonical", "compatibility"} and len(actual) != 1:
            isolation_errors.append(f"{row['test_path']}: isolated test has {len(actual)} imports")
        checked = set(re.findall(r"(?m)^#check\s+([^\s]+)\s*$", test.read_text(encoding="utf-8")))
        representatives = set() if row["representatives"] == "-" else set(
            row["representatives"].split(",")
        )
        if checked != representatives:
            isolation_errors.append(
                f"{row['test_path']}: #checks {sorted(checked)}, "
                f"expected {sorted(representatives)}"
            )

    required_focus = {
        "SpecificationsAndSolvers",
        "QRGivensModifiedGramSchmidt",
        "SeminormalEquationsPipeline",
        "PerturbationConditioningProjectorsRankStability",
        "Chapter21SourceEndpoints",
        "ProtectedAcceptedInterfaces",
        "ProtectedW90Consumers",
        "ProtectedW90Dependencies",
        "IntegratorCanonicalRetarget",
        "RetainedPrivateClosure",
        "ReusableUnderdeterminedApi",
    }
    actual_focus = {Path(row["test_path"]).stem for row in focused_rows}
    if actual_focus != required_focus:
        matrix_errors.append(
            f"focused areas differ: missing={sorted(required_focus-actual_focus)}, extra={sorted(actual_focus-required_focus)}"
        )
    protected = {
        "NumStability.Algorithms.RankOneUpdate",
        "NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation",
        "NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec",
        "NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic",
        "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic",
        "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation",
        "NumStability.Source.Higham.Chapter20.Lemma11",
        "NumStability.Source.Higham.Chapter20.Theorem08",
        "NumStability.Analysis.MatrixAlgebra",
        "NumStability.FloatingPoint.Model",
        "NumStability.Source.Higham.Chapter19.Core",
        "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve",
    }
    focused_imports = {
        module for row in focused_rows for module in row["import_modules"].split(",")
    }
    if not protected.issubset(focused_imports):
        matrix_errors.append(f"protected focused imports missing: {sorted(protected-focused_imports)}")

    local_graph = {
        module: {target for target in targets if target in source_by_module}
        for module, targets in imports.items()
    }
    generated_graph = {
        module: {target for target in imports[module] if target in canonical_modules}
        for module in canonical_modules
    }
    cycle = cycle_in(generated_graph)
    full_cycle = cycle_in(local_graph)
    canonical_facade_witnesses = []
    reusable_source_witnesses = []
    reusable_facade_witnesses = []
    tolerated_source_facade_witnesses = []
    unexpected_source_facade_witnesses = []
    owner_set = set(owners)
    for module in sorted(canonical_modules):
        for target in sorted(local_graph.get(module, ()) & owner_set):
            canonical_facade_witnesses.append(f"{module} -> {target}")
    reusable_modules = {
        module_for_path(Path(path)) for path in canonical_paths
        if any(path.startswith(prefix) for prefix in reusable_prefixes)
    }
    for module in sorted(reusable_modules):
        witness = reachability_witness(
            module, local_graph, lambda item: item.startswith("NumStability.Source.")
        )
        if witness:
            reusable_source_witnesses.append(" -> ".join(witness))
        witness = reachability_witness(module, local_graph, lambda item: item in owner_set)
        if witness:
            reusable_facade_witnesses.append(" -> ".join(witness))
    allowed_source_facade_edges = {
        (
            "NumStability.Analysis.Perturbation.LeastSquares.Wedin",
            "NumStability.Algorithms.Underdetermined.UnderdeterminedSpec",
        ),
        (
            "NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError",
            "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve",
        ),
    }
    for module in sorted(canonical_modules - reusable_modules):
        witness = reachability_witness(module, local_graph, lambda item: item in owner_set)
        if not witness:
            continue
        rendered = " -> ".join(witness)
        edges = set(zip(witness, witness[1:]))
        if edges & allowed_source_facade_edges:
            tolerated_source_facade_witnesses.append(rendered)
        else:
            unexpected_source_facade_witnesses.append(rendered)

    retention_path = root / DELIVERY_PREFIX / "RETENTION.tsv"
    with retention_path.open(encoding="utf-8", newline="") as stream:
        retention_rows = [
            row for row in csv.DictReader(
                (line for line in stream if not line.startswith("format\t")),
                delimiter="\t",
            )
        ]
    facade_errors = []
    if len(retention_rows) != 29 or {row["historical_module"] for row in retention_rows} != owner_set:
        facade_errors.append("RETENTION.tsv owner set/count differs")
    for row in retention_rows:
        path = root / row["historical_path"]
        text = path.read_text(encoding="utf-8")
        has_declaration = DECL_RE.search(text) is not None
        if row["facade_kind"] == "pure_import_shim" and has_declaration:
            facade_errors.append(f"pure facade contains a declaration: {row['historical_module']}")
        if row["facade_kind"] == "declaration_bearing" and not has_declaration:
            facade_errors.append(f"retained facade lacks declarations: {row['historical_module']}")
    if Counter(row["facade_kind"] for row in retention_rows) != Counter(
        pure_import_shim=13, declaration_bearing=16
    ):
        facade_errors.append("facade-kind partition differs from 13 pure / 16 declaration-bearing")
    numeric_columns = (
        "selected", "private", "retained_public", "retained_private",
        "retained_total", "relocated", "reusable", "source",
    )
    retention_totals = {
        column: sum(int(row[column]) for row in retention_rows)
        for column in numeric_columns
    }
    expected_retention_totals = {
        "selected": 1238,
        "private": 40,
        "retained_public": 180,
        "retained_private": 40,
        "retained_total": 220,
        "relocated": 1018,
        "reusable": 387,
        "source": 631,
    }
    if retention_totals != expected_retention_totals:
        facade_errors.append(
            f"RETENTION.tsv arithmetic differs: {retention_totals}"
        )

    routes_path = root / DELIVERY_PREFIX / "DECLARATION_ROUTES.tsv"
    with routes_path.open(encoding="utf-8", newline="") as stream:
        route_rows = list(csv.DictReader(
            (line for line in stream if not line.startswith("format\t")),
            delimiter="\t",
        ))
    route_errors = []
    if len(route_rows) != 1238 or len({row["declaration"] for row in route_rows}) != 1238:
        route_errors.append("declaration route ledger is not 1,238 unique declarations")
    if Counter(row["decision"] for row in route_rows) != Counter(
        relocate_reusable=387, relocate_source=631, retain_historical=220
    ):
        route_errors.append("declaration route decision partition differs")
    if Counter(row["kind"] for row in route_rows) != Counter(
        theorem=904, definition=283, inductive=17, constructor=17, recursor=17
    ):
        route_errors.append("declaration route kind partition differs")
    if Counter(row["visibility"] for row in route_rows) != Counter(public=1198, private=40):
        route_errors.append("declaration route visibility partition differs")
    moved_private = [
        row["declaration"] for row in route_rows
        if row["visibility"] == "private" and row["decision"] != "retain_historical"
    ]
    if moved_private:
        route_errors.append(f"private declarations moved: {moved_private}")

    audited_paths = canonical_paths + list(owners.values()) + [
        row["test_path"] for row in matrix
    ]
    placeholder_paths = []
    missing_docs = []
    unsorted_imports = []
    for relative in audited_paths:
        path = root / relative
        text = path.read_text(encoding="utf-8")
        if PLACEHOLDER_RE.search(text):
            placeholder_paths.append(relative)
        actual_imports = IMPORT_RE.findall(text)
        if actual_imports != sorted(actual_imports):
            unsorted_imports.append(relative)
        if relative in canonical_paths and "/-!" not in text:
            missing_docs.append(relative)

    fold = defaultdict(list)
    for relative in canonical_paths + [row["test_path"] for row in matrix]:
        fold[relative.casefold()].append(relative)
    casefold_collisions = [items for items in fold.values() if len(items) > 1]
    result = {
        "canonical_modules": len(canonical_modules),
        "canonical_tests": len(canonical_rows),
        "compatibility_tests": len(compatibility_rows),
        "focused_tests": len(focused_rows),
        "matrix_errors": matrix_errors,
        "isolation_errors": isolation_errors,
        "unresolved_imports": unresolved,
        "canonical_cycle": cycle or [],
        "full_import_cycle": full_cycle or [],
        "canonical_to_historical_facade": canonical_facade_witnesses,
        "reusable_to_source": reusable_source_witnesses,
        "reusable_to_historical_facade": reusable_facade_witnesses,
        "tolerated_source_to_historical_count": len(tolerated_source_facade_witnesses),
        "unexpected_source_to_historical_facade": unexpected_source_facade_witnesses,
        "retention_totals": retention_totals,
        "route_errors": route_errors,
        "placeholder_or_axiom_paths": placeholder_paths,
        "missing_module_docs": missing_docs,
        "unsorted_import_paths": unsorted_imports,
        "facade_shape_errors": facade_errors,
        "casefold_collisions": casefold_collisions,
    }
    print(json.dumps(result, indent=2))
    failures = [
        value for key, value in result.items()
        if key not in {
            "canonical_modules", "canonical_tests", "compatibility_tests",
            "focused_tests", "tolerated_source_to_historical_count", "retention_totals",
        }
        and value
    ]
    if failures:
        raise StaticError("W04 static audit failed")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, StaticError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
