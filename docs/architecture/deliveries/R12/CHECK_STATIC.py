#!/usr/bin/env python3
"""Static routing, preservation, aggregate, test, and import-graph audits for R12."""

from __future__ import annotations

import csv
import io
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
DELIVERY = ROOT / "docs/architecture/deliveries/R12"
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
CONTROL = "5e075b947a63e84c784afecd00e1f130e21ea659"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion"
ROUTES_PATH = f"{PHASE}/branches/B0004-declaration-routes.tsv"
PRIVATE_PATH = f"{PHASE}/branches/B0004-private-closure.tsv"
PRIVATE_MAP_PATH = f"{PHASE}/branches/B0004-private-normalization.tsv"
TEST_PLAN_PATH = f"{PHASE}/branches/B0004-test-plan.tsv"
IMPORT_RE = re.compile(
    r"(?m)^import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$")
DECL_RE = re.compile(
    r"(?m)^(?:noncomputable\s+)?(theorem|def)\s+(?:\n\s*)?"
    r"([A-Za-z_][A-Za-z0-9_'.]*)")
CHECK_RE = re.compile(r"(?m)^#check\s+@([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
ATTRIBUTE_RE = re.compile(r"(?m)^\s*(?:@\[|attribute\b)")
OLD_MODULES = {
    "NumStability.Source.Higham.Chapter13.Equation23",
    "NumStability.Source.Higham.Chapter13.Equation25",
    "NumStability.Source.Higham.Chapter13.Table01",
}
DESTINATIONS = {
    "NumStability.Source.Higham.Chapter13.Equation23.ProductBounds.PointRow",
    "NumStability.Source.Higham.Chapter13.Equation25.BackwardError.Bounds",
    "NumStability.Source.Higham.Chapter13.Equation25.PartitionedComputation.Implementation1",
    "NumStability.Source.Higham.Chapter13.Table01.BackwardErrorBounds.Endpoints",
    "NumStability.Source.Higham.Chapter13.Table01.DiagonalDominance.Bounds",
    "NumStability.Source.Higham.Chapter13.Table01.ProductTransfers.Families",
}
AGGREGATES = {
    "NumStability.Source.Higham.Chapter13.Equation23": [
        "NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth",
        "NumStability.Source.Higham.Chapter13.Equation23.ProductBounds.PointRow",
    ],
    "NumStability.Source.Higham.Chapter13.Equation25": [
        "NumStability.Source.Higham.Chapter13.Equation25.BackwardError.Bounds",
        "NumStability.Source.Higham.Chapter13.Equation25.Factorization",
        "NumStability.Source.Higham.Chapter13.Equation25.Families",
        "NumStability.Source.Higham.Chapter13.Equation25.PartitionedComputation.Implementation1",
    ],
    "NumStability.Source.Higham.Chapter13.Table01": [
        "NumStability.Source.Higham.Chapter13.Table01.BackwardErrorBounds.Endpoints",
        "NumStability.Source.Higham.Chapter13.Table01.DiagonalDominance.Bounds",
        "NumStability.Source.Higham.Chapter13.Table01.Families",
        "NumStability.Source.Higham.Chapter13.Table01.ProductTransfers.Families",
    ],
}


class StaticError(RuntimeError):
    pass


def git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)


def read_tsv_bytes(payload: bytes) -> list[dict[str, str]]:
    return list(csv.DictReader(io.StringIO(payload.decode("utf-8")), delimiter="\t"))


def read_tsv(path: Path) -> list[dict[str, str]]:
    return read_tsv_bytes(path.read_bytes())


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def module_name(path: Path) -> str:
    return path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def remove_comments(text: str) -> str:
    out: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if not in_string and pair == "/-":
            depth = 1
            index += 2
            continue
        if not in_string and pair == "--":
            newline = text.find("\n", index)
            index = len(text) if newline < 0 else newline
            continue
        if char == '"' and (index == 0 or text[index - 1] != "\\"):
            in_string = not in_string
        out.append(char)
        index += 1
    if depth:
        raise StaticError("unterminated Lean comment")
    return "".join(out)


def commands(text: str) -> dict[str, tuple[str, str]]:
    matches = list(DECL_RE.finditer(text))
    result: dict[str, tuple[str, str]] = {}
    namespace_end = text.rfind("\nend NumStability")
    if namespace_end < 0:
        namespace_end = len(text)
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else namespace_end
        normalized = re.sub(r"\s+", " ", remove_comments(text[match.start():end])).strip()
        name = match.group(2)
        if name in result:
            raise StaticError(f"duplicate declaration command: {name}")
        result[name] = (match.group(1), normalized)
    return result


def exact_routes() -> list[dict[str, str]]:
    control = git_bytes(CONTROL, ROUTES_PATH)
    if (DELIVERY / "DECLARATION_ROUTES.tsv").read_bytes() != control:
        raise StaticError("DECLARATION_ROUTES.tsv is not byte-identical to B0004")
    routes = read_tsv_bytes(control)
    if len(routes) != 34 or len({row["baseline_declaration_name"] for row in routes}) != 34:
        raise StaticError("route cardinality/uniqueness differs")
    if Counter(row["visibility"] for row in routes) != {"public": 34}:
        raise StaticError("visibility roster differs")
    if Counter(row["kind"] for row in routes) != {"theorem": 31, "definition": 3}:
        raise StaticError("kind roster differs")
    if Counter(row["baseline_owner_module"] for row in routes) != {
        "NumStability.Source.Higham.Chapter13.Equation23": 3,
        "NumStability.Source.Higham.Chapter13.Equation25": 3,
        "NumStability.Source.Higham.Chapter13.Table01": 28,
    }:
        raise StaticError("owner split differs")
    if Counter(row["destination_module"] for row in routes) != {
        "NumStability.Source.Higham.Chapter13.Equation23.ProductBounds.PointRow": 3,
        "NumStability.Source.Higham.Chapter13.Equation25.BackwardError.Bounds": 2,
        "NumStability.Source.Higham.Chapter13.Equation25.PartitionedComputation.Implementation1": 1,
        "NumStability.Source.Higham.Chapter13.Table01.BackwardErrorBounds.Endpoints": 8,
        "NumStability.Source.Higham.Chapter13.Table01.DiagonalDominance.Bounds": 15,
        "NumStability.Source.Higham.Chapter13.Table01.ProductTransfers.Families": 5,
    }:
        raise StaticError("destination split differs")
    return routes


def verify_private() -> None:
    if (DELIVERY / "PRIVATE_CLOSURE.tsv").read_bytes() != git_bytes(CONTROL, PRIVATE_PATH):
        raise StaticError("private closure differs from frozen header-only artifact")
    if git_bytes(CONTROL, PRIVATE_MAP_PATH) != (
        b"old_private\tnew_private\tdestination_module\n"):
        raise StaticError("private normalization is not exact header-only")
    if read_tsv(DELIVERY / "PRIVATE_CLOSURE.tsv"):
        raise StaticError("R12 unexpectedly has private closure rows")


def verify_declarations(routes: list[dict[str, str]]) -> None:
    by_destination: dict[str, set[str]] = {}
    by_owner: dict[str, set[str]] = {}
    for row in routes:
        short = row["baseline_declaration_name"].removeprefix("NumStability.")
        by_destination.setdefault(row["destination_module"], set()).add(short)
        by_owner.setdefault(row["baseline_owner_module"], set()).add(short)

    route_by_short = {
        row["baseline_declaration_name"].removeprefix("NumStability."): row
        for row in routes
    }
    baseline: dict[str, tuple[str, str]] = {}
    baseline_order: dict[str, list[str]] = {}
    for owner in OLD_MODULES:
        source = git_bytes(BASE, owner.replace(".", "/") + ".lean").decode("utf-8")
        if ATTRIBUTE_RE.search(remove_comments(source)):
            raise StaticError(f"unexpected declaration attribute in C0001 owner: {owner}")
        found = commands(source)
        baseline_order[owner] = list(found)
        baseline.update(found)
    candidate: dict[str, tuple[str, str]] = {}
    for destination in DESTINATIONS:
        source = module_path(destination).read_text(encoding="utf-8")
        if ATTRIBUTE_RE.search(remove_comments(source)):
            raise StaticError(f"unexpected declaration attribute in destination: {destination}")
        found = commands(source)
        if set(found) != by_destination[destination]:
            raise StaticError(f"destination declaration roster differs: {destination}")
        owners = {
            route_by_short[name]["baseline_owner_module"] for name in found
        }
        if len(owners) != 1:
            raise StaticError(f"destination owner roster differs: {destination}")
        owner = owners.pop()
        expected_order = [
            name for name in baseline_order[owner]
            if name in route_by_short
            and route_by_short[name]["destination_module"] == destination
        ]
        if list(found) != expected_order:
            raise StaticError(f"physical declaration order differs: {destination}")
        for name, command in found.items():
            if name in candidate:
                raise StaticError(f"candidate declaration duplicated: {name}")
            candidate[name] = command

    expected = set().union(*by_destination.values())
    if set(candidate) != expected or not expected <= set(baseline):
        raise StaticError("candidate/baseline declaration union differs")
    for name in expected:
        if candidate[name] != baseline[name]:
            raise StaticError(f"declaration command changed: NumStability.{name}")

    retention = read_tsv(DELIVERY / "RETENTION.tsv")
    if len(retention) != 34:
        raise StaticError("retention row count differs")
    retention_by_name = {row["declaration"]: row for row in retention}
    if len(retention_by_name) != 34:
        raise StaticError("retention declaration uniqueness differs")
    for route in routes:
        row = retention_by_name.get(route["baseline_declaration_name"])
        if row is None:
            raise StaticError("retention name roster differs")
        if row["retention"] != "public_name_preserved" or row[
            "candidate_occurrences"] != "present_exactly_once":
            raise StaticError("retention decision differs")
        if row["baseline_owner"] != route["baseline_owner_module"] or row[
            "destination_module"] != route["destination_module"]:
            raise StaticError(
                f"retention route differs: {route['baseline_declaration_name']}"
            )


def verify_aggregates() -> None:
    for module, expected in AGGREGATES.items():
        text = module_path(module).read_text(encoding="utf-8")
        imports = IMPORT_RE.findall(text)
        if imports != expected or imports != sorted(set(imports)):
            raise StaticError(f"aggregate imports differ: {module}")
        if commands(text):
            raise StaticError(f"aggregate contains declarations: {module}")
        if "/-!" not in text or "declares nothing" not in text:
            raise StaticError(f"aggregate documentation differs: {module}")


def project_graph() -> tuple[dict[str, Path], dict[str, list[str]]]:
    paths = [ROOT / "NumStability.lean", *sorted((ROOT / "NumStability").rglob("*.lean"))]
    modules = {module_name(path): path for path in paths}
    graph: dict[str, list[str]] = {}
    for module, path in modules.items():
        imports = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        missing = [item for item in imports if item.startswith("NumStability") and item not in modules]
        if missing:
            raise StaticError(f"unresolved project import in {module}: {missing[0]}")
        graph[module] = [item for item in imports if item in modules]
    return modules, graph


def verify_graph() -> None:
    modules, graph = project_graph()
    state: dict[str, int] = {}

    def visit(module: str, stack: list[str]) -> None:
        mark = state.get(module, 0)
        if mark == 1:
            raise StaticError("import cycle: " + " -> ".join(stack + [module]))
        if mark == 2:
            return
        state[module] = 1
        for imported in graph[module]:
            visit(imported, stack + [module])
        state[module] = 2

    for module in modules:
        visit(module, [])

    for start in DESTINATIONS:
        seen: set[str] = set()
        pending = [start]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            pending.extend(graph[module])
        overlap = seen & OLD_MODULES
        if overlap:
            raise StaticError(f"canonical leaf reaches historical owner: {start}: {sorted(overlap)}")


def verify_tests(routes: list[dict[str, str]]) -> None:
    plan = read_tsv_bytes(git_bytes(CONTROL, TEST_PLAN_PATH))
    matrix = read_tsv(DELIVERY / "TEST_MATRIX.tsv")
    if len(plan) != 26 or len(matrix) != 26:
        raise StaticError("test-plan/matrix cardinality differs")
    if Counter(row["test_class"] for row in plan) != {
        "canonical_only": 6, "focused": 6, "old_only": 3,
        "protected_consumer": 11,
    }:
        raise StaticError("frozen test class counts differ")

    by_destination: dict[str, list[str]] = {}
    by_owner: dict[str, list[str]] = {}
    for row in routes:
        name = row["baseline_declaration_name"]
        by_destination.setdefault(row["destination_module"], []).append(name)
        by_owner.setdefault(row["baseline_owner_module"], []).append(name)
    for names in [*by_destination.values(), *by_owner.values()]:
        names.sort()

    expected_rows: dict[tuple[str, str], dict[str, str]] = {}
    all_test_modules: list[str] = []
    folder = {
        "canonical_only": "Canonical", "focused": "Focused",
        "old_only": "OldOnly", "protected_consumer": "Consumer",
    }
    for row in plan:
        klass, target = row["test_class"], row["target"]
        stem = target.removeprefix("NumStability.").replace(".", "")
        test_module = f"NumStabilityTest.Reorganization.R12.{folder[klass]}.{stem}"
        expected_rows[(klass, target)] = {"test_module": test_module}
        all_test_modules.append(test_module)

    observed_keys = {
        (row["kind"].replace("-", "_"), row["imported_modules"]): row
        for row in matrix
    }
    if set(observed_keys) != set(expected_rows):
        raise StaticError("TEST_MATRIX does not map one-to-one to frozen plan")

    consumer_targets = set()
    for (klass, target), matrix_row in observed_keys.items():
        test_module = matrix_row["test_module"]
        if test_module != expected_rows[(klass, target)]["test_module"]:
            raise StaticError(f"test module name differs: {target}")
        text = module_path(test_module).read_text(encoding="utf-8")
        if IMPORT_RE.findall(text) != [target]:
            raise StaticError(f"test imports are not isolated: {test_module}")
        checks = CHECK_RE.findall(text)
        if klass == "canonical_only":
            expected_checks = by_destination[target]
        elif klass == "focused":
            expected_checks = by_destination[target][:6]
        elif klass == "old_only":
            expected_checks = by_owner[target]
        else:
            expected_checks = []
            consumer_targets.add(target)
        if checks != expected_checks:
            raise StaticError(f"test check roster differs: {test_module}")
        if matrix_row["imports"] != "1" or int(matrix_row["checks"]) != len(checks):
            raise StaticError(f"test matrix counts differ: {test_module}")

    for module in consumer_targets:
        path = module.replace(".", "/") + ".lean"
        if module_path(module).read_bytes() != git_bytes(BASE, path):
            raise StaticError(f"protected consumer changed: {module}")

    all_text = module_path("NumStabilityTest.Reorganization.R12.All").read_text(
        encoding="utf-8")
    all_imports = IMPORT_RE.findall(all_text)
    if all_imports != sorted(all_test_modules) or len(set(all_imports)) != 26:
        raise StaticError("R12.All import roster/order differs")
    if commands(all_text):
        raise StaticError("R12.All is not declaration-free")


def verify_placeholders() -> None:
    paths = [module_path(module) for module in DESTINATIONS | OLD_MODULES]
    paths += sorted((ROOT / "NumStabilityTest/Reorganization/R12").rglob("*.lean"))
    pattern = re.compile(
        r"\b(sorry|admit)\b|^\s*(?:axiom|constant)\b", re.MULTILINE
    )
    for path in paths:
        if pattern.search(remove_comments(path.read_text(encoding="utf-8"))):
            raise StaticError(f"placeholder found: {path.relative_to(ROOT)}")


def main() -> None:
    routes = exact_routes()
    verify_private()
    verify_declarations(routes)
    verify_aggregates()
    verify_graph()
    verify_tests(routes)
    verify_placeholders()
    print(
        "R12 static OK: 34 exact public commands; 0 private; 6 leaves; "
        "3 complete aggregates; 26 isolated tests; no cycles/old-owner reachability"
    )


if __name__ == "__main__":
    try:
        main()
    except StaticError as error:
        print(f"R12 static audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
