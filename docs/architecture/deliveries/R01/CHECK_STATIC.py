#!/usr/bin/env python3
"""Static routing, wrapper, test-ledger, and import-closure checks for R01."""

from __future__ import annotations

import csv
import hashlib
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

BASE = "b1b18772d80185ec08f49c818919558645c330a1"
ROOT = Path(__file__).resolve().parents[4]
DELIVERY = ROOT / "docs/architecture/deliveries/R01"
DELIVERY_HASHES = {
    "DECLARATION_ROUTES.tsv": "1493383A571EFFDECCD2DF5D5C8DF2657139B2BA140D271B0706C86D32397A52",
    "PRIVATE_CLOSURE.tsv": "CB19F5F3C66C56CE5F688E5E310D64713834635AFDFB77D7CB24DC1EC9D88598",
    "RETENTION.tsv": "CB3BA58A9E73987EEE2417A477E2A773D1F8DCF50E6FC347743F7282CBBA5EF7",
    "TEST_MATRIX.tsv": "FBBD752E77CC091A6919A54352E461265FC6401D45337BFD0C45B0DEA3AF8CCB",
}
FORBIDDEN_CHANGED_PREFIXES = (
    ".agents/", ".codex/", ".lake/", ".venv/", "benchmark-results/", "tmp/",
)
GENERATED_PARTS = {"__pycache__", ".DS_Store"}
GENERATED_SUFFIXES = {".olean", ".ilean", ".pyc", ".pyo", ".aux", ".log", ".out"}
IMPORT_RE = re.compile(r"(?m)^import\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$")
DECL_RE = re.compile(
    r"(?m)^(private\s+)?(?:noncomputable\s+)?(theorem|def)\s+([^\s({:]+)"
)
CHECK_RE = re.compile(r"(?m)^#check\s+([^\s]+)\s*$")
PRIVATE_NAME_RE = re.compile(r'approvedPrivateName\s+"([^"]+)"\s+"([^"]+)"')
UNSELECTED_CLOSURE = {
    "NumStability.higham17_22_exists_blockForm_spectralRadius_lt_one_of_forall_orbit_tendsto",
    "NumStability.higham17_22_sourceBlockForm_of_forall_orbit_tendsto",
}
PRIVATE_REVERSE_CHECKS = {
    "NumStability.eigenvector_one_of_maxGen_of_orbit_tendsto",
    "NumStability.finiteResidualSigma_le_diagonalizable_bound",
    "NumStability.maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto",
    "NumStability.residualSigmaTsum_le_diagonalizable_bound",
    "NumStability.residualSigmaTsum_le_diagonalizable_max_bound_direct",
    "NumStability.sigma_bound",
    "NumStability.singularErrorSourceTerm_norm_bound",
    "NumStability.stationaryDrazinFixedProjector_fixed_by_G",
    "NumStability.stationaryDrazinFixedProjector_idempotent",
    "NumStability.stationaryDrazinRangeProjector_commutes_with_G",
}
ROOT_AGGREGATE_CHECKS = {
    "NumStability.literal_norm_form_forward_bound",
    "NumStability.matPow_G_tendsto_oneEigenProjector_of_convergence",
    "NumStability.stationaryDrazinFixedProjector_idempotent",
}


class StaticError(RuntimeError):
    pass


def read_tsv(name: str) -> list[dict[str, str]]:
    with (DELIVERY / name).open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        raise StaticError(result.stdout + f"git {' '.join(args)} failed")
    return result.stdout


def verify_delivery_hashes() -> None:
    for name, expected in DELIVERY_HASHES.items():
        actual = sha256(DELIVERY / name)
        if actual != expected:
            raise StaticError(f"delivery hash differs: {name}: {actual}")


def verify_changed_paths() -> None:
    changed = {
        line.strip().replace("\\", "/")
        for line in git("diff", "--name-only", "--no-renames", BASE, "--").splitlines()
        if line.strip()
    }
    changed.update(
        line.strip().replace("\\", "/")
        for line in git("ls-files", "--others", "--exclude-standard").splitlines()
        if line.strip()
    )
    generated = sorted(
        path for path in changed
        if path.startswith(FORBIDDEN_CHANGED_PREFIXES)
        or set(path.split("/")) & GENERATED_PARTS
        or Path(path).suffix in GENERATED_SUFFIXES
    )
    if generated:
        raise StaticError(f"generated/private changed path: {generated[0]}")


def normalized_private_name(destination: str, old_name: str) -> str:
    marker = ".0."
    if not old_name.startswith("_private.") or marker not in old_name:
        raise StaticError(f"malformed baseline private name: {old_name}")
    declaration_name = old_name.split(marker, 1)[1]
    return f"_private.{destination}.0.{declaration_name}"


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def strip_comments(text: str) -> str:
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
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            out.append(char)
            if char == "\\" and index + 1 < len(text):
                out.append(text[index + 1])
                index += 2
            else:
                if char == '"':
                    in_string = False
                index += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            if end < 0:
                out.extend(" " * (len(text) - index))
                break
            out.extend(" " * (end - index))
            index = end
        else:
            out.append(char)
            if char == '"':
                in_string = True
            index += 1
    if depth:
        raise StaticError("unterminated block comment")
    return "".join(out)


def import_only(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8-sig")
    stripped = strip_comments(text)
    imports = set(IMPORT_RE.findall(stripped))
    residue = IMPORT_RE.sub("", stripped).strip()
    if residue:
        first = next((line.strip() for line in residue.splitlines() if line.strip()), residue[:80])
        raise StaticError(f"declaration-free module has command residue: {path.relative_to(ROOT)}: {first}")
    if "/-!" not in text:
        raise StaticError(f"module docstring missing: {path.relative_to(ROOT)}")
    return imports


def declaration_inventory(path: Path) -> list[tuple[str, str, str]]:
    stripped = strip_comments(path.read_text(encoding="utf-8-sig"))
    result = []
    for private, command, name in DECL_RE.findall(stripped):
        result.append(("private" if private else "public", "definition" if command == "def" else "theorem", name))
    return result


def import_graph() -> tuple[dict[str, Path], dict[str, set[str]]]:
    files = {module_name(path): path for path in (ROOT / "NumStability").rglob("*.lean")}
    graph = {
        module: set(IMPORT_RE.findall(path.read_text(encoding="utf-8-sig")))
        for module, path in files.items()
    }
    missing = sorted(
        target for targets in graph.values() for target in targets
        if target.startswith("NumStability.") and target not in files
    )
    if missing:
        raise StaticError(f"unresolved project import: {missing[0]}")
    return files, graph


def verify_acyclic(graph: dict[str, set[str]]) -> None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(module: str) -> None:
        if state.get(module) == 2:
            return
        if state.get(module) == 1:
            start = stack.index(module)
            raise StaticError("import cycle: " + " -> ".join(stack[start:] + [module]))
        state[module] = 1
        stack.append(module)
        for target in sorted(graph[module]):
            if target in graph:
                visit(target)
        stack.pop()
        state[module] = 2

    for module in sorted(graph):
        visit(module)


def historical_facades(files: dict[str, Path]) -> set[str]:
    result = set()
    for module, path in files.items():
        text = path.read_text(encoding="utf-8-sig")
        stripped = strip_comments(text)
        imports = IMPORT_RE.findall(stripped)
        residue = IMPORT_RE.sub("", stripped).strip()
        lower = text.lower()
        documented_as_historical = (
            "historical" in lower
            or "compatibility wrapper" in lower
            or "compatibility facade" in lower
        )
        if imports and not residue and documented_as_historical:
            result.add(module)
    return result


def closure(graph: dict[str, set[str]], root: str) -> set[str]:
    seen: set[str] = set()
    todo = [root]
    while todo:
        current = todo.pop()
        for target in graph.get(current, set()):
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def main() -> int:
    verify_delivery_hashes()
    verify_changed_paths()
    routes = read_tsv("DECLARATION_ROUTES.tsv")
    retention = read_tsv("RETENTION.tsv")
    private_closure = read_tsv("PRIVATE_CLOSURE.tsv")
    matrix = read_tsv("TEST_MATRIX.tsv")
    if len(routes) != 243 or len({row["baseline_declaration_name"] for row in routes}) != 243:
        raise StaticError(f"route count differs: {len(routes)}")
    if Counter(row["visibility"] for row in routes) != Counter(public=233, private=10):
        raise StaticError("route visibility counts differ")
    if Counter(row["kind"] for row in routes) != Counter(theorem=215, definition=28):
        raise StaticError("route kind counts differ")

    owners = {row["baseline_owner_module"] for row in routes}
    destinations = {row["destination_module"] for row in routes}
    if (len(owners), len(destinations)) != (16, 20):
        raise StaticError("owner/destination cardinality differs")
    routes_by_owner: dict[str, list[dict[str, str]]] = defaultdict(list)
    routes_by_destination: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in routes:
        routes_by_owner[row["baseline_owner_module"]].append(row)
        routes_by_destination[row["destination_module"]].append(row)
    route_by_name = {row["baseline_declaration_name"]: row for row in routes}

    for owner, rows in routes_by_owner.items():
        path = module_path(owner)
        imports = import_only(path)
        expected = {row["destination_module"] for row in rows}
        if imports != expected:
            raise StaticError(f"historical wrapper imports differ: {owner}: {sorted(imports ^ expected)}")

    if len(retention) != 243 or len({row["baseline_declaration_name"] for row in retention}) != 243:
        raise StaticError("retention ledger cardinality differs")
    if Counter(row["retention_action"] for row in retention) != Counter(
        public_name_preserved=233, approved_private_normalization=10
    ) or Counter(row["expected_status"] for row in retention) != Counter(
        present_exactly_once=243
    ):
        raise StaticError("retention ledger actions differ")
    for route, retained in zip(routes, retention, strict=True):
        private = route["visibility"] == "private"
        expected_name = (
            normalized_private_name(route["destination_module"], route["baseline_declaration_name"])
            if private else route["baseline_declaration_name"]
        )
        expected = {
            "baseline_owner_module": route["baseline_owner_module"],
            "baseline_declaration_name": route["baseline_declaration_name"],
            "visibility": route["visibility"],
            "kind": route["kind"],
            "destination_module": route["destination_module"],
            "expected_candidate_name": expected_name,
            "retention_action": "approved_private_normalization" if private else "public_name_preserved",
            "expected_status": "present_exactly_once",
        }
        if retained != expected:
            raise StaticError(f"retention row differs: {route['baseline_declaration_name']}")
    private_map = {
        row["baseline_declaration_name"]: row["expected_candidate_name"]
        for row in retention if row["visibility"] == "private"
    }
    if len(private_map) != 10 or len(set(private_map.values())) != 10:
        raise StaticError("private normalization roster differs")
    for destination, rows in routes_by_destination.items():
        path = module_path(destination)
        if not path.is_file():
            raise StaticError(f"canonical destination missing: {destination}")
        if "/-!" not in path.read_text(encoding="utf-8-sig"):
            raise StaticError(f"canonical module docstring missing: {destination}")
        actual = declaration_inventory(path)
        expected = []
        for row in rows:
            full = private_map.get(row["baseline_declaration_name"], row["baseline_declaration_name"])
            expected.append((row["visibility"], row["kind"], full.rsplit(".", 1)[-1]))
        if Counter(actual) != Counter(expected):
            raise StaticError(
                f"physical declaration roster differs: {destination}: "
                f"expected={len(expected)} actual={len(actual)}"
            )

    reusable = {
        row["destination_module"] for row in routes
        if row["route_class"] == "reusable"
    }
    source = {
        row["destination_module"] for row in routes
        if row["route_class"] == "source"
    }
    if (len(reusable), len(source)) != (9, 11):
        raise StaticError(f"destination tier counts differ: {len(reusable)}/{len(source)}")
    algorithm_all = "NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.All"
    analysis_all = "NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All"
    results_all = "NumStability.Source.Higham.Chapter17.Results.All"
    results_series = "NumStability.Source.Higham.Chapter17.Results.Series"
    source_umbrella_owners = {
        owner for owner in owners
        if owner.startswith("NumStability.Source.Higham.Chapter17.Equation")
    }
    if len(source_umbrella_owners) != 6:
        raise StaticError("historical equation-umbrella roster differs")
    aggregate_members = {
        algorithm_all: {
            module for module in reusable if module.startswith("NumStability.Algorithms.")
        },
        analysis_all: {
            module for module in reusable if module.startswith("NumStability.Analysis.")
        },
        results_series: {
            row["destination_module"] for row in routes
            if row["baseline_owner_module"] in source_umbrella_owners
        },
        results_all: source | {results_series},
    }
    aggregate_paths = []
    for prefix in (
        ROOT / "NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence",
        ROOT / "NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence",
        ROOT / "NumStability/Source/Higham/Chapter17/Results",
    ):
        aggregate_paths.extend(prefix.rglob("All.lean"))
    series_path = ROOT / "NumStability/Source/Higham/Chapter17/Results/Series.lean"
    if series_path.is_file():
        aggregate_paths.append(series_path)
    actual_aggregates = {module_name(path) for path in aggregate_paths}
    if actual_aggregates != set(aggregate_members):
        raise StaticError(f"aggregate module roster differs: {sorted(actual_aggregates ^ set(aggregate_members))}")
    for path in aggregate_paths:
        module = module_name(path)
        text = path.read_text(encoding="utf-8-sig")
        ordered = IMPORT_RE.findall(strip_comments(text))
        expected = sorted(aggregate_members[module])
        if ordered != expected or len(ordered) != len(set(ordered)):
            raise StaticError(f"aggregate membership/order differs: {path.relative_to(ROOT)}")
        if import_only(path) != aggregate_members[module]:
            raise StaticError(f"aggregate imports differ: {path.relative_to(ROOT)}")

    files, graph = import_graph()
    verify_acyclic(graph)
    historical = owners
    canonical = destinations
    facades = historical_facades(files)
    for module in canonical:
        leaked = closure(graph, module) & historical
        if leaked:
            raise StaticError(f"canonical-to-historical reachability: {module} -> {sorted(leaked)[0]}")
    for module in reusable | {algorithm_all, analysis_all}:
        reached = closure(graph, module)
        source_leaks = sorted(target for target in reached if target.startswith("NumStability.Source."))
        if source_leaks:
            raise StaticError(f"reusable-to-Source reachability: {module} -> {source_leaks[0]}")
        leaked = reached & historical
        if leaked:
            raise StaticError(f"reusable-to-historical reachability: {module} -> {sorted(leaked)[0]}")
        facade = reached & facades
        if facade:
            raise StaticError(f"reusable-to-historical-facade reachability: {module} -> {sorted(facade)[0]}")

    if len(private_closure) != 42 or len({row["declaration"] for row in private_closure}) != 42:
        raise StaticError("private reverse-closure row count differs")
    if Counter(row["visibility"] for row in private_closure) != Counter(public=32, private=10):
        raise StaticError("private reverse-closure visibility counts differ")
    if Counter(row["closure_role"] for row in private_closure) != Counter(
        reverse_dependent=32, private_seed=10
    ):
        raise StaticError("private reverse-closure role counts differ")
    if Counter(row["selected_owner"] for row in private_closure) != Counter(yes=40, no=2):
        raise StaticError("private reverse-closure owner-selection counts differ")
    if {row["declaration"] for row in private_closure if row["visibility"] == "private"} != set(private_map):
        raise StaticError("private seed roster differs from approved normalization map")
    unselected = {
        row["declaration"] for row in private_closure if row["selected_owner"] == "no"
    }
    if unselected != UNSELECTED_CLOSURE:
        raise StaticError("unselected Equation22 reverse-dependent roster differs")
    for row in private_closure:
        declaration = row["declaration"]
        if row["visibility"] == "private":
            if row["closure_role"] != "private_seed" or row["selected_owner"] != "yes":
                raise StaticError(f"private seed metadata differs: {declaration}")
        elif row["closure_role"] != "reverse_dependent":
            raise StaticError(f"public reverse-dependent metadata differs: {declaration}")
        if row["selected_owner"] == "yes":
            route = route_by_name.get(declaration)
            if route is None or route["baseline_owner_module"] != row["owner_module"]:
                raise StaticError(f"selected private-closure route differs: {declaration}")
        elif declaration not in UNSELECTED_CLOSURE:
            raise StaticError(f"unexpected unselected private-closure row: {declaration}")

    if len(matrix) != 41 or len({row["test_module"] for row in matrix}) != 41 or Counter(row["kind"] for row in matrix) != Counter({
        "canonical-only": 20, "old-only": 16, "focused": 5
    }):
        raise StaticError("test matrix shape differs")
    canonical_imports: set[str] = set()
    old_imports: set[str] = set()
    test_payloads: dict[str, tuple[list[str], list[str], str]] = {}
    for row in matrix:
        path = module_path(row["test_module"])
        if not path.is_file():
            raise StaticError(f"matrix test missing: {row['test_module']}")
        text = path.read_text(encoding="utf-8-sig")
        imports = IMPORT_RE.findall(text)
        checks = CHECK_RE.findall(text)
        expected_imports = row["imported_modules"].split(";") if row["imported_modules"] else []
        if imports != expected_imports or len(imports) != int(row["imports"]):
            raise StaticError(f"test import ledger differs: {row['test_module']}")
        if len(checks) != int(row["checks"]):
            raise StaticError(f"test check count differs: {row['test_module']}")
        if len(checks) != len(set(checks)):
            raise StaticError(f"duplicate #check in test: {row['test_module']}")
        test_payloads[row["test_module"]] = (imports, checks, text)
        if row["kind"] == "canonical-only":
            if len(imports) != 1:
                raise StaticError("canonical-only test is not isolated")
            canonical_imports.add(imports[0])
            expected = {
                item["baseline_declaration_name"] for item in routes_by_destination[imports[0]]
                if item["visibility"] == "public"
            }
            if set(checks) != expected:
                raise StaticError(f"canonical-only public check roster differs: {row['test_module']}")
        elif row["kind"] == "old-only":
            if len(imports) != 1:
                raise StaticError("old-only test is not isolated")
            old_imports.add(imports[0])
            expected = {
                item["baseline_declaration_name"] for item in routes_by_owner[imports[0]]
                if item["visibility"] == "public"
            }
            if set(checks) != expected:
                raise StaticError(f"old-only public check roster differs: {row['test_module']}")
    if canonical_imports != destinations or old_imports != owners:
        raise StaticError("isolated test coverage differs from route authority")

    public_test = "NumStabilityTest.Reorganization.R01.Focused.PublicNameRetention"
    private_test = "NumStabilityTest.Reorganization.R01.Focused.PrivateNormalization"
    equation22_test = "NumStabilityTest.Reorganization.R01.Focused.Equation22TypedConsumers"
    series_test = "NumStabilityTest.Reorganization.R01.Focused.StationaryIterationSeries"
    roots_test = "NumStabilityTest.Reorganization.R01.Focused.RootAggregates"
    focused = {row["test_module"] for row in matrix if row["kind"] == "focused"}
    if focused != {public_test, private_test, equation22_test, series_test, roots_test}:
        raise StaticError("focused test module roster differs")

    public_names = {
        row["baseline_declaration_name"] for row in routes if row["visibility"] == "public"
    }
    public_imports, public_checks, _ = test_payloads[public_test]
    if set(public_imports) != {algorithm_all, analysis_all, results_all} or set(public_checks) != public_names:
        raise StaticError("PublicNameRetention exact roster differs")

    private_imports, private_checks, private_text = test_payloads[private_test]
    expected_private_modules = {
        route_by_name[name]["destination_module"] for name in private_map
    }
    private_pairs = PRIVATE_NAME_RE.findall(private_text)
    constructed_private = {
        f"_private.{module}.0.{declaration}" for module, declaration in private_pairs
    }
    if (
        len(private_pairs) != 10
        or len(constructed_private) != 10
        or constructed_private != set(private_map.values())
        or set(private_imports) != expected_private_modules
        or set(private_checks) != PRIVATE_REVERSE_CHECKS
    ):
        raise StaticError("PrivateNormalization exact roster differs")
    for required in ("run_cmd do", "Lean.getEnv", "Lean.Environment.contains environment name"):
        if required not in private_text:
            raise StaticError(f"PrivateNormalization environment check missing: {required}")

    equation22_imports, equation22_checks, _ = test_payloads[equation22_test]
    if equation22_imports != ["NumStability.Source.Higham.Chapter17.Equation22"] or set(equation22_checks) != UNSELECTED_CLOSURE:
        raise StaticError("Equation22TypedConsumers exact roster differs")

    series_imports, series_checks, _ = test_payloads[series_test]
    series_public = {
        row["baseline_declaration_name"] for row in routes
        if row["baseline_owner_module"] in source_umbrella_owners and row["visibility"] == "public"
    }
    if set(series_imports) != {
        "NumStability.Algorithms.StationaryIterationSeries", results_series
    } or set(series_checks) != series_public:
        raise StaticError("StationaryIterationSeries exact roster differs")

    root_imports, root_checks, _ = test_payloads[roots_test]
    if set(root_imports) != {
        "NumStability.Algorithms", "NumStability.Analysis", "NumStability.Source.Higham.Chapter17"
    } or set(root_checks) != ROOT_AGGREGATE_CHECKS:
        raise StaticError("RootAggregates exact roster differs")

    print(
        "R01 static checks passed: "
        f"routes={len(routes)}, public=233, private=10, owners={len(owners)}, "
        f"destinations={len(destinations)}, closure={len(private_closure)}, tests={len(matrix)}, "
        "hashes=4, cycles=0, aggregates=4, focused=5, generated-changes=0, "
        "canonical-to-historical=0, reusable-to-Source=0, reusable-to-facade=0"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, StaticError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
