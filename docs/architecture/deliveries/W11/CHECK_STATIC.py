#!/usr/bin/env python3
"""Static W11 routing, compatibility, isolation, and source-boundary gates."""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
IMPORT_RE = re.compile(
    r"(?m)^(?:public[ \t]+|private[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)
PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
AXIOM_RE = re.compile(r"(?m)^\s*(?:axiom|constant)[ \t]+")
DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|opaque|axiom|inductive|structure|class|instance)\b"
)
LOCAL_NOTATION_RE = re.compile(r"(?m)^\s*(?:local\s+)?notation\b")

PRIVATE_NAMES = {
    "_private.NumStability.Algorithms.RandNLA.HitCountConcentration.0.NumStability.sqMagTraceProbMass_two_point_factor",
    "_private.NumStability.Algorithms.RandNLA.RowSamplingGram.0.NumStability.rowSqNormTraceProbMass_two_point_factor",
    "_private.NumStability.Algorithms.RandNLA.UniformRowSampling.0.NumStability.uniformRowTraceProbMass_two_point_factor",
}
PRIVATE_PAYLOAD_SHA = "FAD5DC5D7CD80112157031E012D32593FBF33ACED6C1B9F94D60DEC55D1EA7F9"
MATRIX_INVERSION_IMPORTS = {
    "NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion",
    "NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion",
    "NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion",
}
LOW_RANK_MODULES = {
    "NumStability.Algorithms.RandNLA.LowRankApprox",
    "NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.ColumnSketches.Core",
    "NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.RankFactorizations.Core",
    "NumStability.Source.DrineasMahoney.RandNLA2016.Equation09.LowRankApproximation.Endpoints",
}
CHAPTER20 = "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve"
EQ08 = "NumStability.Source.DrineasMahoney.RandNLA2016.Equation08.LeastSquaresSketch.Endpoints"
EXPECTED_CANONICAL_FACADE_BOUNDARIES = {
    (
        EQ08,
        "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve",
        "NumStability.Algorithms.RandNLA.LowRankApprox",
    ),
    (
        EQ08,
        "NumStability.Analysis.Perturbation.LeastSquares.GramBasis",
        "NumStability.Algorithms.RandNLA.LowRankApprox",
    ),
    (
        EQ08,
        "NumStability.Algorithms.LinearSystems.LeastSquares.GramBasis",
        "NumStability.Algorithms.RandNLA.LowRankApprox",
    ),
}
EXPECTED_FOCUSED_TESTS = {
    "ElementwiseSampling",
    "ElementwiseSpectralReusable",
    "ElementwiseSpectralEquation02",
    "TraceMGFConcentration",
    "RowAndLeverageSampling",
    "UniformRowSampling",
    "Preconditioning",
    "LeastSquaresReusable",
    "LeastSquaresChapter20Closure",
    "LowRankReusable",
    "LowRankEquation09",
    "PrivateHitCountClosure",
    "PrivateRowGramClosure",
    "PrivateUniformClosure",
    "ProtectedW02Doolittle",
    "ProtectedW02ProbabilitySpectral",
    "ProtectedW06TraceMGF",
    "ProtectedChapter20",
    "ProtectedMatrixInversionAPIs",
    "LowRankMatrixInversionRetarget",
    "SharedConsumerRetargetTarget",
}


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    return result.stdout


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    control = args.control_root.resolve()
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    contract = json.loads((phase / "branches/B0010.json").read_text(encoding="utf-8"))
    if (
        contract.get("status") != "active"
        or contract.get("base_sha") != BASE
        or contract.get("operator_ids") != ["codex-local"]
    ):
        raise RuntimeError("B0010 is not the active singleton codex-local contract")
    owners = {
        rule["path"][:-5].replace("/", ".")
        for rule in contract["owned_paths"] if rule["path"].endswith(".lean")
    }

    evidence = root / "docs/architecture/deliveries/W11"
    tests = read_tsv(evidence / "TEST_MATRIX.tsv")
    if len({row["test_module"] for row in tests}) != len(tests):
        raise RuntimeError("TEST_MATRIX.tsv contains duplicate test modules")
    kind_counts = Counter(row["kind"] for row in tests)
    expected_test_counts = Counter({
        "canonical-reusable": 19,
        "canonical-source": 18,
        "old-path": 18,
        "focused": 21,
    })
    if kind_counts != expected_test_counts:
        raise RuntimeError(f"test matrix counts differ: {dict(kind_counts)}")
    focused_names = {
        row["test_module"].rsplit(".", 1)[-1]
        for row in tests if row["kind"] == "focused"
    }
    if focused_names != EXPECTED_FOCUSED_TESTS:
        raise RuntimeError(
            f"focused test names differ: missing={sorted(EXPECTED_FOCUSED_TESTS - focused_names)}, "
            f"extra={sorted(focused_names - EXPECTED_FOCUSED_TESTS)}"
        )

    isolation_errors: list[str] = []
    canonical_modules: set[str] = set()
    reusable_modules: set[str] = set()
    source_modules: set[str] = set()
    old_path_imports: list[str] = []
    for row in tests:
        path = root / module_path(row["test_module"])
        if not path.is_file():
            isolation_errors.append(f"missing test: {row['test_module']}")
            continue
        imports = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        payload = path.read_text(encoding="utf-8")
        expected = row["imports"].split(",") if row["imports"] else []
        if imports != sorted(set(expected)):
            isolation_errors.append(
                f"{row['test_module']}: imports={imports}, expected={sorted(set(expected))}"
            )
        representatives = row["representatives"].split(",") if row["representatives"] else []
        missing_representatives = [
            representative for representative in representatives
            if f"#check @{representative}" not in payload
        ]
        if missing_representatives:
            isolation_errors.append(
                f"{row['test_module']}: missing #check representatives {missing_representatives}"
            )
        if row["kind"].startswith("canonical-"):
            if len(imports) != 1:
                isolation_errors.append(f"{row['test_module']}: canonical test is not isolated")
            else:
                canonical_modules.add(imports[0])
                if row["kind"] == "canonical-reusable":
                    reusable_modules.add(imports[0])
                else:
                    source_modules.add(imports[0])
        if row["kind"] == "old-path" and (len(imports) != 1 or imports[0] not in owners):
            isolation_errors.append(f"{row['test_module']}: old-path test is not isolated")
        if row["kind"] == "old-path" and len(imports) == 1:
            old_path_imports.append(imports[0])
    if len(old_path_imports) != 18 or set(old_path_imports) != owners:
        isolation_errors.append(
            "old-path import set differs: "
            f"missing={sorted(owners - set(old_path_imports))}, "
            f"extra={sorted(set(old_path_imports) - owners)}"
        )

    routes = read_tsv(evidence / "DECLARATION_ROUTES.tsv")
    route_errors: list[str] = []
    if len(routes) != 3354:
        route_errors.append(f"declaration route count is {len(routes)}, expected 3354")
    if Counter(row["kind"] for row in routes) != Counter({
        "theorem": 2469, "definition": 813, "inductive": 24,
        "constructor": 24, "recursor": 24,
    }):
        route_errors.append("declaration kind counts differ")
    if Counter(row["visibility"] for row in routes) != Counter(public=3351, private=3):
        route_errors.append("declaration visibility counts differ")
    if Counter(row["tier"] for row in routes) != Counter(reusable=2322, source=807, compatibility=225):
        route_errors.append("routing tier counts differ")
    if Counter(row["disposition"] for row in routes) != Counter(relocated=3129, retained_private_closure=225):
        route_errors.append("relocation/retention counts differ")
    if len({row["declaration"] for row in routes}) != len(routes):
        route_errors.append("declaration route ledger contains duplicate declaration names")
    private_rows = [row for row in routes if row["visibility"] == "private"]
    if {row["declaration"] for row in private_rows} != PRIVATE_NAMES:
        route_errors.append("private declaration names differ")
    if any(
        row["disposition"] != "retained_private_closure"
        or row["historical_owner"] != row["destination_module"]
        for row in private_rows
    ):
        route_errors.append("a private declaration moved or changed disposition")
    routed_modules = {
        row["destination_module"] for row in routes if row["disposition"] == "relocated"
    }
    if routed_modules != canonical_modules:
        route_errors.append(
            f"canonical test coverage differs: missing={sorted(routed_modules - canonical_modules)}, "
            f"extra={sorted(canonical_modules - routed_modules)}"
        )
    reusable_destinations = {
        row["destination_module"] for row in routes if row["tier"] == "reusable"
    }
    source_destinations = {
        row["destination_module"] for row in routes if row["tier"] == "source"
    }
    if reusable_destinations != reusable_modules:
        route_errors.append(
            f"reusable canonical coverage differs: missing={sorted(reusable_destinations - reusable_modules)}, "
            f"extra={sorted(reusable_modules - reusable_destinations)}"
        )
    if source_destinations != source_modules:
        route_errors.append(
            f"source canonical coverage differs: missing={sorted(source_destinations - source_modules)}, "
            f"extra={sorted(source_modules - source_destinations)}"
        )
    if any(
        not row["destination_module"].startswith("NumStability.Algorithms.RandomizedLinearAlgebra.")
        for row in routes if row["tier"] == "reusable"
    ):
        route_errors.append("a reusable declaration is outside the reviewed API prefix")
    if any(
        not row["destination_module"].startswith("NumStability.Source.DrineasMahoney.RandNLA2016.")
        for row in routes if row["tier"] == "source"
    ):
        route_errors.append("a source declaration is outside the reviewed source prefix")

    retentions = read_tsv(evidence / "RETENTION.tsv")
    facade_errors: list[str] = []
    physical_owners = owners - {"NumStability.Algorithms.RandNLA"}
    if len(retentions) != 17:
        facade_errors.append(f"RETENTION.tsv has {len(retentions)} physical owners")
    if {row["historical_owner"] for row in retentions} != physical_owners:
        facade_errors.append("RETENTION owner set differs from the 17 physical B0010 owners")
    if sum(int(row["selected"]) for row in retentions) != 3354:
        facade_errors.append("RETENTION selected total differs")
    if sum(int(row["retained_total"]) for row in retentions) != 225:
        facade_errors.append("RETENTION retained total differs")
    if sum(int(row["relocated"]) for row in retentions) != 3129:
        facade_errors.append("RETENTION relocated total differs")
    if Counter(row["facade_kind"] for row in retentions) != Counter(
        declaration_bearing=9, pure_import_shim=8
    ):
        facade_errors.append("facade kind counts differ")

    routes_by_owner: dict[str, list[dict[str, str]]] = {}
    for route in routes:
        routes_by_owner.setdefault(route["historical_owner"], []).append(route)
    for retention in retentions:
        module = retention["historical_owner"]
        owner_routes = routes_by_owner.get(module, [])
        expected_counts = {
            "selected": len(owner_routes),
            "private": sum(row["visibility"] == "private" for row in owner_routes),
            "retained_public": sum(
                row["disposition"] == "retained_private_closure" and row["visibility"] == "public"
                for row in owner_routes
            ),
            "retained_private": sum(
                row["disposition"] == "retained_private_closure" and row["visibility"] == "private"
                for row in owner_routes
            ),
            "retained_total": sum(
                row["disposition"] == "retained_private_closure" for row in owner_routes
            ),
            "relocated": sum(row["disposition"] == "relocated" for row in owner_routes),
            "reusable": sum(row["tier"] == "reusable" for row in owner_routes),
            "source": sum(row["tier"] == "source" for row in owner_routes),
        }
        actual_counts = {key: int(retention[key]) for key in expected_counts}
        if actual_counts != expected_counts:
            facade_errors.append(
                f"{module}: RETENTION/route counts differ: "
                f"actual={actual_counts}, expected={expected_counts}"
            )

    sys.path.insert(0, str(root / "tools/architecture"))
    from generate_baseline import remove_lean_comments
    for row in retentions:
        module = row["historical_owner"]
        payload = (root / module_path(module)).read_text(encoding="utf-8")
        uncommented = remove_lean_comments(payload)
        direct_imports = set(IMPORT_RE.findall(payload))
        required_destinations = {
            route["destination_module"]
            for route in routes_by_owner[module]
            if route["disposition"] == "relocated"
        }
        if not required_destinations <= direct_imports:
            facade_errors.append(
                f"{module}: facade omits relocated destinations "
                f"{sorted(required_destinations - direct_imports)}"
            )
        has_declaration = bool(DECL_RE.search(uncommented) or LOCAL_NOTATION_RE.search(uncommented))
        if row["facade_kind"] == "pure_import_shim":
            residual = IMPORT_RE.sub("", uncommented).strip()
            if has_declaration or residual:
                facade_errors.append(f"pure shim is not import-only: {module}")
        elif row["facade_kind"] == "declaration_bearing":
            if not has_declaration:
                facade_errors.append(f"retained facade lacks declarations: {module}")
        else:
            facade_errors.append(f"unknown facade kind: {module}:{row['facade_kind']}")
    umbrella = (root / module_path("NumStability.Algorithms.RandNLA")).read_text(encoding="utf-8")
    umbrella_uncommented = remove_lean_comments(umbrella)
    if DECL_RE.search(umbrella_uncommented) or IMPORT_RE.sub("", umbrella_uncommented).strip():
        facade_errors.append("RandNLA umbrella is not import-only")
    if set(IMPORT_RE.findall(umbrella)) != physical_owners:
        facade_errors.append("RandNLA umbrella does not import exactly the 17 physical owners")

    private_closure_errors: list[str] = []
    closure_metadata: dict[str, str] = {}
    closure_owners: dict[str, dict[str, int]] = {}
    closure_commands: list[list[str]] = []
    with (evidence / "PRIVATE_CLOSURE.tsv").open(encoding="utf-8", newline="") as stream:
        for fields in csv.reader(stream, delimiter="\t"):
            if not fields:
                continue
            if fields[0] == "metadata" and len(fields) == 3:
                closure_metadata[fields[1]] = fields[2]
            elif fields[0] == "owner" and len(fields) == 11:
                closure_owners[fields[1]] = {
                    "command_count": int(fields[7]),
                    "retained_command_count": int(fields[8]),
                    "move_candidate_count": int(fields[9]),
                    "private_declaration_count": int(fields[10]),
                }
            elif fields[0] == "command":
                closure_commands.append(fields)
    expected_closure_metadata = {
        "base_revision": BASE,
        "projection_id": "P0011",
        "projection_sha256": "0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2",
        "selector_sha256": "24E3BD565946AECFDBAB9D2D21BF1201B86ECD16197F892E1B62A30162D9EE00",
        "owner_count": "17",
        "selected_declaration_count": "3354",
        "command_count": "3086",
        "private_declaration_count": "3",
        "graph_reverse_closure_count": "225",
        "retained_command_count": "225",
        "move_candidate_command_count": "2861",
        "private_payload_sha256": PRIVATE_PAYLOAD_SHA,
    }
    for key, expected in expected_closure_metadata.items():
        if closure_metadata.get(key) != expected:
            private_closure_errors.append(
                f"private closure metadata {key}={closure_metadata.get(key)!r}, expected {expected!r}"
            )
    if len(closure_commands) != 3086:
        private_closure_errors.append(f"private closure command count is {len(closure_commands)}")
    decisions = Counter(fields[8] for fields in closure_commands)
    if decisions != Counter(retain_historical=225, move_candidate=2861):
        private_closure_errors.append(f"private closure decisions differ: {dict(decisions)}")
    private_seeds = {fields[2] for fields in closure_commands if fields[9] == "private_seed"}
    if private_seeds != PRIVATE_NAMES:
        private_closure_errors.append(f"private seed roots differ: {sorted(private_seeds)}")
    if set(closure_owners) != physical_owners:
        private_closure_errors.append("private closure owner set differs")
    retention_by_owner = {row["historical_owner"]: row for row in retentions}
    for owner, counts in closure_owners.items():
        if counts["retained_command_count"] != int(retention_by_owner[owner]["retained_total"]):
            private_closure_errors.append(f"{owner}: retained closure/route count differs")

    import_cache: dict[str, tuple[str, ...]] = {}
    unresolved: set[str] = set()
    def imports_of(module: str) -> tuple[str, ...]:
        if module in import_cache:
            return import_cache[module]
        path = root / module_path(module)
        if not path.is_file():
            if module.startswith("NumStability."):
                unresolved.add(module)
            import_cache[module] = ()
            return ()
        found = tuple(IMPORT_RE.findall(path.read_text(encoding="utf-8")))
        import_cache[module] = found
        return found

    cycles: list[list[str]] = []
    reusable_source_paths: set[tuple[str, tuple[str, ...]]] = set()
    canonical_facade_boundaries: set[tuple[str, str, str]] = set()
    for root_module in sorted(canonical_modules):
        state: dict[str, int] = {}
        stack: list[str] = []
        def visit(module: str) -> None:
            if state.get(module) == 2:
                return
            if state.get(module) == 1:
                cycles.append(stack[stack.index(module):] + [module])
                return
            state[module] = 1
            stack.append(module)
            if (
                root_module in reusable_modules
                and module.startswith("NumStability.Source.")
            ):
                reusable_source_paths.add((root_module, tuple(stack)))
            for target in imports_of(module):
                if target.startswith("NumStability."):
                    if target in owners:
                        canonical_facade_boundaries.add((root_module, module, target))
                    else:
                        visit(target)
            stack.pop()
            state[module] = 2
        visit(root_module)

    boundary_errors: list[str] = []
    if canonical_facade_boundaries != EXPECTED_CANONICAL_FACADE_BOUNDARIES:
        boundary_errors.append(
            "canonical W11-facade boundaries differ: "
            f"missing={sorted(EXPECTED_CANONICAL_FACADE_BOUNDARIES - canonical_facade_boundaries)}, "
            f"extra={sorted(canonical_facade_boundaries - EXPECTED_CANONICAL_FACADE_BOUNDARIES)}"
        )
    reusable_facade_boundaries = {
        boundary for boundary in canonical_facade_boundaries
        if boundary[0] in reusable_modules
    }
    if reusable_facade_boundaries:
        boundary_errors.append(
            f"reusable canonical modules reach W11 facades: {sorted(reusable_facade_boundaries)}"
        )

    dependency_errors: list[str] = []
    for module in sorted(LOW_RANK_MODULES):
        imports = set(imports_of(module))
        matrix_inversion_imports = {
            item for item in imports
            if item.startswith("NumStability.Algorithms.MatrixInversion")
        }
        if matrix_inversion_imports != MATRIX_INVERSION_IMPORTS:
            dependency_errors.append(
                f"{module}: MatrixInversion imports differ: "
                f"actual={sorted(matrix_inversion_imports)}, expected={sorted(MATRIX_INVERSION_IMPORTS)}"
            )
    if CHAPTER20 not in imports_of(EQ08):
        dependency_errors.append("equation-(8) endpoint lost its accepted Chapter20 import")
    for module in reusable_modules:
        if CHAPTER20 in imports_of(module):
            dependency_errors.append(f"reusable module imports Chapter20: {module}")
    expected_chapter20_importers = {
        "NumStability.Algorithms.RandNLA.LeastSquaresSketch",
        EQ08,
    }
    actual_chapter20_importers = {
        module for module in canonical_modules | owners
        if CHAPTER20 in imports_of(module)
    }
    if actual_chapter20_importers != expected_chapter20_importers:
        dependency_errors.append(
            "W11 Chapter20 direct importers differ: "
            f"actual={sorted(actual_chapter20_importers)}, "
            f"expected={sorted(expected_chapter20_importers)}"
        )
    for module in canonical_modules | owners:
        if "NumStability.Algorithms.MatrixInversion" in imports_of(module):
            dependency_errors.append(f"{module}: restored forbidden MatrixInversion umbrella")

    changed = {
        line.strip().replace("\\", "/")
        for line in git(root, "diff", "--name-only", BASE, "--").splitlines()
        if line.strip()
    }
    changed.update(
        line.strip().replace("\\", "/")
        for line in git(root, "ls-files", "--others", "--exclude-standard").splitlines()
        if line.strip()
    )
    lean_paths = sorted(path for path in changed if path.endswith(".lean"))
    placeholder_hits: list[str] = []
    missing_docs: list[str] = []
    unsorted_imports: list[str] = []
    for relative in lean_paths:
        payload = (root / relative).read_text(encoding="utf-8")
        uncommented = remove_lean_comments(payload)
        if PLACEHOLDER_RE.search(uncommented) or AXIOM_RE.search(uncommented):
            placeholder_hits.append(relative)
        if (
            relative.startswith((
                "NumStability/Algorithms/RandomizedLinearAlgebra/",
                "NumStability/Source/DrineasMahoney/RandNLA2016/",
            )) and "/-!" not in payload
        ):
            missing_docs.append(relative)
        imports = IMPORT_RE.findall(payload)
        if imports != sorted(set(imports)):
            unsorted_imports.append(relative)

    casefold: dict[str, str] = {}
    collisions: list[tuple[str, str]] = []
    for path in sorted((root / "NumStability").rglob("*.lean")):
        relative = path.relative_to(root).as_posix()
        folded = relative.casefold()
        if folded in casefold and casefold[folded] != relative:
            collisions.append((casefold[folded], relative))
        casefold[folded] = relative

    result = {
        "tests": dict(kind_counts),
        "canonical_modules": len(canonical_modules),
        "reusable_modules": len(reusable_modules),
        "source_modules": len(source_modules),
        "changed_lean_paths": len(lean_paths),
        "isolation_errors": isolation_errors,
        "route_errors": route_errors,
        "facade_shape_errors": facade_errors,
        "private_closure_errors": private_closure_errors,
        "unresolved_project_imports": sorted(unresolved),
        "import_cycles": cycles[:10],
        "reusable_to_Source_paths": sorted(reusable_source_paths)[:10],
        "canonical_to_W11_facade_boundaries": sorted(canonical_facade_boundaries),
        "expected_pending_facade_boundaries": sorted(EXPECTED_CANONICAL_FACADE_BOUNDARIES),
        "canonical_boundary_errors": boundary_errors,
        "dependency_errors": dependency_errors,
        "placeholder_or_axiom_paths": placeholder_hits,
        "missing_module_docstrings": missing_docs,
        "unsorted_or_duplicate_imports": unsorted_imports,
        "casefold_path_collisions": collisions,
    }
    print(json.dumps(result, indent=2))
    return 1 if any((
        isolation_errors, route_errors, facade_errors, private_closure_errors, unresolved, cycles,
        reusable_source_paths, boundary_errors, dependency_errors,
        placeholder_hits, missing_docs, unsorted_imports, collisions,
    )) else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
