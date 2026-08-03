#!/usr/bin/env python3
"""Generate the reviewed W05 command-preserving semantic split.

The generator consumes the frozen P0006 projection and W05 private-closure
ledger.  Complete Lean command spans are copied from C0004 source blobs into
reviewed reusable or source-numbered leaves.  It derives imports from typed
declaration edges, rejects canonical dependencies on historical facades and
reusable dependencies on ``Source``, preserves the one required historical
private closure, and emits isolated import tests and route evidence.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


BASE = "b56f609f3bf66b5d7d0b677567cce82fee0c275b"
PROJECTION_SHA256 = "6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5"
ENGINE_SHA256 = "3DF117CD4C074B69068F25C196D3112191DA96F5E67B16B6E7888D6FC9A29BBA"

OWNERS = (
    "NumStability.Algorithms.Sylvester.Higham16",
    "NumStability.Algorithms.Sylvester.Higham16Lyapunov",
    "NumStability.Algorithms.Sylvester.Higham16Psi",
    "NumStability.Algorithms.Sylvester.SylvesterBackward",
    "NumStability.Algorithms.Sylvester.SylvesterPerturbation",
    "NumStability.Algorithms.Sylvester.SylvesterSpec",
    "NumStability.Analysis.InverseOpNorm2",
    "NumStability.Analysis.RealInvariantSubspace",
    "NumStability.Analysis.RealQuasiSchur",
    "NumStability.Analysis.SchurTriangulation",
)
OWNER_SET = set(OWNERS)

A = "NumStability.Algorithms.MatrixEquations.Sylvester"
N = "NumStability.Analysis"
S = "NumStability.Source.Higham"

EQ_BASIC = f"{A}.Equation.Basic"
EQ_LYAPUNOV = f"{A}.Equation.Lyapunov"
EQ_RECTANGULAR = f"{A}.Equation.Rectangular"
EQ_VECTORIZATION = f"{A}.Equation.Vectorization"
EQ_DIAGONAL = f"{A}.Equation.Diagonal"
EQ_SCHUR = f"{A}.Equation.SchurCoordinates"
BACK_SPEC = f"{A}.BackwardError.Specification"
BACK_SYLVESTER = f"{A}.BackwardError.SylvesterSVD"
BACK_LYAPUNOV = f"{A}.BackwardError.LyapunovSpectral"
PERT_BASIC = f"{A}.Perturbation.Basic"
PERT_VECTOR = f"{A}.Perturbation.Vectorization"
PERT_SEPARATION = f"{A}.Perturbation.SeparationBounds"
COND_FIRST = f"{A}.Conditioning.FirstOrder"
COND_PRACTICAL = f"{A}.Conditioning.PracticalErrorBounds"
COND_SEPARATION = f"{A}.Conditioning.Separation"
COND_SYLVESTER = f"{A}.Conditioning.StructuredSylvester"
COND_LYAPUNOV = f"{A}.Conditioning.StructuredLyapunov"
COND_SINGULAR = f"{A}.Conditioning.SingularValue"
GENERALIZED = f"{A}.GeneralizedEquations.Basic"

INV_RAYLEIGH = f"{N}.SingularValues.InverseBounds.Rayleigh"
INV_GRAM = f"{N}.SingularValues.InverseBounds.Gram"
INV_OPERATOR = f"{N}.SingularValues.InverseBounds.OperatorTwo"
REAL_INV_COMPLEX = f"{N}.LinearOperators.Schur.Real.InvariantSubspace.Complexification"
REAL_INV_TWO = f"{N}.LinearOperators.Schur.Real.InvariantSubspace.TwoByTwo"
REAL_INV_EXISTENCE = f"{N}.LinearOperators.Schur.Real.InvariantSubspace.Existence"
REAL_QUASI_BASIC = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.Basic"
REAL_QUASI_BLOCK = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.BlockEmbedding"
REAL_QUASI_DEFLATION = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.Deflation"
REAL_QUASI_FRAME = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.OrthogonalFrame"
REAL_QUASI_REINDEX = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.Reindex"
REAL_QUASI_TRAILING = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.TrailingConjugation"
REAL_QUASI_EXISTENCE = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.Existence"
REAL_QUASI_API = f"{N}.LinearOperators.Schur.Real.QuasiTriangular.API"
COMPLEX_BLOCK = f"{N}.LinearOperators.Schur.Complex.BlockEmbedding"
COMPLEX_DEFLATION = f"{N}.LinearOperators.Schur.Complex.Deflation"
COMPLEX_TRIANGULATION = f"{N}.LinearOperators.Schur.Complex.Triangulation"

GENERIC_SOURCE_DESTINATION = {
    "NumStability.sylvester_relative_first_order_bound_of_sepLowerBound":
        f"{S}.Chapter16.Section03.PerturbationAndConditioning.Equation24",
    "NumStability.sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf":
        f"{S}.Chapter16.Section03.PerturbationAndConditioning.Equation24",
    "NumStability.sylvester_relative_first_order_bound_diagonal":
        f"{S}.Chapter16.Section03.PerturbationAndConditioning.Equation24",
    "NumStability.lyapunov_relative_first_order_bound_of_sepLowerBound":
        f"{S}.Chapter16.Section03.PerturbationAndConditioning.Equation27",
    "NumStability.lyapunov_relative_first_order_bound_of_pos_le_sylvesterSepInf":
        f"{S}.Chapter16.Section03.PerturbationAndConditioning.Equation27",
    "NumStability.lyapunov_relative_first_order_bound_diagonal":
        f"{S}.Chapter16.Section03.PerturbationAndConditioning.Equation27",
}

PERTURBATION_CONDITION_NAMES = {
    "NumStability.SylvesterPsiFirstOrderBound",
    "NumStability.sylvesterScaledPerturbationTripleNorm",
    "NumStability.sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul",
    "NumStability.sylvester_relative_first_order_bound_of_psi",
    "NumStability.LyapunovConditionFirstOrderBound",
    "NumStability.lyapunovScaledPerturbationPairNorm",
    "NumStability.lyapunovScaledPerturbationPairNorm_le_sqrt_two_mul",
    "NumStability.lyapunov_relative_first_order_bound_of_condition",
    "NumStability.condSylvester",
}

LOCATORS = {
    f"{S}.Chapter16.Section02.RealSchurDecomposition.InvariantSubspace": {
        REAL_INV_EXISTENCE,
        REAL_INV_TWO,
    },
    f"{S}.Chapter16.Section02.RealSchurDecomposition.QuasiTriangular": {
        REAL_QUASI_API,
    },
    f"{S}.Chapter18.Section01.SchurDecomposition.ComplexTriangulation": {
        COMPLEX_TRIANGULATION,
    },
}

LOCATOR_REPRESENTATIVES = {
    f"{S}.Chapter16.Section02.RealSchurDecomposition.InvariantSubspace":
        "NumStability.exists_real_invariant_subspace_dim_one_or_two",
    f"{S}.Chapter16.Section02.RealSchurDecomposition.QuasiTriangular":
        "NumStability.real_quasi_schur",
    f"{S}.Chapter18.Section01.SchurDecomposition.ComplexTriangulation":
        "NumStability.schur_triangulation",
}


class MigrationError(RuntimeError):
    pass


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load_engine(repo: Path):
    path = repo / "docs/architecture/deliveries/W02/GENERATE_MIGRATION.py"
    found = file_sha256(path)
    if found != ENGINE_SHA256:
        raise MigrationError(
            f"migration engine hash differs: expected {ENGINE_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w05_migration_engine", path)
    if spec is None or spec.loader is None:
        raise MigrationError(f"cannot load migration engine at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.BASE = BASE
    module.P0002_SHA256 = PROJECTION_SHA256
    module.EXPECTED_DECLARATIONS = 921
    module.EXPECTED_PHYSICAL_DECLARATIONS = 921
    module.EXPECTED_COMMANDS = 921
    module.EXPECTED_RETAINED = 138
    module.PHYSICAL = OWNERS
    module.PHYSICAL_SET = OWNER_SET
    return module


def source_destination(name: str) -> str | None:
    short = name.removeprefix("NumStability.")
    if short.startswith("H16_LyapunovDefinition_"):
        return f"{S}.Chapter16.Section02.SylvesterAndLyapunovBackwardError.LyapunovDefinition"
    if short.startswith("H16_Lyapunov_"):
        return f"{S}.Chapter16.Section03.PerturbationAndConditioning.LyapunovSolutions"
    match = re.match(r"H16_eq16_((?:\d+_)*\d+)_", short)
    if not match:
        return None
    numbers = tuple(int(item) for item in match.group(1).split("_"))
    number = numbers[-1]
    if number <= 3:
        topic = "Section01.SylvesterEquation"
    elif 9 <= number <= 21:
        topic = "Section02.SylvesterAndLyapunovBackwardError"
    elif 22 <= number <= 27:
        topic = "Section03.PerturbationAndConditioning"
    elif 28 <= number <= 29:
        topic = "Section04.PracticalErrorBounds"
    elif 30 <= number <= 32:
        topic = "Section05.GeneralizedMatrixEquations"
    else:
        raise MigrationError(f"unreviewed movable Higham equation route: {name}")
    return f"{S}.Chapter16.{topic}.Equation{number:02d}"


def single_public_name(command) -> str:
    public = [name for name in command.declarations if not name.startswith("_private.")]
    if not public:
        raise MigrationError(f"movable command has no public declaration: {command.root}")
    return sorted(public)[0]


def route_command(command) -> str:
    exact = {
        GENERIC_SOURCE_DESTINATION[name]
        for name in command.declarations
        if name in GENERIC_SOURCE_DESTINATION
    }
    exact.update(
        destination
        for name in command.declarations
        if (destination := source_destination(name)) is not None
    )
    if len(exact) > 1:
        raise MigrationError(f"{command.root}: conflicting source routes {sorted(exact)}")
    if exact:
        return next(iter(exact))

    owner = command.owner
    line = command.start_line
    names = set(command.declarations)

    if owner == "NumStability.Algorithms.Sylvester.SylvesterSpec":
        if line < 104:
            return EQ_BASIC
        if line < 147:
            return EQ_LYAPUNOV
        return BACK_SPEC
    if owner == "NumStability.Algorithms.Sylvester.SylvesterPerturbation":
        return COND_FIRST if names & PERTURBATION_CONDITION_NAMES else PERT_BASIC
    if owner == "NumStability.Algorithms.Sylvester.SylvesterBackward":
        return BACK_SYLVESTER if line < 1373 else BACK_LYAPUNOV
    if owner == "NumStability.Algorithms.Sylvester.Higham16Psi":
        if "NumStability.sylvesterOp_diagonal_apply" in names:
            return EQ_DIAGONAL
        return COND_SYLVESTER
    if owner == "NumStability.Algorithms.Sylvester.Higham16Lyapunov":
        if "NumStability.lyapunovOp_diagonal_apply" in names:
            return EQ_DIAGONAL
        return COND_LYAPUNOV
    if owner == "NumStability.Algorithms.Sylvester.Higham16":
        if line < 76:
            return EQ_RECTANGULAR
        if line < 303:
            return PERT_VECTOR if any("perturbation" in name for name in names) else EQ_VECTORIZATION
        # Command spans begin at their doc comments; the reviewed declaration
        # boundaries are 2843 and 3288, whose complete commands start at 2838
        # and 3285 respectively.
        if line < 2838:
            return COND_PRACTICAL
        if line < 3285:
            return EQ_DIAGONAL
        if line < 3680:
            return COND_PRACTICAL
        if line < 5239:
            return EQ_SCHUR
        if line < 5349:
            return EQ_LYAPUNOV
        if line < 5747:
            return COND_SEPARATION
        if line < 7257:
            raise MigrationError(f"unexpected movable non-source Higham16 command at {line}: {command.root}")
        if line < 7926:
            return PERT_SEPARATION
        return GENERALIZED

    if owner == "NumStability.Analysis.InverseOpNorm2":
        if line < 96:
            return INV_RAYLEIGH
        if line < 165:
            return INV_GRAM
        if line < 245:
            return INV_OPERATOR
        return COND_SINGULAR
    if owner == "NumStability.Analysis.RealInvariantSubspace":
        if line < 230:
            return REAL_INV_COMPLEX
        if line < 376:
            return REAL_INV_TWO
        return REAL_INV_EXISTENCE
    if owner == "NumStability.Analysis.RealQuasiSchur":
        if line < 66:
            return REAL_QUASI_BASIC
        if line < 110:
            return REAL_QUASI_BLOCK
        if line < 178:
            return REAL_QUASI_DEFLATION
        if line < 634:
            return REAL_QUASI_FRAME
        if line < 746:
            return REAL_QUASI_REINDEX
        if line < 1117:
            return REAL_QUASI_TRAILING
        if line < 1569:
            return REAL_QUASI_EXISTENCE
        return REAL_QUASI_API
    if owner == "NumStability.Analysis.SchurTriangulation":
        if line < 111:
            return COMPLEX_BLOCK
        if line < 185:
            return COMPLEX_DEFLATION
        return COMPLEX_TRIANGULATION
    raise MigrationError(f"unreviewed owner route: {owner}")


def expanded_wrapper_start(source: str, start: int) -> int:
    cursor = start
    while cursor and source[cursor - 1].isspace():
        cursor -= 1
    previous_start = source.rfind("\n", 0, cursor) + 1
    previous = source[previous_start:cursor].strip()
    if re.fullmatch(r"open\s+[A-Za-z0-9_'.]+\s+in", previous):
        return previous_start
    return start


def render_subset(engine, source: str, commands: list, keep: set[str]) -> str:
    """Render one frozen owner subset, attaching standalone ``open ... in``."""
    lines = source.splitlines(keepends=True)
    starts = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    chars = list(source)
    for match in engine.IMPORT_RE.finditer(source):
        engine.blank_region(chars, match.start(), match.end())
    prior_end = -1
    for command in sorted(commands, key=lambda item: (item.start_line, item.start_column)):
        start = engine.utf16_offset(lines, starts, command.start_line, command.start_column)
        end = engine.utf16_offset(lines, starts, command.end_line, command.end_column)
        start = engine.expanded_doc_start(source, start)
        start = expanded_wrapper_start(source, start)
        if start < prior_end:
            raise MigrationError(f"overlapping expanded command span at {command.root}")
        prior_end = end
        if command.root not in keep:
            engine.blank_region(chars, start, end)
    rendered = "".join(chars)
    rendered = re.sub(r"[ \t]+(?=\r?$)", "", rendered, flags=re.MULTILINE)
    if not rendered.endswith("\n"):
        rendered += "\n"
    return rendered


def module_doc(module: str, imports: set[str], note: str) -> str:
    title = module.removeprefix("NumStability.")
    return (
        "".join(f"import {item}\n" for item in sorted(imports))
        + f"\n/-!\n# {title}\n\n{note}\n-/\n"
    )


def topological_owner_order(module: str, nodes: set[str], dependencies) -> list[str]:
    state = {}
    result = []
    stack = []

    def visit(node: str) -> None:
        if state.get(node) == 2:
            return
        if state.get(node) == 1:
            cycle = stack[stack.index(node):] + [node]
            raise MigrationError(
                f"{module}: cross-owner declaration cycle: " + " -> ".join(cycle)
            )
        state[node] = 1
        stack.append(node)
        for target in sorted(dependencies.get(node, ())):
            visit(target)
        stack.pop()
        state[node] = 2
        result.append(node)

    for node in sorted(nodes):
        visit(node)
    return result


def render_route(
    engine,
    module: str,
    commands: list,
    owner_commands,
    frozen_sources,
    imports,
    owner_order: list[str],
) -> str:
    payload = module_doc(
        module,
        imports,
        "W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.",
    ) + "\n"
    by_owner = defaultdict(list)
    for command in commands:
        by_owner[command.owner].append(command)
    if set(owner_order) != set(by_owner):
        raise MigrationError(f"{module}: incomplete cross-owner render order")
    for owner in owner_order:
        keep = {command.root for command in by_owner[owner]}
        payload += render_subset(
            engine,
            frozen_sources[owner],
            owner_commands[owner],
            keep,
        )
    return payload


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the exact W05 migration tree.")
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_arguments()
    root = args.project_root.resolve()
    control = args.control_root.resolve()
    delivery = root / "docs/architecture/deliveries/W05"
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    projection_path = phase / "projections/P0006.tsv.gz"
    closure_path = delivery / "PRIVATE_CLOSURE.tsv"
    contract_path = phase / "branches/B0005.json"
    selector_path = phase / "selectors/W05.tsv"
    combined_path = control / "benchmark-results/C0004-combined.tsv"

    engine = load_engine(root)
    if engine.git(root, "rev-parse", f"{BASE}^{{commit}}") != BASE:
        raise MigrationError("frozen W05 base is unavailable")
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if (
        contract.get("status") != "active"
        or contract.get("base_sha") != BASE
        or contract.get("branch_name") != "codex/reorg-2026-08-w05-ch16-ch18"
        or contract.get("operator_ids") != ["codex-local"]
    ):
        raise MigrationError("B0005 is not the expected active singleton-writer contract")

    declarations, edges = engine.read_projection(projection_path)
    commands, source_paths = engine.read_closure(closure_path)
    full_modules = engine.read_full_declarations(combined_path)
    if set(source_paths) != OWNER_SET:
        raise MigrationError("closure ledger owner set differs from the W05 selector")
    with selector_path.open(encoding="utf-8", newline="") as stream:
        selector_rows = list(csv.reader(stream, delimiter="\t"))
    selector = {(row[0], row[1]) for row in selector_rows[1:]}
    if selector != {(owner, source_paths[owner]) for owner in OWNERS}:
        raise MigrationError("W05 selector differs from closure owner paths")

    owned_paths = {item["path"] for item in contract["owned_paths"]}
    if owned_paths != set(source_paths.values()):
        raise MigrationError("B0005 owned paths differ from the exact ten owners")
    destination_prefixes = tuple(
        item["path"] for item in contract["destination_prefixes"]
        if item["path"].startswith("NumStability/")
    )
    if len(destination_prefixes) != 14:
        raise MigrationError(f"expected 14 production destination prefixes, found {len(destination_prefixes)}")
    allowed_writes = tuple(source_paths.values()) + tuple(
        item["path"] for item in contract["destination_prefixes"]
    )

    command_for_declaration = {}
    owner_commands = defaultdict(list)
    intended = {}
    for key, command in commands.items():
        owner_commands[command.owner].append(command)
        if command.decision == "move_candidate":
            intended[key] = route_command(command)
        for name in command.declarations:
            if name in command_for_declaration:
                raise MigrationError(f"duplicate command assignment for {name}")
            command_for_declaration[name] = command
    if set(command_for_declaration) != set(declarations):
        raise MigrationError("private ledger does not cover all 921 P0006 declarations")

    final_owner = {}
    route_commands = defaultdict(list)
    for key, command in commands.items():
        destination = command.owner if command.decision == "retain_historical" else intended[key]
        if command.decision == "move_candidate":
            route_commands[destination].append(command)
        for name in command.declarations:
            final_owner[name] = destination

    counts = Counter()
    for name, destination in final_owner.items():
        if destination in OWNER_SET:
            counts["retained"] += 1
        elif destination.startswith("NumStability.Source."):
            counts["source"] += 1
        else:
            counts["reusable"] += 1
    if counts != Counter(retained=138, source=281, reusable=502):
        raise MigrationError(f"reviewed route partition differs: {dict(counts)}")
    if len(route_commands) != 62:
        raise MigrationError(f"expected 62 declaration-bearing route modules, found {len(route_commands)}")

    outgoing = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge)

    dependencies = {module: set() for module in route_commands}
    dependency_witnesses = defaultdict(list)
    for module, routed in route_commands.items():
        reusable = not module.startswith("NumStability.Source.")
        historical_owners = {command.owner for command in routed}
        imports = set()
        for owner in historical_owners:
            imports.update(engine.direct_imports(root, owner))
        imports.difference_update(OWNER_SET)
        if reusable:
            imports = {item for item in imports if not item.startswith("NumStability.Source.")}
        for command in routed:
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target = edge.target
                    if target in final_owner:
                        target_module = final_owner[target]
                    else:
                        target_module = full_modules.get(target)
                    if not target_module or target_module == module:
                        continue
                    if target_module in OWNER_SET:
                        raise MigrationError(
                            f"canonical route depends on historical facade: {name} -> {target} ({target_module})"
                        )
                    if reusable and target_module.startswith("NumStability.Source."):
                        raise MigrationError(f"reusable-to-source edge: {name} -> {target}")
                    if target_module.startswith("NumStability."):
                        imports.add(target_module)
                        dependency_witnesses[(module, target_module)].append(
                            (edge.kind, name, target)
                        )
        imports.discard(module)
        dependencies[module] = imports

    route_modules = set(route_commands)
    graph = {
        module: {item for item in imports if item in route_modules}
        for module, imports in dependencies.items()
    }
    cycle = engine.topological_cycle(graph)
    if cycle:
        details = []
        for source, target in zip(cycle, cycle[1:]):
            witnesses = dependency_witnesses[(source, target)][:3]
            details.append(
                f"{source} -> {target}: "
                + "; ".join(f"{kind} {left} -> {right}" for kind, left, right in witnesses)
            )
        raise MigrationError(
            "route-module dependency cycle: " + " -> ".join(cycle)
            + "\n" + "\n".join(details)
        )

    declaration_origin = {
        name: command.owner for name, command in command_for_declaration.items()
    }
    route_owner_dependencies = defaultdict(lambda: defaultdict(set))
    for edge in edges:
        if edge.source not in final_owner or edge.target not in final_owner:
            continue
        module = final_owner[edge.source]
        if module != final_owner[edge.target] or module not in route_modules:
            continue
        source_owner = declaration_origin[edge.source]
        target_owner = declaration_origin[edge.target]
        if source_owner != target_owner:
            route_owner_dependencies[module][source_owner].add(target_owner)
    route_owner_order = {}
    for module, routed in route_commands.items():
        owners = {command.owner for command in routed}
        route_owner_order[module] = topological_owner_order(
            module,
            owners,
            route_owner_dependencies[module],
        )

    generated_under_prefix = defaultdict(set)
    for module in route_modules | set(LOCATORS):
        path = engine.module_path(module).as_posix()
        matches = [prefix for prefix in destination_prefixes if path.startswith(prefix)]
        if len(matches) != 1:
            raise MigrationError(f"{module}: expected one authorized production prefix, found {matches}")
        generated_under_prefix[matches[0]].add(module)
    all_modules = {}
    for prefix in destination_prefixes:
        children = generated_under_prefix[prefix]
        if not children:
            raise MigrationError(f"destination prefix has no reviewed content: {prefix}")
        all_modules[prefix.rstrip("/").replace("/", ".") + ".All"] = set(children)
    if len(all_modules) != 14:
        raise MigrationError("expected one All entry point per production prefix")

    route_lines = [
        "format\t1",
        "declaration\thistorical_module\tdestination_module\tdecision\tkind\tvisibility\tcommand_root\tstart_line",
    ]
    representatives = {}
    for module, routed in route_commands.items():
        public = sorted(
            name for command in routed for name in command.declarations
            if declarations[name].visibility == "public" and not name.startswith("_private.")
        )
        if not public:
            raise MigrationError(f"route has no public representative: {module}")
        representatives[module] = public[0]
    for name in sorted(declarations):
        declaration = declarations[name]
        command = command_for_declaration[name]
        destination = final_owner[name]
        if command.decision == "retain_historical":
            decision = "retain_historical"
        elif destination.startswith("NumStability.Source."):
            decision = "move_source"
        else:
            decision = "move_reusable"
        route_lines.append("\t".join((
            name,
            declaration.module,
            destination,
            decision,
            declaration.kind,
            declaration.visibility,
            command.root,
            str(command.start_line),
        )))

    generated_imports = dict(dependencies)
    generated_imports.update({module: set(imports) for module, imports in LOCATORS.items()})
    generated_imports.update(all_modules)
    generated_representatives = dict(representatives)
    generated_representatives.update(LOCATOR_REPRESENTATIVES)
    for module, imports in all_modules.items():
        generated_representatives[module] = generated_representatives[sorted(imports)[0]]

    test_payloads = {}
    test_rows = ["kind\timport_module\ttest_path\trepresentatives"]
    for index, module in enumerate(sorted(generated_imports), 1):
        representative = generated_representatives[module]
        relative = Path(f"NumStabilityTest/Reorganization/W05/Canonical/C{index:03d}.lean")
        test_payloads[relative] = f"import {module}\n\n#check {representative}\n"
        test_rows.append(f"canonical\t{module}\t{relative.as_posix()}\t{representative}")

    for index, owner in enumerate(OWNERS, 1):
        by_destination = defaultdict(list)
        for command in owner_commands[owner]:
            destination = final_owner[command.declarations[0]]
            by_destination[destination].extend(
                name for name in command.declarations
                if declarations[name].visibility == "public" and not name.startswith("_private.")
            )
        checks = [sorted(names)[0] for _, names in sorted(by_destination.items()) if names]
        relative = Path(f"NumStabilityTest/Reorganization/W05/Compatibility/O{index:02d}.lean")
        test_payloads[relative] = f"import {owner}\n\n" + "".join(f"#check {name}\n" for name in checks)
        test_rows.append(f"compatibility\t{owner}\t{relative.as_posix()}\t{','.join(checks)}")

    focused = {
        Path("NumStabilityTest/Reorganization/W05/Focused/Sylvester.lean"): (
            {
                f"{A}.Equation.All",
                f"{A}.BackwardError.All",
                f"{A}.Conditioning.All",
                f"{A}.Perturbation.All",
                f"{A}.GeneralizedEquations.All",
            },
            (
                "NumStability.sylvesterOp",
                "NumStability.sylvester_perturbation_bound",
                "NumStability.sylvesterInverseOpBound_of_sepLowerBound",
            ),
        ),
        Path("NumStabilityTest/Reorganization/W05/Focused/Schur.lean"): (
            {f"{N}.LinearOperators.Schur.All"},
            (
                "NumStability.real_quasi_schur",
                "NumStability.schur_triangulation",
            ),
        ),
        Path("NumStabilityTest/Reorganization/W05/Focused/InverseBounds.lean"): (
            {f"{N}.SingularValues.InverseBounds.All", COND_SINGULAR},
            (
                "NumStability.sigmaMin_mul_vecNorm2_le_matMulVec",
                "NumStability.sepLowerBound_of_sylvesterOp_sigmaMin",
            ),
        ),
    }
    for relative, (imports, checks) in focused.items():
        test_payloads[relative] = (
            "".join(f"import {module}\n" for module in sorted(imports))
            + "\n"
            + "".join(f"#check {name}\n" for name in checks)
        )
        test_rows.append(
            f"focused\t{','.join(sorted(imports))}\t{relative.as_posix()}\t{','.join(checks)}"
        )

    if len(generated_imports) != 79 or len(test_payloads) != 92:
        raise MigrationError(
            f"unexpected generated/test inventory: modules={len(generated_imports)}, tests={len(test_payloads)}"
        )

    if not args.write:
        print(json.dumps({
            "declarations": len(declarations),
            "retained": counts["retained"],
            "moved_reusable": counts["reusable"],
            "moved_source": counts["source"],
            "route_modules": len(route_modules),
            "locators": len(LOCATORS),
            "all_modules": len(all_modules),
            "canonical_tests": len(generated_imports),
            "compatibility_tests": len(OWNERS),
            "focused_tests": len(focused),
        }, indent=2))
        return 0

    frozen_sources = {}
    for owner, relative in source_paths.items():
        payload = engine.git(root, "show", f"{BASE}:{relative}", binary=True)
        if not isinstance(payload, bytes):
            raise MigrationError(f"failed to read frozen bytes for {owner}")
        frozen_sources[owner] = payload.decode("utf-8")

    for module in sorted(route_modules):
        payload = render_route(
            engine,
            module,
            route_commands[module],
            owner_commands,
            frozen_sources,
            dependencies[module],
            route_owner_order[module],
        )
        engine.safe_write(root, engine.module_path(module), payload, allowed_writes)
    for module, imports in sorted(LOCATORS.items()):
        payload = module_doc(
            module,
            imports,
            "Source locator for Higham's numbered presentation; the formal content lives in reusable Schur modules.",
        )
        engine.safe_write(root, engine.module_path(module), payload, allowed_writes)
    for module, imports in sorted(all_modules.items()):
        payload = module_doc(module, imports, "W05 reviewed discovery entry point.")
        engine.safe_write(root, engine.module_path(module), payload, allowed_writes)

    for owner in OWNERS:
        retained_roots = {
            command.root for command in owner_commands[owner]
            if command.decision == "retain_historical"
        }
        moved_modules = {
            intended[(command.owner, command.root)]
            for command in owner_commands[owner]
            if command.decision == "move_candidate"
        }
        if retained_roots:
            imports = engine.direct_imports(root, owner)
            imports.update(moved_modules)
            payload = module_doc(
                owner,
                imports,
                "Historical compatibility facade. The genuine-private reverse closure remains here with its original declaration identity.",
            ) + "\n" + render_subset(
                engine,
                frozen_sources[owner],
                owner_commands[owner],
                retained_roots,
            )
        else:
            # Preserve the historical module's direct import surface as well
            # as its own relocated declarations.  W06 legitimately imports
            # some compatibility owners transitively (notably
            # InverseOpNorm2 -> Higham16Psi/Higham16Lyapunov).
            imports = engine.direct_imports(root, owner)
            imports.update(moved_modules)
            payload = module_doc(
                owner,
                imports,
                "Historical compatibility facade for the W05 semantic modules.",
            )
        engine.safe_write(root, Path(source_paths[owner]), payload, allowed_writes)

    for relative, payload in sorted(test_payloads.items()):
        engine.safe_write(root, relative, payload, allowed_writes)
    engine.safe_write(
        root,
        Path("docs/architecture/deliveries/W05/DECLARATION_ROUTES.tsv"),
        "\n".join(route_lines) + "\n",
        allowed_writes,
    )
    engine.safe_write(
        root,
        Path("docs/architecture/deliveries/W05/TEST_MATRIX.tsv"),
        "\n".join(test_rows) + "\n",
        allowed_writes,
    )
    print(
        f"wrote {len(route_modules)} declaration leaves, {len(LOCATORS)} locators, "
        f"{len(all_modules)} entry points, and {len(test_payloads)} tests"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MigrationError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
