#!/usr/bin/env python3
"""Generate the command-preserving W07 stationary-iteration migration.

The generator consumes the immutable C0007 owner blobs, the active P0012
projection, and C0007 ``.ilean`` command spans.  Only declarations from
``StationaryIteration`` move.  The other four owners are documented in place
and retained for their B0011 ``classify;document`` review.  Whole Lean commands
are copied byte-for-byte, generated families remain indivisible, the exact
private reverse closure remains at the historical path, and imports are
derived from typed declaration edges.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


BASE = "9eb534a06db267203c2b9b88227edd44fc64f5db"
BRANCH = "codex/reorg-2026-08-w07-stationary-ch17"
SELECTOR_SHA256 = "478EFA94CE2311ECD54A7AA4A155336EF3DB8219BFA42E137BA7C37D0D97176A"
PROJECTION_SHA256 = "9B683940DE4C94D17E48E200D1F10594EB26614CFD2AEF2BCB036F667BB5159C"
C0007_RAW_SHA256 = "80AE3FBB3948104C60FF7EA80E899CC11CE542D0A772EA087375C00EB0ED9ED3"
PLAN_ENGINE_SHA256 = "E353E4BE155CE70D33E272414C4C41CC2E6B3A0C8A8C9618A96CD868558D0BFD"
MIGRATION_ENGINE_SHA256 = "3DF117CD4C074B69068F25C196D3112191DA96F5E67B16B6E7888D6FC9A29BBA"
EXPECTED_DECLARATIONS = 252
EXPECTED_COMMANDS = 228
EXPECTED_PRIVATE = 8
EXPECTED_GRAPH_FLOOR = 31
EXPECTED_ACTUAL_RETAINED = 116
EXPECTED_RELOCATED = 136
EXPECTED_REUSABLE = 47
EXPECTED_SOURCE = 89
EXPECTED_SIGNATURE_EDGES = 800
EXPECTED_BODY_EDGES = 1_400
EXPECTED_UNION_EDGES = 1_474
PRIVATE_PAYLOAD_SHA256 = "6A1B37537E0002E89B1B88F2BED03C6F7A701936A237FF33A49DFBD58E76E2B7"

MAIN_OWNER = "NumStability.Algorithms.StationaryIteration"
OWNERS = (
    MAIN_OWNER,
    "NumStability.Algorithms.StationaryIterationDrazin",
    "NumStability.Algorithms.StationaryIterationRounded",
    "NumStability.Algorithms.StationaryIterationSemiconvergent",
    "NumStability.Algorithms.StationaryIterationSemiconvergentExistence",
)
OWNER_SET = set(OWNERS)
EXPECTED_ILEAN_SHA256 = {
    MAIN_OWNER: "C37117C75CB247217E3E932A58A64E44AB4A288AA97ADA2AFEB05C306FEFBFAD",
    "NumStability.Algorithms.StationaryIterationDrazin": "478793EDFDE374747084AA081C0602413686F4D3D585F5CC03803AD37AD28930",
    "NumStability.Algorithms.StationaryIterationRounded": "F06718301AE21AAF813A098A2CB734F74137D09ECEE405633F25191AFC7DF690",
    "NumStability.Algorithms.StationaryIterationSemiconvergent": "38685DFB688F68C9E98BC2BC53B926BB31F10DD62EFBDC563C9BDDCA374E87C2",
    "NumStability.Algorithms.StationaryIterationSemiconvergentExistence": "097C658A42A08CCA76D31E33FE93653438978DA333AC773419A37508FCEC1AB8",
}

A = "NumStability.Algorithms.LinearSystems.Iterative.Stationary"
S = "NumStability.Source.Higham.Chapter17"

R_SPLIT_CORE = f"{A}.Splittings.Core.Definitions"
R_SPLIT_SCALING = f"{A}.Splittings.Scaling.Diagonal"
R_RECURRENCE = f"{A}.Recurrences.Affine.Unrolling"
R_EXECUTION = f"{A}.Execution.Computed.Model"
R_PROJECTOR = f"{A}.Projectors.Drazin.Algebra"
R_CONVERGENCE = f"{A}.Convergence.Singular.FixedSubspaces"
R_LOCAL = f"{A}.ErrorAnalysis.Local.OneStep"
R_FORWARD = f"{A}.ErrorAnalysis.Forward.ComplementDecomposition"
R_RESIDUAL = f"{A}.ErrorAnalysis.Residual.Identities"

Q01 = f"{S}.Equation01.ComputedIteration.Results"
Q02 = f"{S}.Equation02.LocalError.Results"
Q03 = f"{S}.Equation03.ComputedRecurrence.Results"
Q04 = f"{S}.Equation04.FixedPoint.Results"
Q05 = f"{S}.Equation05.ErrorExpansion.Results"
Q06 = f"{S}.Equation06.ComponentwiseForward.Results"
Q07 = f"{S}.Equation07.NormwiseGrowth.Results"
Q08 = f"{S}.Equation08.NormwiseForward.Results"
Q09 = f"{S}.Equation09.ComponentwiseGrowth.Results"
Q10 = f"{S}.Equation10.LocalErrorSimplification.Results"
Q12 = f"{S}.Equation12.PartialSumBound.Results"
Q13 = f"{S}.Equation13.ComponentwiseForward.Results"
Q15 = f"{S}.Equation15.NormwiseForward.Results"
Q16 = f"{S}.Equation16.Jacobi.Results"
Q17 = f"{S}.Equation17.SOR.Results"
Q18 = f"{S}.Equation18.ResidualRecurrence.Results"
Q19 = f"{S}.Equation19.ResidualBound.Results"
Q20 = f"{S}.Equation20.ResidualSigma.Results"
Q21 = f"{S}.Equation21.SingularIteration.Results"
Q27 = f"{S}.Equation27.SingularErrorSplit.Results"
Q28 = f"{S}.Equation28.SingularErrorSplit.Results"
Q29 = f"{S}.Equation29.SingularSource.Results"
Q33 = f"{S}.Equation33.StoppingTests.Results"
SEC02 = f"{S}.Section02.ScaleIndependence.Results"
SEC04 = f"{S}.Section04.PrintedConclusions.Results"


REUSABLE_GROUPS = {
    R_SPLIT_CORE: {
        "SplittingSpec", "iterMatrix", "dualIterMatrix", "AG_eq_HA",
        "A_matPow_G_eq_matPow_H_A",
    },
    R_SPLIT_SCALING: {
        "stationaryRowColumnScale", "stationaryScaledInverse",
        "diagMatrix_mul_diagMatrix_eq_id", "stationaryRowColumnScale_apply",
    },
    R_RECURRENCE: {
        "affine_fixed_point_unroll", "matMulVec_finset_sum_right",
        "affine_recurrence_unroll",
    },
    R_EXECUTION: {"ComputedIteration"},
    R_PROJECTOR: {
        "IndexOneDrazinInverse", "stationaryDrazinRangeProjector",
        "stationaryDrazinFixedProjector",
        "stationaryDrazinRangeProjector_idempotent",
        "stationaryDrazinRangeProjector_matSub_id_mul_left",
        "stationaryDrazinRangeProjector_matSub_id_mul_right",
        "stationaryDrazinRangeProjector_mul_fixedProjector_eq_zero",
        "stationaryDrazinFixedProjector_mul_rangeProjector_eq_zero",
    },
    R_CONVERGENCE: {
        "matPow_fixed_of_matMulVec_fixed", "matPow_mul_fixed_of_matMul_fixed",
        "matPow_comm_of_matMul_comm",
    },
    R_LOCAL: {"one_step_error"},
    R_FORWARD: {"matMulVec_add_complement_apply"},
    R_RESIDUAL: {"residual_eq_A_error", "A_matMul_Minv_eq_sub"},
}

SOURCE_GROUPS = {
    SEC02: {
        "stationaryRowColumnScale_splittingSpec",
        "stationaryScaledIterMatrix_similarity",
        "stationaryScaledIterMatrix_charpoly_eq",
    },
    Q01: {
        "SourceComputedIteration", "computedIteration_of_sourceComputedIteration",
        "sourceComputedIteration_step_affine",
    },
    Q02: {"LocalErrorBound"},
    Q03: {"sourceComputedIteration_finite_sum"},
    Q04: {"stationary_solution_fixed_point", "stationary_solution_finite_sum"},
    Q05: {
        "one_step_error_source", "sourceComputedIteration_error_finite_sum",
        "normwise_one_step_bound",
    },
    Q06: {"componentwise_forward_bound"},
    Q07: {
        "NormwiseIterateGrowthValues", "normwiseIterateGrowth",
        "NormwiseIterateGrowthBound", "normwiseIterateGrowth_ratio_le",
        "normwiseIterateGrowthBound_of_sSup",
    },
    Q08: {"normwise_forward_bound"},
    Q09: {
        "ComponentwiseIterateGrowthValues", "componentwiseIterateGrowth",
        "ComponentwiseIterateGrowthBound", "componentwiseIterateGrowth_ratio_le",
        "componentwiseIterateGrowthBound_of_sSup",
    },
    Q10: {"local_error_simplified", "local_error_normwise_simplified"},
    Q12: {"PartialSumBound"},
    Q13: {
        "main_forward_bound", "finiteForwardCorrection", "mainForwardBoundVector",
        "mainForwardBoundVector_nonneg", "finiteForwardCorrection_nonneg",
        "finiteForwardCorrection_le_mainForwardBoundVector",
        "finiteForwardCorrection_norm_bound",
    },
    Q15: {"finite_norm_form_forward_bound"},
    Q16: {
        "jacobi_splitting_abs", "jacobiForwardBoundVector",
        "mainForwardBoundVector_eq_jacobiForwardBoundVector",
        "finite_norm_form_jacobi_forward_bound", "jacobiForwardBoundVector_nonneg",
    },
    Q17: {
        "sor_splitting_bound", "sorForwardFactor", "sorForwardFactor_nonneg",
        "mainForwardBoundVector_le_sorForwardBoundVector",
        "mainForwardBoundVector_norm_le_sorForwardBoundVector",
        "finite_norm_form_sor_forward_bound", "sorForwardFactor_one",
        "finite_norm_form_gaussSeidel_forward_bound",
    },
    Q18: {"one_step_residual", "residual_finite_sum"},
    Q19: {"normwise_one_step_residual_bound", "normwise_residual_bound"},
    Q20: {
        "finiteResidualSigmaMatrix", "finiteResidualSigma",
        "residualSigmaTsumMatrix", "residualSigmaTsum",
        "residualSigmaTsumMatrix_apply", "residualSigmaTsumMatrix_eq_of_hasSum",
        "residualSigmaTsum_eq_infNorm_of_hasSum",
        "residualSigmaTsum_le_of_row_sum_le", "ResidualSigmaValues",
        "residualSigmaSup", "residualSigmaSup_le_of_finiteResidualSigma_le",
        "diagonalResidualRatioMax", "diagonalResidualRatio_le_max",
        "diagonalResidualRatioMax_nonneg", "normwise_residual_sigma_finite_bound",
    },
    Q21: {"singular_stationary_iterate_finite_sum", "matMulVec_neumannSum_range"},
    Q27: {"singular_error_split_finite"},
    Q28: {"singularErrorSourceTerm"},
    Q29: {
        "stationaryLocalErrorSourceVector", "singularErrorSourceNormSum",
        "singularErrorSourceComponentBound",
    },
    Q33: {
        "stopping_test_rhs_backward_subordinate",
        "stopping_test_matrix_backward_subordinate",
        "stopping_test_mixed_backward_subordinate",
        "stopping_test_rhs_backward_componentwise",
        "stopping_test_matrix_backward_componentwise",
        "stopping_test_mixed_backward_componentwise",
    },
    SEC04: {
        "singular_consistent_source_term_eq_I_sub_G",
        "singular_consistent_second_term_telescope",
        "singular_stationary_iterate_consistent_split",
    },
}


class MigrationError(RuntimeError):
    pass


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def run_git(repo: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise MigrationError(f"git {' '.join(arguments)} failed: {detail}")
    return result.stdout.decode("utf-8", errors="strict").strip()


def load_module(path: Path, expected_hash: str, name: str):
    found = sha256_file(path)
    if found != expected_hash:
        raise MigrationError(
            f"engine hash differs for {path}: expected {expected_hash}, found {found}"
        )
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise MigrationError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def read_selector(path: Path) -> dict[str, str]:
    if sha256_file(path) != SELECTOR_SHA256:
        raise MigrationError("W07 selector hash differs")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["module", "path"] or len(rows) != 6:
        raise MigrationError("W07 selector must contain exactly five owners")
    owners = tuple(row[0] for row in rows[1:])
    if owners != OWNERS:
        raise MigrationError(f"W07 selector owners differ: {owners}")
    return {row[0]: row[1] for row in rows[1:]}


def configure_engines(plan, migration):
    plan.FROZEN_BASE = BASE
    plan.P0002_SHA256 = PROJECTION_SHA256
    plan.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    plan.EXPECTED_SIGNATURE_EDGES = EXPECTED_SIGNATURE_EDGES
    plan.EXPECTED_BODY_EDGES = EXPECTED_BODY_EDGES
    plan.EXPECTED_PHYSICAL_DECLARATIONS = EXPECTED_DECLARATIONS
    plan.EXPECTED_PRIVATE_SEEDS = EXPECTED_PRIVATE
    plan.EXPECTED_RETAINED_COMMANDS = EXPECTED_GRAPH_FLOOR
    plan.PHYSICAL_OWNERS = OWNERS
    migration.BASE = BASE
    migration.P0002_SHA256 = PROJECTION_SHA256
    migration.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    migration.EXPECTED_COMMANDS = EXPECTED_COMMANDS
    migration.EXPECTED_RETAINED = EXPECTED_ACTUAL_RETAINED
    migration.PHYSICAL = OWNERS
    migration.PHYSICAL_SET = OWNER_SET


def read_model(repo, control, ilean_root, source_paths, plan):
    projection = (
        control / "docs/architecture/phases/2026-08-repository-reorganization"
        / "projections/P0012.tsv.gz"
    )
    declarations, edges = plan.read_projection(projection)
    typed = Counter(edge.kind for edge in edges)
    union = len({(edge.source, edge.target) for edge in edges})
    if typed != Counter(signature=EXPECTED_SIGNATURE_EDGES, body=EXPECTED_BODY_EDGES):
        raise MigrationError(f"P0012 typed counts differ: {dict(typed)}")
    if union != EXPECTED_UNION_EDGES:
        raise MigrationError(f"P0012 union count differs: {union}")
    if {item.module for item in declarations.values()} != OWNER_SET:
        raise MigrationError("P0012 declaration owners differ from W07")

    sources = {}
    evidence = {}
    commands = {}
    for owner in OWNERS:
        payload, source, blob = plan.read_base_source(
            repo, BASE, source_paths[owner]
        )
        sources[owner] = source
        relative_ilean = plan.module_path(owner, ".ilean")
        ilean_path = ilean_root / relative_ilean
        ilean, ilean_hash = plan.read_ilean(ilean_path, owner)
        if ilean_hash != EXPECTED_ILEAN_SHA256[owner]:
            raise MigrationError(
                f"{owner} .ilean differs: expected {EXPECTED_ILEAN_SHA256[owner]}, "
                f"found {ilean_hash}"
            )
        owner_commands = plan.commands_from_ilean(owner, ilean, source)
        overlap = set(commands).intersection(owner_commands)
        if overlap:
            raise MigrationError(f"duplicate command keys: {sorted(overlap)[:3]}")
        commands.update(owner_commands)
        evidence[owner] = plan.OwnerEvidence(
            module=owner,
            source_path=source_paths[owner],
            source_blob_sha1=blob,
            source_sha256=sha256_bytes(payload),
            ilean_path=(Path(".lake/build/lib/lean") / relative_ilean).as_posix(),
            ilean_sha256=ilean_hash,
        )
    declaration_commands = plan.build_command_map(
        declarations, edges, commands, sources
    )
    if len(commands) != EXPECTED_COMMANDS:
        raise MigrationError(f"mapped {len(commands)} commands, expected {EXPECTED_COMMANDS}")
    depth, chosen_target, chosen_witness = plan.compute_closure(
        declarations, edges, commands, declaration_commands
    )
    graph_declarations = {
        name for key in depth for name in commands[key].declarations
    }
    if len(graph_declarations) != EXPECTED_GRAPH_FLOOR:
        raise MigrationError("private reverse closure count differs")
    payload = ("\n".join(sorted(graph_declarations)) + "\n").encode("utf-8")
    if sha256_bytes(payload) != PRIVATE_PAYLOAD_SHA256:
        raise MigrationError("private reverse-closure payload hash differs")
    return (
        declarations, edges, sources, evidence, commands,
        declaration_commands, depth, chosen_target, chosen_witness,
    )


def route_lookup() -> dict[str, str]:
    result = {}
    for module, names in list(REUSABLE_GROUPS.items()) + list(SOURCE_GROUPS.items()):
        for name in names:
            if name in result:
                raise MigrationError(f"duplicate route for {name}")
            result[name] = module
    if len(REUSABLE_GROUPS) != 9 or len(SOURCE_GROUPS) != 25:
        raise MigrationError("reviewed route-module partition differs")
    return result


DIRECT_IMPORT_RE = re.compile(
    r"(?m)^(?:public[ \t]+|private[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)


def direct_imports(source: str) -> set[str]:
    return set(DIRECT_IMPORT_RE.findall(source))


def topological_cycle(graph: dict[str, set[str]]) -> list[str] | None:
    state = {}
    stack = []

    def visit(node):
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


def assign_routes(commands, graph_floor):
    reviewed = route_lookup()
    actual_retained = set(graph_floor)
    actual_retained.update(
        key for key, command in commands.items() if command.owner != MAIN_OWNER
    )
    intended = {}
    seen_movable = set()
    for key, command in commands.items():
        if key in actual_retained:
            intended[key] = command.owner
            continue
        if command.owner != MAIN_OWNER:
            raise MigrationError(f"classify-only owner unexpectedly movable: {command.owner}")
        short = command.root.removeprefix("NumStability.")
        if short not in reviewed:
            raise MigrationError(f"unrouted StationaryIteration command: {command.root}")
        intended[key] = reviewed[short]
        seen_movable.add(short)
    if seen_movable != set(reviewed):
        raise MigrationError(
            f"reviewed route names differ: missing={sorted(set(reviewed)-seen_movable)}, "
            f"extra={sorted(seen_movable-set(reviewed))}"
        )
    retained_declarations = sum(len(commands[key].declarations) for key in actual_retained)
    if retained_declarations != EXPECTED_ACTUAL_RETAINED:
        raise MigrationError(f"actual retention differs: {retained_declarations}")
    return intended, actual_retained


def compute_dependencies(
    commands, intended, declarations, edges, declaration_commands,
    sources, full_modules,
):
    final_owner = {}
    for key, command in commands.items():
        for name in command.declarations:
            final_owner[name] = intended[key]
    route_commands = defaultdict(list)
    for key, command in commands.items():
        if intended[key] != command.owner:
            route_commands[intended[key]].append(command)
    if len(route_commands) != 34:
        raise MigrationError(f"expected 34 canonical modules, found {len(route_commands)}")
    outgoing = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge)
    dependencies = {}
    original_imports = direct_imports(sources[MAIN_OWNER])
    for module, owned in route_commands.items():
        imports = {item for item in original_imports if item not in OWNER_SET}
        for command in owned:
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target_module = final_owner.get(
                        edge.target, full_modules.get(edge.target)
                    )
                    if not target_module or target_module == module:
                        continue
                    if target_module in OWNER_SET:
                        raise MigrationError(
                            f"canonical {name} depends on retained {edge.target}"
                        )
                    if (
                        target_module.startswith("NumStability.Source.")
                        and not module.startswith("NumStability.Source.")
                    ):
                        raise MigrationError(
                            f"reusable-to-Source declaration edge {name} -> {edge.target}"
                        )
                    if target_module.startswith("NumStability."):
                        imports.add(target_module)
        imports.discard(MAIN_OWNER)
        dependencies[module] = imports
    graph = {
        module: {target for target in imports if target in route_commands}
        for module, imports in dependencies.items()
    }
    cycle = topological_cycle(graph)
    if cycle:
        raise MigrationError("canonical dependency cycle: " + " -> ".join(cycle))
    return final_owner, route_commands, dependencies


def insert_doc(payload: str, title: str, paragraph: str) -> str:
    lines = payload.splitlines(keepends=True)
    import_lines = [
        index for index, line in enumerate(lines)
        if line.startswith("import ")
        or line.startswith("public import ")
        or line.startswith("private import ")
    ]
    cursor = import_lines[-1] + 1 if import_lines else 0
    doc = f"\n/-!\n# {title}\n\n{paragraph}\n-/\n"
    return "".join(lines[:cursor]) + doc + "".join(lines[cursor:])


def scoped_write(root: Path, relative: Path, payload: str, allowed, check: bool):
    posix = relative.as_posix()
    if not any(
        posix == item if kind == "exact" else posix.startswith(item)
        for kind, item in allowed
    ):
        raise MigrationError(f"refusing out-of-contract write: {posix}")
    path = root / relative
    if check:
        if not path.is_file() or path.read_text(encoding="utf-8") != payload:
            raise MigrationError(f"generated file is missing or stale: {posix}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8", newline="\n")


def private_rows(
    declarations, commands, evidence, graph_floor, actual_retained,
    depth, chosen_target, chosen_witness,
):
    output = io.StringIO(newline="")
    writer = csv.writer(output, delimiter="\t", lineterminator="\n")
    writer.writerow(["format", "1"])
    metadata = {
        "generated_by": "docs/architecture/deliveries/W07/GENERATE_MIGRATION.py",
        "base_revision": BASE,
        "projection_id": "P0012",
        "projection_sha256": PROJECTION_SHA256,
        "selector_sha256": SELECTOR_SHA256,
        "owner_count": "5",
        "selected_declaration_count": str(EXPECTED_DECLARATIONS),
        "command_count": str(EXPECTED_COMMANDS),
        "private_declaration_count": str(EXPECTED_PRIVATE),
        "graph_reverse_closure_count": str(EXPECTED_GRAPH_FLOOR),
        "actual_retained_declaration_count": str(EXPECTED_ACTUAL_RETAINED),
        "private_payload_sha256": PRIVATE_PAYLOAD_SHA256,
        "coordinate_convention": "lines=1-based; columns=UTF-16-code-units-0-based; end=half-open",
    }
    for key, value in metadata.items():
        writer.writerow(["metadata", key, value])
    writer.writerow([
        "columns", "owner", "module", "source_path", "source_blob_sha1",
        "source_sha256", "ilean_path", "ilean_sha256", "command_count",
        "graph_floor_command_count", "actual_retained_command_count",
        "private_declaration_count",
    ])
    writer.writerow([
        "columns", "command", "owner_module", "command_root", "span_origin",
        "start_line", "start_column", "end_line", "end_column", "decision",
        "reason", "closure_depth", "witness_owner", "witness_root",
        "witness_edge_kind", "witness_source_declaration",
        "witness_target_declaration", "selected_declaration_count",
        "private_declaration_count", "selected_declarations_json",
    ])
    for owner in OWNERS:
        owned = [command for command in commands.values() if command.owner == owner]
        writer.writerow([
            "owner", owner, evidence[owner].source_path,
            evidence[owner].source_blob_sha1, evidence[owner].source_sha256,
            evidence[owner].ilean_path, evidence[owner].ilean_sha256,
            str(len(owned)), str(sum(command.key in graph_floor for command in owned)),
            str(sum(command.key in actual_retained for command in owned)),
            str(sum(
                declarations[name].visibility == "private"
                for command in owned for name in command.declarations
            )),
        ])
    for owner in OWNERS:
        owned = sorted(
            (command for command in commands.values() if command.owner == owner),
            key=lambda command: (command.start_line, command.start_column, command.root),
        )
        for command in owned:
            key = command.key
            target_owner = target_root = witness_kind = witness_source = witness_target = ""
            closure_depth = ""
            if key in graph_floor:
                decision = "retain_historical"
                closure_depth = str(depth[key])
                if depth[key] == 0:
                    reason = "private_seed"
                else:
                    reason = "depends_on_private_closure"
                    target_owner, target_root = chosen_target[key]
                    witness_kind, witness_source, witness_target = chosen_witness[
                        (key, chosen_target[key])
                    ]
            elif key in actual_retained:
                decision, reason = "retain_historical", "classify_document_only_owner"
            else:
                decision, reason = "relocate", "reviewed_semantic_route"
            private_count = sum(
                declarations[name].visibility == "private"
                for name in command.declarations
            )
            writer.writerow([
                "command", owner, command.root, command.span_origin,
                str(command.start_line + 1), str(command.start_column),
                str(command.end_line + 1), str(command.end_column), decision, reason,
                closure_depth, target_owner, target_root, witness_kind,
                witness_source, witness_target, str(len(command.declarations)),
                str(private_count),
                json.dumps(command.declarations, ensure_ascii=False, separators=(",", ":")),
            ])
    return output.getvalue()


def build_tests(declarations, commands, intended, route_commands, final_owner):
    tests = {}
    rows = [["test_module", "kind", "imports", "covers", "representatives"]]

    def add(module, kind, imports, covers, representatives):
        imports = tuple(sorted(set(imports)))
        relative = Path(*module.split(".")).with_suffix(".lean")
        payload = "".join(f"import {item}\n" for item in imports)
        payload += f"\n/-!\n# W07 {covers} test\n-/\n\n"
        payload += "".join(f"#check @{name}\n" for name in representatives)
        tests[relative] = payload
        rows.append([
            module, kind, ",".join(imports), covers,
            ",".join(representatives),
        ])

    representatives = {}
    for module, owned in route_commands.items():
        public = sorted(
            name for command in owned for name in command.declarations
            if declarations[name].visibility == "public"
            and not name.startswith("_private.")
        )
        if not public:
            raise MigrationError(f"canonical module lacks public representative: {module}")
        representatives[module] = public[0]
    for index, module in enumerate(sorted(route_commands), 1):
        kind = "canonical-source" if module.startswith("NumStability.Source.") else "canonical-reusable"
        add(
            f"NumStabilityTest.Reorganization.W07.Canonical.C{index:03d}",
            kind, (module,), module, (representatives[module],),
        )

    old_representatives = {
        MAIN_OWNER: ("NumStability.SplittingSpec", "NumStability.sigma_bound"),
        OWNERS[1]: ("NumStability.bottomProjector", "NumStability.eq_17_31_normwise_bound"),
        OWNERS[2]: ("NumStability.stationaryRoundedRhs", "NumStability.flStationaryIterationUpper_actual_forward_bound"),
        OWNERS[3]: ("NumStability.topProjector", "NumStability.matPow_G_tendsto_oneEigenProjector"),
        OWNERS[4]: ("NumStability.blockJ", "NumStability.semiconvergent_block_form_exists"),
    }
    for owner in OWNERS:
        leaf = owner.rsplit(".", 1)[-1]
        add(
            f"NumStabilityTest.Reorganization.W07.OldPath.{leaf}",
            "old-path", (owner,), leaf, old_representatives[owner],
        )

    focused = [
        ("ReusableIteration", (R_SPLIT_CORE, R_RECURRENCE, R_EXECUTION),
         ("NumStability.SplittingSpec", "NumStability.affine_recurrence_unroll", "NumStability.ComputedIteration")),
        ("RoundedExecution", (OWNERS[2],),
         ("NumStability.RoundedStationarySolveCertificate", "NumStability.flStationaryIterationUpper_actual_forward_bound")),
        ("SemiconvergenceProjector", (R_PROJECTOR, OWNERS[3]),
         ("NumStability.IndexOneDrazinInverse", "NumStability.oneEigenProjector")),
        ("Drazin", (R_PROJECTOR, OWNERS[1]),
         ("NumStability.stationaryDrazinRangeProjector", "NumStability.indexOneDrazinInverse_unique")),
        ("Chapter17Boundary", (Q01, Q13, Q20, Q33),
         ("NumStability.SourceComputedIteration", "NumStability.main_forward_bound", "NumStability.finiteResidualSigma", "NumStability.stopping_test_mixed_backward_componentwise")),
        ("PrivateRetention", (MAIN_OWNER, OWNERS[1]),
         ("NumStability.sigma_bound", "NumStability.stationaryDrazin_matPow_vec_split", "NumStability.eq_17_31_normwise_bound")),
        ("ProtectedW06", ("NumStabilityTest.Reorganization.W06.Focused.ProtectedW07",),
         ("NumStability.stationaryDrazinRangeProjector",)),
        ("AcceptedChapter17Consumers", (
            f"{S}.Equation08", f"{S}.Equation12", f"{S}.Equation15",
            f"{S}.Equation16", f"{S}.Equation17", f"{S}.Equation20",
        ), (
            "NumStability.summable_infNorm_matPow",
            "NumStability.partialSumBound_cALiteral",
            "NumStability.literal_norm_form_forward_bound",
            "NumStability.literal_norm_form_jacobi_forward_bound",
            "NumStability.literal_norm_form_sor_forward_bound",
            "NumStability.residualSigmaTsum_eq_residualSigmaSup",
        )),
        ("AcceptedSemiconvergentConsumer", (
            "NumStability.Analysis.SemiconvergentBlockFormExists",
        ), (
            "NumStability.semiconvergent_block_form_exists_of_triangular_complement",
            "NumStability.matPow_G_tendsto_oneEigenProjector_of_triangular_complement_diag_conv",
        )),
    ]
    for name, imports, reps in focused:
        add(
            f"NumStabilityTest.Reorganization.W07.Focused.{name}",
            "focused", imports, name, reps,
        )
    return tests, rows


def main() -> int:
    script = Path(__file__).resolve()
    default_repo = script.parents[4]
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=default_repo)
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--ilean-root", type=Path)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write and args.check:
        raise MigrationError("choose at most one of --write and --check")
    repo = args.repo_root.resolve()
    control = args.control_root.resolve()
    ilean_root = (args.ilean_root or (control / ".lake/build/lib/lean")).resolve()
    if run_git(repo, "rev-parse", f"{BASE}^{{commit}}") != BASE:
        raise MigrationError("C0007 base is unavailable")
    if run_git(repo, "branch", "--show-current") != BRANCH:
        raise MigrationError("wrong W07 worker branch")

    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    contract = json.loads((phase / "branches/B0011.json").read_text(encoding="utf-8"))
    projection_record = json.loads((phase / "projections/P0012.json").read_text(encoding="utf-8"))
    if (
        contract.get("status") != "active"
        or contract.get("base_sha") != BASE
        or contract.get("branch_name") != BRANCH
        or contract.get("lane_id") != "local-lane"
        or contract.get("owner_id") != "primary-human"
        or contract.get("operator_ids") != ["codex-local"]
        or projection_record.get("status") != "active"
    ):
        raise MigrationError("B0011/P0012 activation contract differs")
    source_paths = read_selector(phase / "selectors/W07.tsv")
    plan = load_module(
        repo / "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py",
        PLAN_ENGINE_SHA256, "w07_private_engine",
    )
    migration = load_module(
        repo / "docs/architecture/deliveries/W02/GENERATE_MIGRATION.py",
        MIGRATION_ENGINE_SHA256, "w07_migration_engine",
    )
    configure_engines(plan, migration)
    (
        declarations, edges, sources, evidence, commands,
        declaration_commands, depth, chosen_target, chosen_witness,
    ) = read_model(repo, control, ilean_root, source_paths, plan)
    intended, actual_retained = assign_routes(commands, set(depth))
    raw_graph = control / "benchmark-results/C0007-combined.tsv"
    if not raw_graph.is_file() or sha256_file(raw_graph) != C0007_RAW_SHA256:
        raise MigrationError("C0007 raw format-2 graph differs")
    full_modules = migration.read_full_declarations(raw_graph)
    final_owner, route_commands, dependencies = compute_dependencies(
        commands, intended, declarations, edges, declaration_commands,
        sources, full_modules,
    )

    reusable_count = sum(
        len(command.declarations)
        for module, owned in route_commands.items()
        if not module.startswith("NumStability.Source.")
        for command in owned
    )
    source_count = sum(
        len(command.declarations)
        for module, owned in route_commands.items()
        if module.startswith("NumStability.Source.")
        for command in owned
    )
    if reusable_count != EXPECTED_REUSABLE or source_count != EXPECTED_SOURCE:
        raise MigrationError(
            f"route totals differ: reusable={reusable_count}, source={source_count}"
        )

    converted = {}
    owner_commands = defaultdict(list)
    for key, command in commands.items():
        item = migration.Command(
            owner=command.owner, root=command.root,
            start_line=command.start_line + 1, start_column=command.start_column,
            end_line=command.end_line + 1, end_column=command.end_column,
            decision="retain_historical" if key in actual_retained else "move_candidate",
            declarations=tuple(command.declarations),
        )
        converted[key] = item
        owner_commands[command.owner].append(item)

    generated = {}
    for module, owned in sorted(route_commands.items()):
        keep = {command.root for command in owned}
        payload = migration.render_subset(
            sources[MAIN_OWNER], owner_commands[MAIN_OWNER], keep,
            dependencies[module],
        )
        tier = "Chapter 17 source correspondence" if module.startswith("NumStability.Source.") else "reusable stationary-iteration API"
        payload = insert_doc(
            payload, module,
            f"W07 canonical {tier}. Whole commands are copied unchanged from `{MAIN_OWNER}`; the historical path re-exports this module.",
        )
        generated[migration.module_path(module)] = payload

    main_retained_roots = {
        command.root for key, command in commands.items()
        if command.owner == MAIN_OWNER and key in actual_retained
    }
    moved_modules = {
        intended[key] for key, command in commands.items()
        if command.owner == MAIN_OWNER and key not in actual_retained
    }
    main_imports = direct_imports(sources[MAIN_OWNER]) | moved_modules
    main_payload = migration.render_subset(
        sources[MAIN_OWNER], owner_commands[MAIN_OWNER],
        main_retained_roots, main_imports,
    )
    main_payload = insert_doc(
        main_payload, MAIN_OWNER + " historical facade",
        "Historical declaration-bearing W07 facade. Eight genuine private declarations and the 29-node main-owner portion of their exact reverse closure retain their original identities here; every movable command is re-exported from canonical reusable or Chapter 17 modules.",
    )
    generated[Path(source_paths[MAIN_OWNER])] = main_payload

    owner_docs = {
        OWNERS[1]: "W07 classify/document-only Drazin and numbered Chapter 17 surface. B0011 does not authorize declaration relocation from this owner; its final mixed/reusable/source classification is requested from the integrator.",
        OWNERS[2]: "W07 classify/document-only rounded stationary-execution and Chapter 17 error-bound surface. B0011 does not authorize declaration relocation from this owner; its final classification is requested from the integrator.",
        OWNERS[3]: "W07 classify/document-only semiconvergence and projector surface. B0011 does not authorize declaration relocation from this owner; its final classification is requested from the integrator.",
        OWNERS[4]: "W07 classify/document-only semiconvergent block-form existence surface. B0011 does not authorize declaration relocation from this owner; its final classification is requested from the integrator.",
    }
    for owner in OWNERS[1:]:
        generated[Path(source_paths[owner])] = insert_doc(
            sources[owner], owner, owner_docs[owner]
        )

    tests, test_rows = build_tests(
        declarations, commands, intended, route_commands, final_owner
    )
    generated.update(tests)

    route_rows = [[
        "declaration", "kind", "visibility", "historical_owner",
        "destination_module", "tier", "disposition", "command_root", "start_line",
    ]]
    retention_rows = [[
        "declaration", "kind", "visibility", "historical_owner",
        "destination_module", "retention_reason", "private_floor",
        "closure_depth", "witness_source", "witness_target", "witness_edge_kind",
        "command_root", "start_line",
    ]]
    for name in sorted(declarations):
        declaration = declarations[name]
        key = declaration_commands[name]
        command = commands[key]
        destination = final_owner[name]
        if key in actual_retained:
            if key in depth:
                disposition = "retained_private_closure"
                reason = "private_seed" if depth[key] == 0 else "depends_on_private_closure"
                closure_depth = str(depth[key])
                witness_source = witness_target = witness_kind = ""
                if depth[key] > 0:
                    witness_kind, witness_source, witness_target = chosen_witness[
                        (key, chosen_target[key])
                    ]
            else:
                disposition = "retained_classify_only"
                reason = "classify_document_only_owner"
                closure_depth = witness_source = witness_target = witness_kind = ""
            tier = "historical-closure" if declaration.module == MAIN_OWNER else "unclassified-review"
            retention_rows.append([
                name, declaration.kind, declaration.visibility, declaration.module,
                destination, reason, "yes" if key in depth else "no",
                closure_depth, witness_source, witness_target, witness_kind,
                command.root, str(command.start_line + 1),
            ])
        elif destination.startswith("NumStability.Source."):
            tier, disposition = "source", "relocated"
        else:
            tier, disposition = "reusable", "relocated"
        route_rows.append([
            name, declaration.kind, declaration.visibility, declaration.module,
            destination, tier, disposition, command.root,
            str(command.start_line + 1),
        ])

    route_tsv = "\n".join("\t".join(row) for row in route_rows) + "\n"
    retention_tsv = "\n".join("\t".join(row) for row in retention_rows) + "\n"
    private_tsv = private_rows(
        declarations, commands, evidence, set(depth), actual_retained,
        depth, chosen_target, chosen_witness,
    )
    test_tsv = "\n".join("\t".join(row) for row in test_rows) + "\n"
    route_counts = Counter(final_owner.values())
    summary = {
        "canonical_modules": len(route_commands),
        "canonical_reusable_modules": len(REUSABLE_GROUPS),
        "canonical_source_modules": len(SOURCE_GROUPS),
        "classify_document_owner_declarations": 87,
        "commands": len(commands),
        "declarations": len(declarations),
        "focused_tests": 9,
        "graph_private_floor": EXPECTED_GRAPH_FLOOR,
        "old_path_tests": 5,
        "private_declarations": EXPECTED_PRIVATE,
        "relocated": EXPECTED_RELOCATED,
        "retained": EXPECTED_ACTUAL_RETAINED,
        "retained_classify_only_outside_floor": 85,
        "reusable": reusable_count,
        "route_declaration_counts": dict(sorted(route_counts.items())),
        "source": source_count,
        "tests": len(tests),
    }
    generated[Path("docs/architecture/deliveries/W07/DECLARATION_ROUTES.tsv")] = route_tsv
    generated[Path("docs/architecture/deliveries/W07/PRIVATE_CLOSURE.tsv")] = private_tsv
    generated[Path("docs/architecture/deliveries/W07/RETENTION.tsv")] = retention_tsv
    generated[Path("docs/architecture/deliveries/W07/TEST_MATRIX.tsv")] = test_tsv
    generated[Path("docs/architecture/deliveries/W07/ROUTE_SUMMARY.json")] = json.dumps(
        summary, indent=2, sort_keys=True
    ) + "\n"

    allowed = [
        (item["match"], item["path"])
        for item in contract["owned_paths"] + contract["destination_prefixes"]
    ]
    if not args.write and not args.check:
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0
    for relative, payload in sorted(generated.items(), key=lambda item: item[0].as_posix()):
        scoped_write(repo, relative, payload, allowed, args.check)
    action = "verified" if args.check else "wrote"
    print(f"{action} {len(generated)} generated files")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MigrationError, OSError, RuntimeError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
