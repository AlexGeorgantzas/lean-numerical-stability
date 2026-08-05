#!/usr/bin/env python3
"""Generate the command-preserving W11 RandNLA migration.

The generator consumes only the immutable C0006 source blobs, the active
P0011 projection and C0006 ``.ilean`` command spans.  It keeps the exact
reverse closure of the three genuine private declarations at historical
paths, routes reviewed paper-specific upper sets to the exact B0010 Source
prefixes, and writes all remaining commands to reusable RandNLA APIs.

Whole Lean commands are copied byte-for-byte.  No declaration, proof,
attribute, namespace, option, local instance, or generated family is rebuilt.
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
from collections import Counter, defaultdict, deque
from pathlib import Path


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
BRANCH = "codex/reorg-2026-08-w11-randnla"
SELECTOR_SHA256 = "24E3BD565946AECFDBAB9D2D21BF1201B86ECD16197F892E1B62A30162D9EE00"
PROJECTION_SHA256 = "0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2"
PLAN_ENGINE_SHA256 = "E353E4BE155CE70D33E272414C4C41CC2E6B3A0C8A8C9618A96CD868558D0BFD"
MIGRATION_ENGINE_SHA256 = "3DF117CD4C074B69068F25C196D3112191DA96F5E67B16B6E7888D6FC9A29BBA"
EXPECTED_DECLARATIONS = 3_354
EXPECTED_COMMANDS = 3_086
EXPECTED_PRIVATE = 3
EXPECTED_RETAINED_COMMANDS = 225
EXPECTED_RETAINED_DECLARATIONS = 225
EXPECTED_SOURCE_COMMANDS = 733
EXPECTED_SOURCE_DECLARATIONS = 807
EXPECTED_REUSABLE_COMMANDS = 2_128
EXPECTED_REUSABLE_DECLARATIONS = 2_322
EXPECTED_SIGNATURE_EDGES = 19_096
EXPECTED_BODY_EDGES = 26_201
EXPECTED_UNION_EDGES = 28_652
PRIVATE_PAYLOAD_SHA256 = "FAD5DC5D7CD80112157031E012D32593FBF33ACED6C1B9F94D60DEC55D1EA7F9"
LOW_RANK_COMPAT_ILEAN_SHA256 = "EB210E11ECBA7E2C21877E1B331126E6726E8DEA733B8D35D065844B0A1CBBBE"

LOW_RANK_C0006_IMPORTS = """import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
"""
LOW_RANK_COMPAT_IMPORT = "import NumStability.Algorithms.MatrixInversion\n"

R = "NumStability.Algorithms.RandomizedLinearAlgebra"
S = "NumStability.Source.DrineasMahoney.RandNLA2016"


class MigrationError(RuntimeError):
    pass


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def run_git(repo: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise MigrationError(f"git {' '.join(arguments)} failed: {detail}")
    return result.stdout.decode("utf-8", errors="strict").strip()


def load_module(path: Path, expected_hash: str, name: str):
    actual = sha256_file(path)
    if actual != expected_hash:
        raise MigrationError(
            f"engine hash differs for {path}: expected {expected_hash}, found {actual}"
        )
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise MigrationError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def read_selector(path: Path) -> tuple[tuple[str, ...], dict[str, str]]:
    if sha256_file(path) != SELECTOR_SHA256:
        raise MigrationError("W11 selector hash differs")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["module", "path"] or len(rows) != 19:
        raise MigrationError("W11 selector must contain exactly 18 owners")
    owners = tuple(row[0] for row in rows[1:])
    paths = {row[0]: row[1] for row in rows[1:]}
    if owners != tuple(sorted(owners)) or len(paths) != 18:
        raise MigrationError("W11 selector is duplicated or not sorted")
    return owners, paths


def configure_plan_engine(engine, owners: tuple[str, ...]):
    engine.FROZEN_BASE = BASE
    engine.P0002_SHA256 = PROJECTION_SHA256
    engine.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    engine.EXPECTED_SIGNATURE_EDGES = EXPECTED_SIGNATURE_EDGES
    engine.EXPECTED_BODY_EDGES = EXPECTED_BODY_EDGES
    engine.EXPECTED_PHYSICAL_DECLARATIONS = EXPECTED_DECLARATIONS
    engine.EXPECTED_PRIVATE_SEEDS = EXPECTED_PRIVATE
    engine.EXPECTED_RETAINED_COMMANDS = EXPECTED_RETAINED_COMMANDS
    engine.PHYSICAL_OWNERS = tuple(owner for owner in owners if not owner.endswith(".RandNLA"))


def configure_migration_engine(engine, owners: tuple[str, ...]):
    engine.BASE = BASE
    engine.P0002_SHA256 = PROJECTION_SHA256
    engine.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    engine.EXPECTED_COMMANDS = EXPECTED_COMMANDS
    engine.EXPECTED_RETAINED = EXPECTED_RETAINED_COMMANDS
    engine.PHYSICAL = tuple(owner for owner in owners if not owner.endswith(".RandNLA"))
    engine.PHYSICAL_SET = set(engine.PHYSICAL)


def command_text(command, sources: dict[str, str]) -> str:
    return sources[command.owner][command.start_offset:command.end_offset]


def commands_from_compatible_low_rank_ilean(plan, owner, ilean, ilean_hash, source):
    """Rebase the sole known C0006 import-header delta in a command map.

    The available cache was compiled from source that differs from C0006 only
    by replacing the three reviewed MatrixInversion leaf imports with the old
    umbrella import.  Declarations and their command text are identical, but
    every declaration coordinate is two lines earlier.  Verify that exact
    cache hash and exact header substitution, parse against the compatible
    text, then prove every rebased command slice byte-for-byte equal.
    """
    if ilean_hash != LOW_RANK_COMPAT_ILEAN_SHA256:
        raise MigrationError(
            "LowRankApprox .ilean is not exact C0006 metadata and is not the "
            "single reviewed import-header-compatible cache"
        )
    if source.count(LOW_RANK_C0006_IMPORTS) != 1:
        raise MigrationError("LowRankApprox C0006 MatrixInversion import header differs")
    compatible = source.replace(
        LOW_RANK_C0006_IMPORTS, LOW_RANK_COMPAT_IMPORT, 1
    )
    parsed = plan.commands_from_ilean(owner, ilean, compatible)
    lines, starts = plan.source_offsets(source)
    rebased = {}
    for key, command in parsed.items():
        start_line = command.start_line + 2
        end_line = command.end_line + 2
        start_offset = plan.coordinate_offset(
            lines, starts, start_line, command.start_column
        )
        end_offset = plan.coordinate_offset(
            lines, starts, end_line, command.end_column
        )
        original_text = source[start_offset:end_offset]
        compatible_text = compatible[command.start_offset:command.end_offset]
        if original_text != compatible_text:
            raise MigrationError(
                f"LowRankApprox compatible span differs after rebase: {command.root}"
            )
        adjusted = plan.Command(
            owner=owner,
            root=command.root,
            span_origin="ilean-reviewed-import-rebase",
            start_line=start_line,
            start_column=command.start_column,
            end_line=end_line,
            end_column=command.end_column,
            start_offset=start_offset,
            end_offset=end_offset,
        )
        rebased[key] = adjusted
    return rebased


def read_model(repo: Path, control: Path, ilean_root: Path, owners, source_paths, plan):
    projection = (
        control / "docs/architecture/phases/2026-08-repository-reorganization"
        / "projections/P0011.tsv.gz"
    )
    declarations, edges = plan.read_projection(projection)
    edge_counts = Counter(edge.kind for edge in edges)
    union_count = len({(edge.source, edge.target) for edge in edges})
    if edge_counts != Counter(signature=EXPECTED_SIGNATURE_EDGES, body=EXPECTED_BODY_EDGES):
        raise MigrationError(f"P0011 typed counts differ: {dict(edge_counts)}")
    if union_count != EXPECTED_UNION_EDGES:
        raise MigrationError(f"P0011 union count differs: {union_count}")

    physical = tuple(owner for owner in owners if owner != "NumStability.Algorithms.RandNLA")
    if {item.module for item in declarations.values()} != set(physical):
        raise MigrationError("P0011 declaration owners differ from the 17 physical owners")

    sources: dict[str, str] = {}
    evidence = {}
    all_commands = {}
    for owner in physical:
        payload, source, blob = plan.read_base_source(repo, BASE, source_paths[owner])
        sources[owner] = source
        relative_ilean = plan.module_path(owner, ".ilean")
        ilean_path = ilean_root / relative_ilean
        ilean, ilean_hash = plan.read_ilean(ilean_path, owner)
        if owner == "NumStability.Algorithms.RandNLA.LowRankApprox":
            try:
                owner_commands = plan.commands_from_ilean(owner, ilean, source)
            except plan.PlanError:
                owner_commands = commands_from_compatible_low_rank_ilean(
                    plan, owner, ilean, ilean_hash, source
                )
        else:
            owner_commands = plan.commands_from_ilean(owner, ilean, source)
        overlap = set(all_commands).intersection(owner_commands)
        if overlap:
            raise MigrationError(f"duplicate command keys: {sorted(overlap)[:5]}")
        all_commands.update(owner_commands)
        evidence[owner] = plan.OwnerEvidence(
            module=owner,
            source_path=source_paths[owner],
            source_blob_sha1=blob,
            source_sha256=sha256_bytes(payload),
            ilean_path=(Path(".lake/build/lib/lean") / relative_ilean).as_posix(),
            ilean_sha256=ilean_hash,
        )

    declaration_commands = plan.build_command_map(
        declarations, edges, all_commands, sources
    )
    if len(all_commands) != EXPECTED_COMMANDS:
        raise MigrationError(
            f"mapped {len(all_commands)} commands, expected {EXPECTED_COMMANDS}"
        )
    depth, chosen_target, chosen_witness = plan.compute_closure(
        declarations, edges, all_commands, declaration_commands
    )
    retained_declarations = {
        name for key in depth for name in all_commands[key].declarations
    }
    if len(retained_declarations) != EXPECTED_RETAINED_DECLARATIONS:
        raise MigrationError("command retention differs from the 225-declaration floor")
    payload = ("\n".join(sorted(retained_declarations)) + "\n").encode("utf-8")
    if sha256_bytes(payload) != PRIVATE_PAYLOAD_SHA256:
        raise MigrationError("private reverse-closure payload hash differs")
    return (
        declarations, edges, sources, evidence, all_commands,
        declaration_commands, depth, chosen_target, chosen_witness,
    )


def source_seed(command) -> bool:
    owner = command.owner.rsplit(".", 1)[-1]
    name = command.root.rsplit(".", 1)[-1]
    low = name.lower()
    line = command.start_line + 1
    if owner == "ElementwiseSampling":
        return bool(re.search(r"sqMagProb_sum_eq_one|highProbability_sqMagTraceStability", name))
    if owner == "HitCountConcentration":
        return "highProbability_sqMagTraceStability" in name
    if owner == "ElementwiseSpectral":
        return "algorithm1" in low or name == "real_log_180000_le_18"
    if owner == "RowSampling":
        return bool(re.search(
            r"rowSqNormProb_sum_eq_one|rowSqNormTraceProbability_eventProb_rowTracePositiveProb",
            name,
        ))
    if owner == "RowSamplingGram":
        return bool(re.search(
            r"rowSqNormTraceProbability_(?:expectationReal_(?:rowSampleGram_frob|rowSketchGram_frob|fl_rowSampleGram_frob)|eventProb_)",
            name,
        ))
    if owner == "RowSamplingLeverage":
        return (
            name == "leverageScoreProb_eq_rowNormSq_div_nat"
            or "leverageTraceProbability_eventProb_" in name
        )
    if owner == "RowSamplingLeverageMGF":
        return "eventProb_" in name
    if owner == "RowSamplingLeverageComputedBasis":
        return "eventProb_" in name
    if owner in {"UniformRowSamplingComposition", "UniformRowSamplingFP", "Preconditioning"}:
        return "Probability_eventProb_" in name
    if owner == "LeastSquaresSketch":
        return "leverageTraceProbability_eventProb_" in name
    if owner == "LowRankApprox":
        return "equation9" in low or "source" in low
    return False


def compute_source_commands(commands, edges, declaration_commands, retained):
    command_edges: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    reverse: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    for edge in edges:
        source = declaration_commands.get(edge.source)
        target = declaration_commands.get(edge.target)
        if source is None or target is None or source == target:
            continue
        command_edges[source].add(target)
        reverse[target].add(source)

    source = {
        key for key, command in commands.items()
        if key not in retained and source_seed(command)
    }
    queue = deque(sorted(source))
    while queue:
        target = queue.popleft()
        for user in sorted(reverse.get(target, ())):
            if user in retained or user in source:
                continue
            source.add(user)
            queue.append(user)

    movable_to_retained = [
        (user, target) for user, targets in command_edges.items()
        if user not in retained for target in targets if target in retained
    ]
    reusable_to_source = [
        (user, target) for user, targets in command_edges.items()
        if user not in retained and user not in source
        for target in targets if target in source
    ]
    if movable_to_retained:
        raise MigrationError(f"movable command reaches retained command: {movable_to_retained[0]}")
    if reusable_to_source:
        raise MigrationError(f"reusable command reaches Source command: {reusable_to_source[0]}")
    source_declarations = sum(len(commands[key].declarations) for key in source)
    if len(source) != EXPECTED_SOURCE_COMMANDS or source_declarations != EXPECTED_SOURCE_DECLARATIONS:
        by_owner = Counter(
            (commands[key].owner.rsplit(".", 1)[-1], len(commands[key].declarations))
            for key in source
        )
        owner_totals = Counter()
        for key in source:
            owner_totals[commands[key].owner.rsplit(".", 1)[-1]] += len(
                commands[key].declarations
            )
        raise MigrationError(
            f"Source partition differs: {len(source)} commands/{source_declarations} declarations; "
            f"commands={dict(Counter(owner for owner, _ in by_owner.elements()))}; "
            f"declarations={dict(owner_totals)}"
        )
    return source, command_edges


SIMPLE_REUSABLE = {
    "ElementwiseSampling": f"{R}.Sampling.Elementwise.Core",
    "HitCountConcentration": f"{R}.Concentration.HitCounts.Bounds",
    "ElementwiseTraceMGF": f"{R}.Concentration.TraceMGF.Elementwise",
    "ElementwiseSpectral": f"{R}.Concentration.SpectralTransfer.Elementwise",
    "RowSampling": f"{R}.Sampling.RowNorm.Core",
    "RowSamplingGram": f"{R}.Sampling.RowNorm.Gram",
    "RowSamplingLeverage": f"{R}.Sampling.LeverageScore.Core",
    "RowSamplingTraceMGF": f"{R}.Concentration.TraceMGF.RowNorm",
    "RowSamplingLeverageMGF": f"{R}.Concentration.TraceMGF.LeverageScore",
    "RowSamplingLeverageComputedBasis": f"{R}.Sampling.LeverageScore.ComputedBasis",
    "UniformRowSampling": f"{R}.Sampling.UniformRows.Core",
    "UniformRowSamplingComposition": f"{R}.Preconditioning.ExactTransforms.UniformRowComposition",
    "UniformRowSamplingFP": f"{R}.Sampling.UniformRows.FloatingPoint",
    "UniformRowSamplingMGF": f"{R}.Concentration.TraceMGF.UniformRows",
}


def reusable_route(command) -> str:
    owner = command.owner.rsplit(".", 1)[-1]
    name = command.root.rsplit(".", 1)[-1]
    low = name.lower()
    full = command.root.lower()
    if owner in SIMPLE_REUSABLE:
        return SIMPLE_REUSABLE[owner]
    fp = bool(re.search(r"fl|computed|budget|gamma|unitroundoff|roundoff|perturb", low))
    if owner == "Preconditioning":
        # Exact transforms, structured sketches, and their floating-point
        # certificates form one typed SCC in the historical owner.
        return f"{R}.Preconditioning.ExactTransforms.Core"
    if owner == "LeastSquaresSketch":
        if name in {
            "rowSampleLSMatrixWithBasisScale",
            "rowSampleLSVectorWithBasisScale",
            "rowSampleLSResidualWithBasisScale_eq_coord",
        }:
            return f"{R}.LeastSquaresSketching.RowSampling.Core"
        # Objectives, embeddings, solver transfer, and FP bounds are mutually
        # connected through typed edges and therefore share a canonical core.
        return f"{R}.LeastSquaresSketching.Objectives.Core"
    if owner == "LowRankApprox":
        if fp or re.search(r"doolittle|lubackward|methoda", low):
            return f"{R}.LowRankApproximation.ColumnSketches.Core"
        if re.search(r"columnsketch|rightsketch|preconditionrows", full):
            return f"{R}.LowRankApproximation.ColumnSketches.Core"
        if re.search(r"projector|moorepenrose|generalizedinverse|nonsinginv", low):
            return f"{R}.LowRankApproximation.ColumnSketches.Core"
        if re.search(r"svd|singular|rectrightgram|eigen", low):
            return f"{R}.LowRankApproximation.ColumnSketches.Core"
        if re.search(r"norm|frob|residual", low):
            return f"{R}.LowRankApproximation.RankFactorizations.Core"
        return f"{R}.LowRankApproximation.RankFactorizations.Core"
    raise MigrationError(f"unrouted reusable owner: {command.owner}")


def source_route(command) -> str:
    owner = command.owner.rsplit(".", 1)[-1]
    name = command.root.rsplit(".", 1)[-1]
    fixed = {
        "ElementwiseSampling": f"{S}.Algorithm01.ElementwiseSampling.Sampling",
        "HitCountConcentration": f"{S}.Algorithm01.ElementwiseSampling.HitCountConcentration",
        "ElementwiseTraceMGF": f"{S}.Algorithm01.ElementwiseSampling.TraceMGF",
        "ElementwiseSpectral": f"{S}.Equation02.SpectralApproximation.ElementwiseSpectral",
        "RowSamplingGram": f"{S}.Equation05.GramApproximation.Bounds",
        "RowSamplingTraceMGF": f"{S}.Equation07.SubspaceEmbedding.RowNormTraceMGF",
        "RowSamplingLeverageMGF": f"{S}.Equation07.SubspaceEmbedding.LeverageTraceMGF",
        "RowSamplingLeverageComputedBasis": f"{S}.Equation07.SubspaceEmbedding.ComputedBasis",
        "UniformRowSampling": f"{S}.Algorithm03.RandomProjectionPreconditioning.UniformRows",
        "UniformRowSamplingComposition": f"{S}.Algorithm03.RandomProjectionPreconditioning.UniformRowComposition",
        "UniformRowSamplingFP": f"{S}.Algorithm03.RandomProjectionPreconditioning.FloatingPoint",
        "Preconditioning": f"{S}.Algorithm03.RandomProjectionPreconditioning.Preconditioning",
        "LeastSquaresSketch": f"{S}.Equation08.LeastSquaresSketch.Endpoints",
        "LowRankApprox": f"{S}.Equation09.LowRankApproximation.Endpoints",
    }
    if owner == "RowSampling":
        if name == "rowSqNormProb_sum_eq_one":
            return f"{S}.Equation04.RowSamplingProbability.Normalization"
        return f"{S}.Algorithm02.RowSampling.Endpoints"
    if owner == "RowSamplingLeverage":
        if name == "leverageScoreProb_eq_rowNormSq_div_nat":
            return f"{S}.Equation06.LeverageProbability.Normalization"
        return f"{S}.Equation07.SubspaceEmbedding.Leverage"
    if owner not in fixed:
        raise MigrationError(f"unrouted Source owner: {command.owner}")
    return fixed[owner]


EXPECTED_ROUTE_DECLARATIONS = {
    f"{R}.Concentration.HitCounts.Bounds": 55,
    f"{R}.Concentration.SpectralTransfer.Elementwise": 91,
    f"{R}.Concentration.TraceMGF.Elementwise": 1,
    f"{R}.Concentration.TraceMGF.RowNorm": 1,
    f"{R}.Concentration.TraceMGF.LeverageScore": 12,
    f"{R}.Concentration.TraceMGF.UniformRows": 32,
    f"{R}.Sampling.Elementwise.Core": 82,
    f"{R}.Sampling.RowNorm.Core": 73,
    f"{R}.Sampling.RowNorm.Gram": 69,
    f"{R}.Sampling.LeverageScore.Core": 15,
    f"{R}.Sampling.LeverageScore.ComputedBasis": 36,
    f"{R}.Sampling.UniformRows.Core": 22,
    f"{R}.Sampling.UniformRows.FloatingPoint": 204,
    f"{R}.Preconditioning.ExactTransforms.UniformRowComposition": 6,
    f"{R}.Preconditioning.ExactTransforms.Core": 1082,
    f"{R}.LeastSquaresSketching.Objectives.Core": 72,
    f"{R}.LeastSquaresSketching.RowSampling.Core": 3,
    f"{R}.LowRankApproximation.ColumnSketches.Core": 301,
    f"{R}.LowRankApproximation.RankFactorizations.Core": 165,
    f"{S}.Algorithm01.ElementwiseSampling.Sampling": 2,
    f"{S}.Algorithm01.ElementwiseSampling.HitCountConcentration": 37,
    f"{S}.Algorithm01.ElementwiseSampling.TraceMGF": 10,
    f"{S}.Algorithm02.RowSampling.Endpoints": 3,
    f"{S}.Algorithm03.RandomProjectionPreconditioning.UniformRows": 1,
    f"{S}.Algorithm03.RandomProjectionPreconditioning.UniformRowComposition": 4,
    f"{S}.Algorithm03.RandomProjectionPreconditioning.FloatingPoint": 78,
    f"{S}.Algorithm03.RandomProjectionPreconditioning.Preconditioning": 31,
    f"{S}.Equation02.SpectralApproximation.ElementwiseSpectral": 200,
    f"{S}.Equation04.RowSamplingProbability.Normalization": 1,
    f"{S}.Equation05.GramApproximation.Bounds": 4,
    f"{S}.Equation06.LeverageProbability.Normalization": 1,
    f"{S}.Equation07.SubspaceEmbedding.Leverage": 2,
    f"{S}.Equation07.SubspaceEmbedding.RowNormTraceMGF": 10,
    f"{S}.Equation07.SubspaceEmbedding.LeverageTraceMGF": 20,
    f"{S}.Equation07.SubspaceEmbedding.ComputedBasis": 7,
    f"{S}.Equation08.LeastSquaresSketch.Endpoints": 57,
    f"{S}.Equation09.LowRankApproximation.Endpoints": 339,
}


def make_routes(commands, retained, source):
    intended = {}
    for key, command in commands.items():
        if key in retained:
            intended[key] = command.owner
        elif key in source:
            intended[key] = source_route(command)
        else:
            intended[key] = reusable_route(command)
    counts = Counter()
    command_counts = Counter()
    for key, destination in intended.items():
        if destination == commands[key].owner:
            continue
        command_counts[destination] += 1
        counts[destination] += len(commands[key].declarations)
    if dict(counts) != EXPECTED_ROUTE_DECLARATIONS:
        missing = {k: v for k, v in EXPECTED_ROUTE_DECLARATIONS.items() if counts.get(k) != v}
        extra = {k: v for k, v in counts.items() if EXPECTED_ROUTE_DECLARATIONS.get(k) != v}
        raise MigrationError(f"route declaration counts differ: expected/missing={missing}, actual/extra={extra}")
    return intended, counts, command_counts


DIRECT_IMPORT_RE = re.compile(
    r"(?m)^(?:public[ \t]+|private[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)


SENSITIVE_IMPORTS = {
    "NumStability.Analysis.LiebTrace",
    "NumStability.Algorithms.LU.Doolittle",
    "NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion",
    "NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion",
    "NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion",
}

LOW_RANK_MATRIX_INVERSION_IMPORTS = {
    "NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion",
    "NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion",
    "NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion",
}


def direct_imports_from_source(source: str) -> set[str]:
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


def compute_dependencies(
    commands, intended, declarations, edges, declaration_commands,
    sources, full_modules, physical_set,
):
    final_owner = {}
    for key, command in commands.items():
        for name in command.declarations:
            final_owner[name] = intended[key]
    route_commands = defaultdict(list)
    for key, command in commands.items():
        if intended[key] != command.owner:
            route_commands[intended[key]].append(command)
    route_modules = set(route_commands)
    outgoing = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge)
    dependencies = {}
    for module, owned in route_commands.items():
        historical = {command.owner for command in owned}
        if len(historical) != 1:
            raise MigrationError(f"{module}: receives commands from multiple historical owners")
        owner = next(iter(historical))
        imports = direct_imports_from_source(sources[owner])
        imports = {
            item for item in imports
            if item not in physical_set and item not in SENSITIVE_IMPORTS
            and (module.startswith("NumStability.Source.") or not item.startswith("NumStability.Source."))
        }
        if owner == "NumStability.Algorithms.RandNLA.LowRankApprox":
            imports.update(LOW_RANK_MATRIX_INVERSION_IMPORTS)
        for command in owned:
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target = edge.target
                    target_module = final_owner.get(target, full_modules.get(target))
                    if not target_module or target_module == module:
                        continue
                    if target_module in physical_set:
                        raise MigrationError(f"movable {name} still depends on retained {target}")
                    if target_module.startswith("NumStability.Source.") and not module.startswith("NumStability.Source."):
                        raise MigrationError(f"reusable-to-Source declaration edge {name} -> {target}")
                    if target_module.startswith("NumStability."):
                        imports.add(target_module)
        imports.discard(owner)
        dependencies[module] = imports
    graph = {
        module: {item for item in imports if item in route_modules}
        for module, imports in dependencies.items()
    }
    cycle = topological_cycle(graph)
    if cycle:
        raise MigrationError("route-module dependency cycle: " + " -> ".join(cycle))
    return final_owner, route_commands, dependencies


def insert_doc(payload: str, title: str, paragraph: str) -> str:
    lines = payload.splitlines(keepends=True)
    cursor = 0
    while cursor < len(lines) and lines[cursor].startswith("import "):
        cursor += 1
    doc = f"\n/-!\n# {title}\n\n{paragraph}\n-/\n"
    return "".join(lines[:cursor]) + doc + "".join(lines[cursor:])


def module_doc(module: str, imports: set[str], paragraph: str) -> str:
    return (
        "".join(f"import {item}\n" for item in sorted(imports))
        + f"\n/-!\n# {module}\n\n{paragraph}\n-/\n"
    )


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


def command_rows(
    declarations, commands, intended, evidence, depth, chosen_target, chosen_witness,
):
    private = io.StringIO(newline="")
    writer = csv.writer(private, delimiter="\t", lineterminator="\n")
    writer.writerow(["format", "1"])
    for key, value in (
        ("generated_by", "docs/architecture/deliveries/W11/GENERATE_MIGRATION.py"),
        ("base_revision", BASE),
        ("projection_id", "P0011"),
        ("projection_sha256", PROJECTION_SHA256),
        ("selector_sha256", SELECTOR_SHA256),
        ("owner_count", "17"),
        ("selected_declaration_count", str(EXPECTED_DECLARATIONS)),
        ("command_count", str(EXPECTED_COMMANDS)),
        ("private_declaration_count", str(EXPECTED_PRIVATE)),
        ("graph_reverse_closure_count", str(EXPECTED_RETAINED_DECLARATIONS)),
        ("retained_command_count", str(EXPECTED_RETAINED_COMMANDS)),
        ("move_candidate_command_count", str(EXPECTED_COMMANDS - EXPECTED_RETAINED_COMMANDS)),
        ("private_payload_sha256", PRIVATE_PAYLOAD_SHA256),
        ("coordinate_convention", "lines=1-based; columns=UTF-16-code-units-0-based; end=half-open"),
    ):
        writer.writerow(["metadata", key, value])
    writer.writerow([
        "columns", "owner", "module", "source_path", "source_blob_sha1",
        "source_sha256", "ilean_path", "ilean_sha256", "command_count",
        "retained_command_count", "move_candidate_count", "private_declaration_count",
    ])
    writer.writerow([
        "columns", "command", "owner_module", "command_root", "span_origin",
        "start_line", "start_column", "end_line", "end_column", "decision",
        "reason", "closure_depth", "witness_owner", "witness_root",
        "witness_edge_kind", "witness_source_declaration",
        "witness_target_declaration", "selected_declaration_count",
        "private_declaration_count", "selected_declarations_json",
    ])
    owners = sorted(evidence)
    for owner in owners:
        owned = [command for command in commands.values() if command.owner == owner]
        retained = sum(command.key in depth for command in owned)
        private_count = sum(
            declarations[name].visibility == "private"
            for command in owned for name in command.declarations
        )
        item = evidence[owner]
        writer.writerow([
            "owner", owner, item.source_path, item.source_blob_sha1,
            item.source_sha256, item.ilean_path, item.ilean_sha256,
            str(len(owned)), str(retained), str(len(owned) - retained), str(private_count),
        ])
    for owner in owners:
        owned = sorted(
            (command for command in commands.values() if command.owner == owner),
            key=lambda command: (command.start_line, command.start_column, command.root),
        )
        for command in owned:
            key = command.key
            if key not in depth:
                decision, reason, closure_depth = "move_candidate", "closure_free", ""
                target_owner = target_root = witness_kind = witness_source = witness_target = ""
            elif depth[key] == 0:
                decision, reason, closure_depth = "retain_historical", "private_seed", "0"
                target_owner = target_root = witness_kind = witness_source = witness_target = ""
            else:
                decision = "retain_historical"
                reason = "depends_on_retained_command"
                closure_depth = str(depth[key])
                target_owner, target_root = chosen_target[key]
                witness_kind, witness_source, witness_target = chosen_witness[(key, chosen_target[key])]
            private_count = sum(
                declarations[name].visibility == "private" for name in command.declarations
            )
            writer.writerow([
                "command", owner, command.root, command.span_origin,
                str(command.start_line + 1), str(command.start_column),
                str(command.end_line + 1), str(command.end_column), decision, reason,
                closure_depth, target_owner, target_root, witness_kind, witness_source,
                witness_target, str(len(command.declarations)), str(private_count),
                json.dumps(command.declarations, ensure_ascii=False, separators=(",", ":")),
            ])
    return private.getvalue()


def build_tests(declarations, commands, intended, route_commands, final_owner, owners):
    tests = {}
    rows = [["test_module", "kind", "imports", "covers", "representatives"]]

    def add(module: str, kind: str, imports: tuple[str, ...], covers: str, reps: tuple[str, ...]):
        imports = tuple(sorted(set(imports)))
        relative = Path(*module.split(".")).with_suffix(".lean")
        payload = "".join(f"import {item}\n" for item in imports)
        payload += f"\n/-!\n# W11 {covers} test\n-/\n\n"
        payload += "".join(f"#check @{item}\n" for item in reps)
        tests[relative] = payload
        rows.append([module, kind, ",".join(imports), covers, ",".join(reps)])

    representatives = {}
    for module, owned in route_commands.items():
        public = sorted(
            name for command in owned for name in command.declarations
            if declarations[name].visibility == "public" and not name.startswith("_private.")
        )
        if not public:
            raise MigrationError(f"canonical module lacks a public representative: {module}")
        representatives[module] = public[0]
    for index, module in enumerate(sorted(route_commands), 1):
        test_module = f"NumStabilityTest.Reorganization.W11.Canonical.C{index:03d}"
        kind = "canonical-source" if module.startswith("NumStability.Source.") else "canonical-reusable"
        add(test_module, kind, (module,), module, (representatives[module],))

    for owner in owners:
        leaf = owner.rsplit(".", 1)[-1]
        test_module = f"NumStabilityTest.Reorganization.W11.OldPath.{leaf}"
        if owner == "NumStability.Algorithms.RandNLA":
            reps = (
                "NumStability.ElementwiseSample",
                "NumStability.HasOrthonormalColumns",
                "NumStability.BlockDiagonalSourceSVDTailCertificate",
            )
        else:
            public = sorted(
                name for key, command in commands.items() if command.owner == owner
                for name in command.declarations
                if declarations[name].visibility == "public"
                and intended[key] != owner and not name.startswith("_private.")
            )
            if not public:
                raise MigrationError(f"old-path owner lacks a moved public witness: {owner}")
            reps = tuple(public[:2])
        add(test_module, "old-path", (owner,), leaf, reps)

    eq08 = f"{S}.Equation08.LeastSquaresSketch.Endpoints"
    eq09 = f"{S}.Equation09.LowRankApproximation.Endpoints"
    low_rank_algorithms = f"{R}.LowRankApproximation.ColumnSketches.Core"
    low_rank_rank_factorizations = f"{R}.LowRankApproximation.RankFactorizations.Core"
    focused = [
        ("ElementwiseSampling", (f"{R}.Sampling.Elementwise.Core", f"{S}.Algorithm01.ElementwiseSampling.Sampling"), ("NumStability.ElementwiseSample",)),
        ("ElementwiseSpectralReusable", (f"{R}.Concentration.SpectralTransfer.Elementwise",), (representatives[f"{R}.Concentration.SpectralTransfer.Elementwise"],)),
        ("ElementwiseSpectralEquation02", (f"{S}.Equation02.SpectralApproximation.ElementwiseSpectral",), (representatives[f"{S}.Equation02.SpectralApproximation.ElementwiseSpectral"],)),
        ("TraceMGFConcentration", (f"{R}.Concentration.HitCounts.Bounds", f"{R}.Concentration.TraceMGF.Elementwise", f"{R}.Concentration.TraceMGF.RowNorm", f"{R}.Concentration.TraceMGF.LeverageScore", f"{R}.Concentration.TraceMGF.UniformRows"), ("NumStability.sqMagTraceProbMass_snoc", "NumStability.uniformRowOuterGramSample_centered_cstar_selfAdjoint")),
        ("RowAndLeverageSampling", (f"{R}.Sampling.RowNorm.Core", f"{R}.Sampling.RowNorm.Gram", f"{R}.Sampling.LeverageScore.Core", f"{R}.Sampling.LeverageScore.ComputedBasis"), ("NumStability.HasOrthonormalColumns", "NumStability.ComputedRowScaleDen")),
        ("UniformRowSampling", (f"{R}.Sampling.UniformRows.Core", f"{R}.Sampling.UniformRows.FloatingPoint", f"{R}.Concentration.TraceMGF.UniformRows"), ("NumStability.ComputedUniformRowScaleDen",)),
        ("Preconditioning", (f"{R}.Preconditioning.ExactTransforms.Core",), ("NumStability.ComputedPreconditioner",)),
        ("LeastSquaresReusable", (f"{R}.LeastSquaresSketching.Objectives.Core", f"{R}.LeastSquaresSketching.RowSampling.Core"), ("NumStability.PreservesLSObjective",)),
        ("LeastSquaresChapter20Closure", (eq08,), (
            "NumStability.leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver",
            "NumStability.leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid",
        )),
        ("LowRankReusable", (low_rank_rank_factorizations, low_rank_algorithms), ("NumStability.partialColOrthonormal_exists_fullColOrthonormal",)),
        ("LowRankEquation09", (eq09,), (representatives[eq09],)),
        ("PrivateHitCountClosure", ("NumStability.Algorithms.RandNLA.HitCountConcentration", "NumStability.Algorithms.RandNLA.ElementwiseSpectral"), ("NumStability.sqMagTraceProbMass_marginal_two_ne", "NumStability.sqMagTraceProbability_eventProb_forall_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum")),
        ("PrivateRowGramClosure", ("NumStability.Algorithms.RandNLA.RowSamplingGram", "NumStability.Algorithms.RandNLA.RowSamplingLeverage", "NumStability.Algorithms.RandNLA.LeastSquaresSketch"), ("NumStability.rowSqNormTraceProbMass_marginal_two_ne", "NumStability.leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan")),
        ("PrivateUniformClosure", ("NumStability.Algorithms.RandNLA.UniformRowSampling", "NumStability.Algorithms.RandNLA.UniformRowSamplingComposition", "NumStability.Algorithms.RandNLA.Preconditioning", "NumStability.Algorithms.RandNLA.UniformRowSamplingFP"), ("NumStability.uniformRowTraceProbMass_marginal_two_ne", "NumStability.countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta")),
        ("ProtectedW02Doolittle", ("NumStability.Algorithms.LU.Doolittle", "NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic", "NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates"), ("NumStability.DoolittleLU", "NumStability.DoolittleDenseLoopCertificate.to_DoolittleLU")),
        ("ProtectedW02ProbabilitySpectral", ("NumStability.Analysis.FiniteProbability", "NumStability.Analysis.MatrixSpectral"), ("NumStability.FiniteProbability",)),
        ("ProtectedW06TraceMGF", ("NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge", "NumStability.Analysis.CStarMatrices.Expectation.Finite", "NumStability.Analysis.CStarMatrices.Trace.Basic", "NumStability.Analysis.FunctionalCalculus.OperatorLog.Monotonicity", "NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity"), ("NumStability.cstarMatrixBlockDiagonal", "NumStability.FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy")),
        ("ProtectedChapter20", ("NumStability.Source.Higham.Chapter20.Theorem03.QRSolve",), ("NumStability.StoredQRDisplayedRowBudgetControl",)),
        ("ProtectedMatrixInversionAPIs", ("NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion", "NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion", "NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion"), ("NumStability.methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget", "NumStability.methodAComputedInverse", "NumStability.ideal_forward_error")),
        ("LowRankMatrixInversionRetarget", (eq09,), ("NumStability.rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget", "NumStability.nonsingInv_entry_abs_sub_computed_inverse_le_of_perturbed_inverse_component_budget")),
        ("SharedConsumerRetargetTarget", (low_rank_rank_factorizations,), ("NumStability.partialColOrthonormal_exists_fullColOrthonormal",)),
    ]
    for name, imports, reps in focused:
        add(f"NumStabilityTest.Reorganization.W11.Focused.{name}", "focused", imports, name, reps)
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
        raise MigrationError("C0006 base is unavailable")
    if run_git(repo, "branch", "--show-current") != BRANCH:
        raise MigrationError("wrong W11 worker branch")

    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    selector = phase / "selectors/W11.tsv"
    contract = json.loads((phase / "branches/B0010.json").read_text(encoding="utf-8"))
    projection_record = json.loads((phase / "projections/P0011.json").read_text(encoding="utf-8"))
    if (
        contract.get("status") != "active" or contract.get("base_sha") != BASE
        or contract.get("operator_ids") != ["codex-local"]
        or projection_record.get("status") != "active"
    ):
        raise MigrationError("B0010/P0011 activation contract differs")
    owners, source_paths = read_selector(selector)
    plan = load_module(
        repo / "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py",
        PLAN_ENGINE_SHA256,
        "w11_private_engine",
    )
    migration = load_module(
        repo / "docs/architecture/deliveries/W02/GENERATE_MIGRATION.py",
        MIGRATION_ENGINE_SHA256,
        "w11_migration_engine",
    )
    configure_plan_engine(plan, owners)
    configure_migration_engine(migration, owners)
    (
        declarations, edges, sources, evidence, commands,
        declaration_commands, depth, chosen_target, chosen_witness,
    ) = read_model(repo, control, ilean_root, owners, source_paths, plan)
    retained = set(depth)
    source, command_edges = compute_source_commands(
        commands, edges, declaration_commands, retained
    )
    intended, route_counts, route_command_counts = make_routes(commands, retained, source)
    reusable_commands = set(commands) - retained - source
    reusable_declarations = sum(len(commands[key].declarations) for key in reusable_commands)
    if len(reusable_commands) != EXPECTED_REUSABLE_COMMANDS or reusable_declarations != EXPECTED_REUSABLE_DECLARATIONS:
        raise MigrationError("reusable partition differs")

    full_graph = control / "benchmark-results/C0006-combined.tsv"
    full_modules = migration.read_full_declarations(full_graph)
    physical = set(owner for owner in owners if owner != "NumStability.Algorithms.RandNLA")
    final_owner, route_commands, dependencies = compute_dependencies(
        commands, intended, declarations, edges, declaration_commands,
        sources, full_modules, physical,
    )
    tests, test_rows = build_tests(
        declarations, commands, intended, route_commands, final_owner, owners
    )

    # Convert zero-based .ilean coordinates to the migration engine's
    # one-based ledger coordinates.
    migrate_commands = {}
    owner_commands = defaultdict(list)
    for key, command in commands.items():
        converted = migration.Command(
            owner=command.owner,
            root=command.root,
            start_line=command.start_line + 1,
            start_column=command.start_column,
            end_line=command.end_line + 1,
            end_column=command.end_column,
            decision="retain_historical" if key in retained else "move_candidate",
            declarations=tuple(command.declarations),
        )
        migrate_commands[key] = converted
        owner_commands[command.owner].append(converted)

    allowed = []
    for item in contract["owned_paths"] + contract["destination_prefixes"]:
        allowed.append((item["match"], item["path"]))
    for item in contract["destination_prefixes"]:
        allowed.append((item["match"], item["path"]))

    generated = {}
    for module, owned in sorted(route_commands.items()):
        owner = owned[0].owner
        keep = {command.root for command in owned}
        payload = migration.render_subset(
            sources[owner], owner_commands[owner], keep, dependencies[module]
        )
        tier = "source correspondence" if module.startswith("NumStability.Source.") else "reusable randomized linear algebra"
        payload = insert_doc(
            payload,
            module,
            f"W11 canonical {tier} destination. Whole commands are copied unchanged from `{owner}`; the historical path re-exports this module.",
        )
        generated[migration.module_path(module)] = payload

    original_imports = {
        owner: direct_imports_from_source(sources[owner]) for owner in physical
    }
    for owner in sorted(physical):
        retained_roots = {
            command.root for command in commands.values()
            if command.owner == owner and command.key in retained
        }
        moved_modules = {
            intended[key] for key, command in commands.items()
            if command.owner == owner and key not in retained
        }
        imports = set(original_imports[owner]) | moved_modules
        if retained_roots:
            payload = migration.render_subset(
                sources[owner], owner_commands[owner], retained_roots, imports
            )
            payload = insert_doc(
                payload,
                owner + " compatibility facade",
                "Historical declaration-bearing W11 facade. The genuine-private reverse closure remains here with its original identity; all movable commands are re-exported from canonical modules.",
            )
        else:
            payload = module_doc(
                owner,
                imports,
                "Historical W11 import-only compatibility facade. Declarations moved unchanged to the canonical modules imported above.",
            )
        generated[Path(source_paths[owner])] = payload

    umbrella = "NumStability.Algorithms.RandNLA"
    umbrella_imports = direct_imports_from_source(
        run_git(repo, "show", f"{BASE}:{source_paths[umbrella]}")
    )
    generated[Path(source_paths[umbrella])] = module_doc(
        umbrella,
        umbrella_imports,
        "Historical W11 RandNLA discovery facade. It preserves every pre-migration child import.",
    )

    for relative, payload in tests.items():
        generated[relative] = payload

    route_lines = [[
        "declaration", "kind", "visibility", "historical_owner",
        "destination_module", "tier", "disposition", "command_root", "start_line",
    ]]
    for name in sorted(declarations):
        declaration = declarations[name]
        key = declaration_commands[name]
        destination = final_owner[name]
        if destination == declaration.module:
            tier, disposition = "compatibility", "retained_private_closure"
        elif destination.startswith("NumStability.Source."):
            tier, disposition = "source", "relocated"
        else:
            tier, disposition = "reusable", "relocated"
        route_lines.append([
            name, declaration.kind, declaration.visibility, declaration.module,
            destination, tier, disposition, commands[key].root,
            str(commands[key].start_line + 1),
        ])
    route_tsv = "\n".join("\t".join(row) for row in route_lines) + "\n"

    retention_lines = [[
        "historical_owner", "path", "selected", "private", "retained_public",
        "retained_private", "retained_total", "relocated", "reusable", "source",
        "facade_kind",
    ]]
    for owner in sorted(physical):
        selected = [name for name, item in declarations.items() if item.module == owner]
        retained_names = [name for name in selected if final_owner[name] == owner]
        reusable_names = [name for name in selected if final_owner[name] != owner and not final_owner[name].startswith("NumStability.Source.")]
        source_names = [name for name in selected if final_owner[name].startswith("NumStability.Source.")]
        private_count = sum(declarations[name].visibility == "private" for name in selected)
        retained_private = sum(declarations[name].visibility == "private" for name in retained_names)
        retention_lines.append([
            owner, source_paths[owner], str(len(selected)), str(private_count),
            str(len(retained_names) - retained_private), str(retained_private),
            str(len(retained_names)), str(len(selected) - len(retained_names)),
            str(len(reusable_names)), str(len(source_names)),
            "declaration_bearing" if retained_names else "pure_import_shim",
        ])
    retention_tsv = "\n".join("\t".join(row) for row in retention_lines) + "\n"
    private_tsv = command_rows(
        declarations, commands, intended, evidence, depth, chosen_target, chosen_witness
    )
    test_tsv = "\n".join("\t".join(row) for row in test_rows) + "\n"
    summary = {
        "canonical_modules": len(route_commands),
        "commands": len(commands),
        "declarations": len(declarations),
        "focused_tests": sum(row[1] == "focused" for row in test_rows[1:]),
        "old_path_tests": sum(row[1] == "old-path" for row in test_rows[1:]),
        "retained": EXPECTED_RETAINED_DECLARATIONS,
        "reusable": EXPECTED_REUSABLE_DECLARATIONS,
        "source": EXPECTED_SOURCE_DECLARATIONS,
        "tests": len(tests),
    }
    generated[Path("docs/architecture/deliveries/W11/DECLARATION_ROUTES.tsv")] = route_tsv
    generated[Path("docs/architecture/deliveries/W11/RETENTION.tsv")] = retention_tsv
    generated[Path("docs/architecture/deliveries/W11/PRIVATE_CLOSURE.tsv")] = private_tsv
    generated[Path("docs/architecture/deliveries/W11/TEST_MATRIX.tsv")] = test_tsv
    generated[Path("docs/architecture/deliveries/W11/ROUTE_SUMMARY.json")] = json.dumps(summary, indent=2, sort_keys=True) + "\n"

    if not args.write and not args.check:
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0
    for relative, payload in sorted(generated.items(), key=lambda item: item[0].as_posix()):
        scoped_write(repo, relative, payload, allowed, check=args.check)
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
