#!/usr/bin/env python3
"""Generate the command-preserving W06 semantic split.

The generator is intentionally phase-specific.  It consumes the exact C0005
P0007 projection, B0006's reviewed destination table, and W06's command-level
private-closure ledger.  Whole Lean commands are copied from immutable C0005
blobs; genuine private declarations and their reverse closure remain at the
historical paths.  Typed edges determine imports and are checked before any
file is written.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import re
import sys
from collections import Counter, defaultdict, deque
from pathlib import Path


BASE = "240c0d041781385a647fbec461d6863537e562cb"
PROJECTION_SHA256 = "E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39"
SELECTOR_SHA256 = "5D482CF32C656C77AF3AABA674C3FE39AA5AEBD0FED6BC0C3E569DCDB328E484"
COMBINED_SHA256 = "1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0"
ENGINE_SHA256 = "3DF117CD4C074B69068F25C196D3112191DA96F5E67B16B6E7888D6FC9A29BBA"
OVERLAP_REVIEW_SHA256 = "4A2CC83F6BFA8A31E97E1647D4BAB30421F16949E3AC38873A594807DBC7FCE5"
EXPECTED_DECLARATIONS = 3_512
EXPECTED_COMMANDS = 3_450
EXPECTED_GRAPH_RETAINED = 768
EXPECTED_FINAL_RETAINED = 775
EXPECTED_PRIVATE = 94
EXPECTED_SIGNATURE_EDGES = 15_044
EXPECTED_BODY_EDGES = 16_341
EXPECTED_UNION_EDGES = 22_079
EXPECTED_REVIEWED_LEAVES = 143
EXPECTED_SOURCE_LINES = 84_241


class MigrationError(RuntimeError):
    pass


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_engine(repo: Path, owners: tuple[str, ...]):
    path = repo / "docs/architecture/deliveries/W02/GENERATE_MIGRATION.py"
    found = sha256_file(path)
    if found != ENGINE_SHA256:
        raise MigrationError(
            f"migration engine hash differs: expected {ENGINE_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w06_migration_engine", path)
    if spec is None or spec.loader is None:
        raise MigrationError(f"cannot load migration engine at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.BASE = BASE
    module.P0002_SHA256 = PROJECTION_SHA256
    module.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    module.EXPECTED_PHYSICAL_DECLARATIONS = EXPECTED_DECLARATIONS
    module.EXPECTED_COMMANDS = EXPECTED_COMMANDS
    module.EXPECTED_RETAINED = EXPECTED_GRAPH_RETAINED
    module.PHYSICAL = owners
    module.PHYSICAL_SET = set(owners)
    return module


def read_selector(path: Path) -> tuple[tuple[str, ...], dict[str, str]]:
    if sha256_file(path) != SELECTOR_SHA256:
        raise MigrationError("W06 selector hash differs")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["module", "path"] or len(rows) != 68:
        raise MigrationError("W06 selector must contain exactly 67 rows")
    owners = tuple(row[0] for row in rows[1:])
    paths = {row[0]: row[1] for row in rows[1:]}
    if owners != tuple(sorted(owners)) or len(paths) != 67:
        raise MigrationError("W06 selector is not a unique sorted owner list")
    return owners, paths


def parse_review_routes(path: Path, owners: tuple[str, ...]) -> dict[str, tuple[tuple[str, ...], tuple[str, ...]]]:
    routes = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| `NumStability.") or "Historical (" not in line:
            continue
        cells = line.split("|")
        if len(cells) < 5:
            raise MigrationError(f"malformed B0006 routing row: {line[:100]}")
        owner_match = re.search(r"`(NumStability\.[^`]+)`", cells[1])
        if owner_match is None:
            raise MigrationError(f"routing row lacks owner: {line[:100]}")
        reusable = tuple(re.findall(r"`(NumStability\.[^`]+)`", cells[2]))
        source = tuple(re.findall(r"`(NumStability\.[^`]+)`", cells[3]))
        routes[owner_match.group(1)] = (reusable, source)
    if set(routes) != set(owners):
        raise MigrationError(
            f"B0006 routing owner set differs: missing={sorted(set(owners)-set(routes))}, "
            f"extra={sorted(set(routes)-set(owners))}"
        )
    return routes


def pick(routes, owner: str, suffix: str) -> str:
    candidates = [item for group in routes[owner] for item in group if item.endswith(suffix)]
    if len(candidates) != 1:
        raise MigrationError(f"{owner}: suffix {suffix!r} matches {candidates}")
    return candidates[0]


def root_leaf(command) -> str:
    return command.root.removeprefix("NumStability.")


EXTRA_RETAINED_ROOTS = {
    "NumStability.Higham16LyapunovSemigroupIntegrable",
    "NumStability.higham16CMatrixFiniteDimensionalComplex",
    "NumStability.higham16CMatrixFiniteDimensionalReal",
    "NumStability.higham16Problem16_2LyapunovKernel",
    "NumStability.higham16Problem16_2LyapunovIntegral",
    "NumStability.higham16_problem16_2_generalIntegral_neg_eq_lyapunovIntegral",
    "NumStability.higham16_problem16_2_lyapunovKernel_posDef",
}


def extra_retained(command) -> bool:
    """Retain seven Problem 16.2 commands pinned by section/local-instance context."""
    return (
        command.owner == "NumStability.Algorithms.Sylvester.Higham16Problem16_2"
        and command.decision == "move_candidate"
        and command.root in EXTRA_RETAINED_ROOTS
    )


def route_matrix_algorithms(command, routes) -> str | None:
    owner = command.owner
    name = root_leaf(command)
    if owner == "NumStability.Algorithms.MatrixPowers":
        computed = {
            "ComputedMatPowVec", "fl_matPowVecSeq", "computedMatPowVec_fl_matVec",
            "computedMatPowVec_fl_matVec_gamma_add_two", "computedMatPow_tendsto_zero_of_geometric",
        }
        jordan = {"JordanFormSpec", "infNorm_diagonal_le", "matPow_diagonal", "matPow_similarity"}
        exact = {"infNorm_le_mul_of_abs_le_mul_abs", "matPow_abs_weighted_bound"}
        computed_source = {
            "one_step_matpow_bound", "matPow_componentwise_bound", "matPow_normwise_bound",
            "matPow_convergence_bound", "matPow_matrix_bound", "matPow_nonneg_componentwise_bound",
            "similarity_product_bound", "similarity_normwise_bound", "matPow_convergence_weighted",
            "matPow_convergence_weighted_fl",
        }
        real_cases = {
            "higham_knight_18_1", "higham_knight_18_1_fl_tendsto",
            "higham_knight_18_2_diagonalizable", "higham_18_1_real_diagonalizable_tendsto",
            "higham_18_1_real_diagonalizable_fl_tendsto",
        }
        if name in computed or name.startswith("ComputedMatPowVec."):
            return pick(routes, owner, ".ComputedIteration.Model")
        if name in jordan or name.startswith("JordanFormSpec."):
            return pick(routes, owner, ".JordanScaling.RealDiagonal")
        if name in exact:
            return pick(routes, owner, ".ExactNormBounds.Real")
        if name in computed_source:
            return pick(routes, owner, ".Equations08To14.ComputedIteration")
        if name in real_cases:
            return pick(routes, owner, ".Theorems01And02.RealCases")
        if name.startswith("higham_eq_18_4_"):
            return pick(routes, owner, ".Equations04And05.RealDiagonal")
        raise MigrationError(f"unrouted MatrixPowers command: {name}")

    if owner == "NumStability.Algorithms.MatrixPowersComplex":
        exact = {
            "complexVecInfNorm_vecMul_le", "complexMatrixInfNorm_mul_le",
            "complexMatrixInfNorm_add_le", "complexMatrixInfNorm_diagonal_le",
            "complexVecInfNorm_ofReal", "complexMatrixInfNorm_ofReal",
            "complexMatrixInfNorm_ofReal_le_mul", "complexMatrixMul_add_left",
            "complexMatrixMul_add_right",
        }
        source_similarity = {"complex_similarity_product_bound", "complex_similarity_normwise_bound"}
        if name in exact:
            return pick(routes, owner, ".ExactNormBounds.Complex")
        if name in source_similarity:
            return pick(routes, owner, ".Equations08To14.ComplexSimilarity")
        if name.startswith("higham_18_1_"):
            return pick(routes, owner, ".Theorems01And02.ComplexJordan")
        return pick(routes, owner, ".JordanScaling.Complex")

    if owner == "NumStability.Algorithms.MatrixPowersJordan":
        if name.startswith("higham_18_1_"):
            return pick(routes, owner, ".Theorems01And02.RealJordan")
        if name == "higham_eq_18_5_alt_real_jordan":
            return pick(routes, owner, ".Equations04And05.RealJordan")
        return pick(routes, owner, ".JordanScaling.RealJordan")

    if owner == "NumStability.Algorithms.MatrixPowersLp":
        return (
            pick(routes, owner, ".Equations04And05.LpDiagonal")
            if name.startswith("higham_eq_18_4_")
            else pick(routes, owner, ".LpBounds.ComplexDiagonal")
        )
    if owner == "NumStability.Algorithms.MatrixPowersLpJordan":
        return (
            pick(routes, owner, ".Equations04And05.LpJordan")
            if name == "higham_eq_18_5_alt_lp_jordan"
            else pick(routes, owner, ".LpBounds.ComplexJordan")
        )
    if owner == "NumStability.Algorithms.MatrixPowersPseudospectral":
        if name in {"pseudospectral_gap", "higham_knight_18_2_pseudospectral"}:
            return pick(routes, owner, ".Theorems01And02.PseudospectralPackaging")
        return pick(routes, owner, ".Pseudospectra.Perturbation.Definitions")
    if owner == "NumStability.Algorithms.MatrixPowersPseudospectralCriterion":
        if name in {"matrixPowers_tendsto_zero_of_pseudospectralRadiusLt", "higham_18_2_pseudospectral_criterion"}:
            return pick(routes, owner, ".Theorems01And02.PseudospectralCriterion")
        return pick(routes, owner, ".Pseudospectra.Perturbation.ConvergenceCriterion")
    if owner == "NumStability.Algorithms.MatrixPowersSpectral":
        if name in {
            "matPow_convergence_spectral",
            "matPow_convergence_spectral_fl",
            "matPow_norm_chain",
        }:
            return pick(routes, owner, ".Theorems01And02.SpectralCriterion")
        return pick(routes, owner, ".ExactNormBounds.SpectralRadius")
    return None


SINGLE_REUSABLE_SUFFIX = {
    "NumStability.Analysis.CStarMatrixBridge": ".CStarMatrices.Basic.RealMatrixBridge",
    "NumStability.Analysis.CStarMatrixExpectation": ".CStarMatrices.Expectation.Finite",
    "NumStability.Analysis.CStarMatrixTrace": ".CStarMatrices.Trace.Basic",
    "NumStability.Analysis.DunfordResidue": ".FunctionalCalculus.Resolvent.DunfordResidue",
    "NumStability.Analysis.HenriciExtremal": ".MatrixPowers.Henrici.Extremal",
    "NumStability.Analysis.HenriciSharpConstant": ".MatrixPowers.Henrici.ImprovedConstant",
    "NumStability.Analysis.HenriciSharpConstantExact": ".MatrixPowers.Henrici.SharpConstant",
    "NumStability.Analysis.JordanNormalForm": ".Jordan.NormalForm.PrimaryDecomposition",
    "NumStability.Analysis.LiebTrace": ".MatrixInequalities.LiebTrace.Concavity",
    "NumStability.Analysis.MatrixPowersBaiDemmelGuDistance": ".MatrixPowers.BaiDemmelGu.DistanceToInstability",
    "NumStability.Analysis.MatrixPowersHenrici": ".MatrixPowers.Henrici.DepartureFromNormality",
    "NumStability.Analysis.MatrixPowersSpijkerRational": ".MatrixPowers.Spijker.Rational",
    "NumStability.Analysis.NilpotentJordanChain": ".Jordan.NormalForm.NilpotentChains",
    "NumStability.Analysis.NumericalRadius": ".NumericalRadius.Core.Basic",
    "NumStability.Analysis.OperatorLog": ".FunctionalCalculus.OperatorLog.Monotonicity",
    "NumStability.Analysis.PseudospectralLowerBound": ".Pseudospectra.Perturbation.LowerBounds",
    "NumStability.Analysis.PseudospectralResolvent": ".Pseudospectra.Resolvent.LowerBounds",
    "NumStability.Analysis.RealSchurTriangulation": ".Schur.Real.Triangularization.SplitCharpoly",
    "NumStability.Analysis.ResolventFunctionalCalculus": ".FunctionalCalculus.Resolvent.Analyticity",
    "NumStability.Analysis.SpijkerProjectionIntegral": ".MatrixPowers.Spijker.ProjectionIntegral",
}


def route_analysis(command, routes) -> str | None:
    owner = command.owner
    name = root_leaf(command)
    if owner in SINGLE_REUSABLE_SUFFIX:
        return pick(routes, owner, SINGLE_REUSABLE_SUFFIX[owner])
    if owner == "NumStability.Analysis.BergerInequality":
        return pick(routes, owner, ".NumericalRadius.Berger.Hermitian")
    if owner == "NumStability.Analysis.BergerResolvent":
        return pick(routes, owner, ".NumericalRadius.Berger.PowerTwo")
    if owner == "NumStability.Analysis.MatrixPowersBaiDemmelGu":
        return (
            pick(routes, owner, ".NamedBounds.BaiDemmelGu")
            if name.startswith("higham18_baiDemmelGu_")
            else pick(routes, owner, ".BaiDemmelGu.StabilityRadius")
        )
    if owner == "NumStability.Analysis.MatrixPowersBinomialBound":
        return pick(routes, owner, ".Henrici.BinomialPowerBound")
    if owner == "NumStability.Analysis.MatrixPowersGautschi":
        return (
            pick(routes, owner, ".NamedBounds.Gautschi")
            if name.startswith("higham18_eq18_6_")
            else pick(routes, owner, ".Gautschi.Bounds")
        )
    if owner == "NumStability.Analysis.MatrixPowersHenriciNormal":
        return pick(routes, owner, ".Henrici.NormalMatrices")
    if owner == "NumStability.Analysis.MatrixPowersKreiss":
        return (
            pick(routes, owner, ".NamedBounds.Kreiss")
            if name.startswith("higham18_kreiss_")
            else pick(routes, owner, ".Kreiss.ResolventBound")
        )
    if owner == "NumStability.Analysis.MatrixPowersKreissSpijker":
        return (
            pick(routes, owner, ".NamedBounds.SpijkerKreiss")
            if name.startswith("higham18_kreiss_")
            else pick(routes, owner, ".Spijker.KreissBridge")
        )
    if owner == "NumStability.Analysis.MatrixPowersLaszlo":
        return (
            pick(routes, owner, ".NamedBounds.Laszlo")
            if name == "higham18_laszlo_nearest_normal_frobSq"
            else pick(routes, owner, ".Laszlo.NearestNormal")
        )
    if owner == "NumStability.Analysis.MatrixPowersLp185Primary":
        return pick(routes, owner, ".Equations04And05.Equation05Primary")
    if owner == "NumStability.Analysis.MatrixPowersSchur":
        return pick(routes, owner, ".ExactNormBounds.Schur")
    if owner == "NumStability.Analysis.MatrixPowersSpijkerPlanar":
        return pick(routes, owner, ".Spijker.PlanarAlgebra")
    if owner == "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis":
        return pick(routes, owner, ".Spijker.PlanarAnalysis")
    if owner == "NumStability.Analysis.PseudospectralPowerBound":
        return (
            pick(routes, owner, ".Equations08To14.PowerBound")
            if name.startswith("higham18_eq18_8")
            else pick(routes, owner, ".Pseudospectra.PowerBounds.Contour")
        )
    # BergerGeneral and SpijkerClosure have no movable commands.  If a future
    # ledger unexpectedly presents one, fail rather than invent a route.
    if owner in {
        "NumStability.Analysis.BergerGeneral",
        "NumStability.Analysis.MatrixPowersSpijkerClosure",
    }:
        raise MigrationError(f"unexpected movable command in fully retained owner {owner}: {name}")
    return None


SYLVESTER_EXPECTED = {
    # owner leaf: (retained, reusable, source)
    "Higham16AutoCondition": (8, 5, 0),
    "Higham16Eq9Assembly": (0, 2, 16),
    "Higham16Eq9EndToEnd": (0, 5, 8),
    "Higham16HessenbergRounded": (2, 0, 8),
    "Higham16HessenbergSchur": (34, 0, 8),
    "Higham16LyapunovSigmaMin": (0, 16, 17),
    "Higham16Minimizers": (194, 155, 139),
    "Higham16NormEstimator": (0, 29, 2),
    "Higham16PerturbationSigmaMin": (0, 14, 20),
    "Higham16PivotedSmallBlocks": (0, 37, 4),
    "Higham16Problem16_2": (34, 0, 8),
    "Higham16PsiSigmaMin": (0, 2, 4),
    "Higham16QuasiQuasiRounded": (0, 58, 0),
    "Higham16QuasiQuasiSylvester": (0, 22, 12),
    "Higham16QuasiRoundedSolve": (7, 31, 0),
    "Higham16QuasiRoundedSylvester": (16, 7, 12),
    "Higham16RoundedExecutor": (0, 17, 6),
    "Higham16RoundedTriangular": (0, 26, 6),
    "Higham16Spectrum": (305, 297, 56),
    "Higham16SpectrumMinimizers": (16, 0, 0),
    "Higham16VecNorm": (48, 291, 245),
    "Higham16VecPermutationNotes": (3, 2, 1),
    "SylvesterSchurExistence": (31, 25, 3),
}


NON_SYLVESTER_EXPECTED = {
    "BergerGeneral": (10, 0, 0),
    "BergerInequality": (1, 5, 0),
    "BergerResolvent": (10, 4, 0),
    "CStarMatrixBridge": (0, 97, 0),
    "CStarMatrixExpectation": (0, 27, 0),
    "CStarMatrixTrace": (0, 31, 0),
    "DunfordResidue": (0, 5, 0),
    "HenriciExtremal": (0, 22, 0),
    "HenriciSharpConstant": (0, 13, 0),
    "HenriciSharpConstantExact": (0, 21, 0),
    "JordanNormalForm": (0, 30, 0),
    "LiebTrace": (0, 370, 0),
    "MatrixPowers": (0, 36, 17),
    "MatrixPowersBaiDemmelGu": (0, 19, 3),
    "MatrixPowersBaiDemmelGuDistance": (0, 33, 0),
    "MatrixPowersBinomialBound": (17, 3, 0),
    "MatrixPowersComplex": (0, 19, 4),
    "MatrixPowersGautschi": (0, 1, 2),
    "MatrixPowersHenrici": (0, 21, 0),
    "MatrixPowersHenriciNormal": (2, 1, 0),
    "MatrixPowersJordan": (0, 16, 3),
    "MatrixPowersKreiss": (0, 20, 2),
    "MatrixPowersKreissSpijker": (0, 20, 2),
    "MatrixPowersLaszlo": (0, 26, 1),
    "MatrixPowersLp": (0, 14, 2),
    "MatrixPowersLp185Primary": (0, 0, 2),
    "MatrixPowersLpJordan": (0, 7, 1),
    "MatrixPowersPseudospectral": (0, 5, 2),
    "MatrixPowersPseudospectralCriterion": (0, 4, 2),
    "MatrixPowersSchur": (9, 4, 0),
    "MatrixPowersSpectral": (0, 7, 3),
    "MatrixPowersSpijkerClosure": (4, 0, 0),
    "MatrixPowersSpijkerPlanar": (5, 29, 0),
    "MatrixPowersSpijkerPlanarAnalysis": (17, 12, 0),
    "MatrixPowersSpijkerRational": (0, 26, 0),
    "NilpotentJordanChain": (0, 29, 0),
    "NumericalRadius": (1, 14, 0),
    "OperatorLog": (0, 19, 0),
    "PseudospectralLowerBound": (0, 14, 0),
    "PseudospectralPowerBound": (0, 14, 2),
    "PseudospectralResolvent": (1, 5, 0),
    "RealSchurTriangulation": (0, 18, 0),
    "ResolventFunctionalCalculus": (0, 9, 0),
    "SpijkerProjectionIntegral": (0, 3, 0),
}


SPECTRUM_GENERIC_SOURCE = {
    "sylvester_realQuasiSchur_transform_solution_iff",
    "sylvester_realQuasiSchur_transform_solution_iff_twoBlockSpectral",
    "sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_no_common_complex_right_eigenvalue",
    "sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_vecCoeff_det_ne_zero",
    "sylvester_realQuasiSchur_factors_twoBlockSpectral_block_separation_of_no_common_complex_right_eigenvalue",
    "sylvester_realQuasiSchur_factors_twoBlockSpectral_block_separation_of_vecCoeff_det_ne_zero",
}

SPECTRUM_EQ29_SOURCE = (
    "NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds."
    "Equation29Extensions.Spectrum"
)


EQ9_ASSEMBLY_REUSABLE = {
    "frobNormRect_orthogonal_conjugation_eq",
    "frobNormRect_eq_of_orthogonal_similarity",
}


EQ9_END_SOURCE = {
    "frobNormRect_sylvesterResidualRect_bartels_stewart_end_to_end_le",
    "bartels_stewart_end_to_end_residual",
}


PERTURBATION_GENERIC_SOURCE = {
    "sylvester_relative_error_le_of_sepLowerBound_schur_transform_residual_budget",
    "sylvester_relative_error_le_of_sigmaMin_schur_transform_residual_budget",
    "sylvester_relative_error_le_of_pos_le_sylvesterSepInf_schur_transform_residual_budget",
}


ROUNDED_EXECUTOR_GENERIC_SOURCE = {
    "flBartelsStewartSuppliedSchurRounded_residual_bound",
    "flBartelsStewartSuppliedSchurRounded_residual_bound_computedScale",
    "flBartelsStewartSuppliedRealSchurRounded_residual_bound",
    "flBartelsStewartSuppliedRealSchurRounded_residual_bound_computedScale",
}


PROBLEM_SOURCE_ROOTS = {
    "Higham16CMatrix",
    "higham16Problem16_2Kernel",
    "higham16Problem16_2Integral",
    "Higham16ExponentialProductIntegrable",
    "higham16_problem16_2_kernel_hasDerivAt",
    "higham16_problem16_2_kernel_hasDerivAt_factored",
    "Higham16Hurwitz",
    "Higham16Hurwitz.star",
}


def source_routes(routes, owner: str) -> tuple[str, ...]:
    return routes[owner][1]


def sole_source(routes, owner: str) -> str:
    items = source_routes(routes, owner)
    if len(items) != 1:
        raise MigrationError(f"{owner}: expected one source route, found {items}")
    return items[0]


def higham_equation_numbers(name: str) -> tuple[int, ...]:
    match = re.search(r"(?:H16_)?eq16_((?:\d+_)*\d+)", name)
    if match is None:
        return ()
    return tuple(int(item) for item in match.group(1).split("_"))


def source_destination_for_seed(command, routes) -> str | None:
    """Return the reviewed source route when a movable command is a source seed."""
    owner = command.owner
    leaf = owner.rsplit(".", 1)[-1]
    name = root_leaf(command)
    base_name = name.rsplit(".", 1)[-1]
    h16 = base_name.startswith("H16_")

    if leaf == "Higham16Eq9Assembly":
        return None if base_name in EQ9_ASSEMBLY_REUSABLE else sole_source(routes, owner)
    if leaf == "Higham16Eq9EndToEnd":
        return sole_source(routes, owner) if h16 or base_name in EQ9_END_SOURCE else None
    if leaf in {"Higham16HessenbergRounded", "Higham16HessenbergSchur"}:
        return sole_source(routes, owner)
    if leaf == "Higham16Problem16_2":
        return sole_source(routes, owner) if name in PROBLEM_SOURCE_ROOTS else None
    if leaf == "Higham16LyapunovSigmaMin":
        return sole_source(routes, owner) if h16 or base_name == "lyapunov_relative_first_order_bound_of_sigmaMin" else None
    if leaf == "Higham16NormEstimator":
        return sole_source(routes, owner) if base_name in {
            "sylvester_practical_error_bound_with_norm1_estimator",
            "H16_eq16_29_sylvester_practical_error_bound_with_norm1_estimator",
        } else None
    if leaf == "Higham16PerturbationSigmaMin":
        return sole_source(routes, owner) if h16 or base_name in PERTURBATION_GENERIC_SOURCE else None
    if leaf == "Higham16PivotedSmallBlocks":
        return sole_source(routes, owner) if h16 or base_name.startswith("higham16_eq16_8_") else None
    if leaf == "Higham16PsiSigmaMin":
        return sole_source(routes, owner) if h16 or base_name == "sylvester_relative_first_order_bound_of_sigmaMin" else None
    if leaf in {"Higham16QuasiQuasiSylvester", "Higham16QuasiRoundedSylvester", "Higham16RoundedTriangular"}:
        return sole_source(routes, owner) if h16 else None
    if leaf == "Higham16RoundedExecutor":
        return sole_source(routes, owner) if h16 or base_name in ROUNDED_EXECUTOR_GENERIC_SOURCE else None
    if leaf == "Higham16Spectrum":
        if not h16 and base_name not in SPECTRUM_GENERIC_SOURCE:
            return None
        numbers = higham_equation_numbers(base_name)
        if 29 in numbers:
            return SPECTRUM_EQ29_SOURCE
        if numbers and max(numbers) <= 3:
            return pick(routes, owner, ".ComplexSolvability.SpectralCriterion")
        return pick(routes, owner, ".Equations04To08.Spectrum")
    if leaf == "Higham16VecNorm":
        generic_seed = (
            base_name.startswith("sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_")
            or base_name == "sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge"
        )
        if not h16 and not generic_seed:
            return None
        if base_name.startswith(("H16_eq16_2_", "H16_eq16_3_")):
            return pick(routes, owner, ".ComplexSolvability.Vectorized")
        if base_name.startswith("H16_eq16_4_8_") or (
            generic_seed and base_name != "sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge"
        ):
            return pick(routes, owner, ".Equations04To08.Vectorized")
        if base_name.startswith("H16_eq16_28_") or "_aposteriori_" in base_name:
            return pick(routes, owner, ".Equation29Extensions.Vectorized")
        return pick(routes, owner, ".SigmaMinCorollaries.Vectorized")
    if leaf == "Higham16VecPermutationNotes":
        return sole_source(routes, owner) if base_name.startswith("H16_notes_") else None
    if leaf == "Higham16Minimizers" and h16:
        numbers = higham_equation_numbers(name)
        if 29 in numbers:
            return pick(routes, owner, ".Equation29Extensions.Minimizers")
        if 26 in numbers:
            return pick(routes, owner, ".AttainedSeparation.Equation26")
        return pick(routes, owner, ".AttainedMinima.Equations15And21")
    if leaf == "SylvesterSchurExistence":
        return sole_source(routes, owner) if h16 else None
    if h16:
        # Every remaining Sylvester owner has exactly one reviewed source leaf.
        return sole_source(routes, owner)
    return None


def compute_sylvester_source_closure(commands, edges, command_for_declaration, routes):
    move = {
        key for key, command in commands.items()
        if command.decision == "move_candidate" and not extra_retained(command)
        and (".Sylvester." in command.owner or command.owner.endswith(".SylvesterSchurExistence"))
    }
    labels: dict[tuple[str, str], set[str]] = defaultdict(set)
    seeds = set()
    for key in sorted(move):
        destination = source_destination_for_seed(commands[key], routes)
        if destination is not None:
            seeds.add(key)
            labels[key].add(destination)

    command_edges: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    reverse: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    for edge in edges:
        source = command_for_declaration.get(edge.source)
        target = command_for_declaration.get(edge.target)
        if source is None or target is None or source == target:
            continue
        command_edges[source].add(target)
        reverse[target].add(source)

    source_set = set(seeds)
    queue = deque(sorted(seeds))
    while queue:
        target = queue.popleft()
        for consumer in sorted(reverse.get(target, ())):
            if consumer in move and consumer not in source_set:
                source_set.add(consumer)
                queue.append(consumer)

    changed = True
    while changed:
        changed = False
        for key in sorted(source_set):
            inherited = set().union(*(labels[target] for target in command_edges.get(key, ()) if target in source_set))
            if not inherited.issubset(labels[key]):
                labels[key].update(inherited)
                changed = True
    missing = sorted(key for key in source_set if not labels[key])
    if missing:
        raise MigrationError(f"source-tainted commands lack a seed destination: {missing[:10]}")
    return source_set, labels


def choose_inherited_source_destination(command, candidates: set[str], routes) -> str:
    owner = command.owner
    leaf = owner.rsplit(".", 1)[-1]
    name = root_leaf(command)
    base_name = name.rsplit(".", 1)[-1]
    if leaf == "Higham16Minimizers":
        numbers = higham_equation_numbers(base_name)
        if 29 in numbers:
            return pick(routes, owner, ".Equation29Extensions.Minimizers")
        if 26 in numbers:
            return pick(routes, owner, ".AttainedSeparation.Equation26")
        return pick(routes, owner, ".AttainedMinima.Equations15And21")
    if leaf == "Higham16VecNorm":
        if base_name.startswith(("H16_eq16_2_", "H16_eq16_3_")):
            return pick(routes, owner, ".ComplexSolvability.Vectorized")
        if base_name.startswith("H16_eq16_4_8_") or base_name.startswith(
            "sylvester_realQuasiSchur_factors_twoBlockSpectral_block_and_det_ne_zero_of_"
        ):
            return pick(routes, owner, ".Equations04To08.Vectorized")
        if base_name.startswith("H16_eq16_28_") or "_aposteriori_" in base_name:
            return pick(routes, owner, ".Equation29Extensions.Vectorized")
        return pick(routes, owner, ".SigmaMinCorollaries.Vectorized")
    if leaf == "Higham16Spectrum":
        if base_name.startswith("H16_eq16_3_"):
            return pick(routes, owner, ".ComplexSolvability.SpectralCriterion")
        if base_name.startswith("H16_eq16_29_"):
            return SPECTRUM_EQ29_SOURCE
        return pick(routes, owner, ".Equations04To08.Spectrum")
    if len(source_routes(routes, owner)) == 1:
        return sole_source(routes, owner)
    if len(candidates) == 1:
        return next(iter(candidates))
    # Dependencies occasionally cross source subsections.  Prefer the route
    # whose leaf is textually witnessed by the command, then deterministic
    # chapter order.  The per-owner partition assertions and Lean build remain
    # the authority for this non-tier-changing choice.
    tokens = re.findall(r"[A-Z]?[a-z]+|\d+", name)
    scored = sorted(
        candidates,
        key=lambda item: (-sum(token.lower() in item.lower() for token in tokens), item),
    )
    return scored[0]


def route_sylvester_reusable(command, routes) -> str:
    owner = command.owner
    leaf = owner.rsplit(".", 1)[-1]
    name = root_leaf(command)
    if leaf == "Higham16Minimizers":
        return pick(routes, owner, ".AttainedMinima.Separation") if command.start_line <= 267 else pick(routes, owner, ".AttainedMinima.BackwardError")
    if leaf == "Higham16NormEstimator":
        return pick(routes, owner, ".OneNorm.GeneralIndex") if command.start_line < 270 else pick(routes, owner, ".PracticalEstimator.OneNorm")
    if leaf == "Higham16Spectrum":
        complex_schur = (
            401 <= command.start_line <= 773
            or 1442 <= command.start_line <= 3195
        )
        return pick(routes, owner, ".ComplexSchur.SpectralSolvability") if complex_schur else pick(routes, owner, ".QuasiTriangularBartelsStewart.BlockTraversal")
    if leaf == "Higham16VecNorm":
        return (
            pick(routes, owner, ".ComplexSchur.VectorizedSolvability")
            if name.rsplit(".", 1)[-1] == "existsUnique_isSylvesterSolutionRect_of_sylvesterVecCoeff_det_ne_zero"
            else pick(routes, owner, ".SigmaMinBounds.Vectorized")
        )
    reusable = routes[owner][0]
    if len(reusable) != 1:
        raise MigrationError(f"{owner}: reusable command {name} has ambiguous routes {reusable}")
    return reusable[0]


def expanded_wrapper_start(source: str, start: int) -> int:
    """Attach a standalone command wrapper to its atomic `.ilean` command.

    Lean's `.ilean` span begins at the wrapped declaration, not at an
    immediately preceding `open ... in`, `omit ... in`, or `set_option ... in`.
    Leaving that prefix behind can capture the next declaration after a split.
    Walk outwards so nested one-line wrappers move and blank atomically.
    """
    cursor = start
    while True:
        while cursor and source[cursor - 1].isspace():
            cursor -= 1
        previous_start = source.rfind("\n", 0, cursor) + 1
        previous = source[previous_start:cursor].strip()
        wrapped = (
            re.fullmatch(r"(?:open|omit|include)\s+.+\s+in", previous)
            or re.fullmatch(r"set_option\s+.+\s+in", previous)
            or re.fullmatch(r"attribute\s+.+\s+in", previous)
        )
        if not wrapped:
            return start
        start = previous_start
        cursor = previous_start


def blank_matrixpowers_duplicate(engine, source: str) -> str:
    """Remove C0005's stale physical copy of canonical `infNorm_add_le`."""
    start_marker = "/-- Triangle inequality for the matrix"
    end_marker = "/-- Componentwise domination"
    start = source.find(start_marker)
    end = source.find(end_marker, start + 1)
    if (
        start < 0 or end < 0
        or source.count(start_marker) != 1
        or source.count(end_marker) != 1
    ):
        raise MigrationError("MatrixPowers stale infNorm_add_le span was not found uniquely")
    chars = list(source)
    engine.blank_region(chars, start, end)
    return "".join(chars)


def render_subset(engine, source: str, commands: list, keep: set[str]) -> str:
    """Render a command subset while preserving exact wrapper/scaffolding text."""
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
    for command in sorted(
        commands,
        key=lambda item: (item.start_line, item.start_column, item.end_line, item.end_column),
    ):
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
    rendered = rendered.rstrip(" \t\r\n") + "\n"
    return rendered


def module_doc(module: str, imports: set[str], note: str) -> str:
    title = module.removeprefix("NumStability.")
    return (
        "".join(f"import {item}\n" for item in sorted(imports))
        + f"\n/-!\n# {title}\n\n{note}\n-/\n"
    )


def topological_owner_order(module: str, nodes: set[str], dependencies) -> list[str]:
    state: dict[str, int] = {}
    result: list[str] = []
    stack: list[str] = []

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


def expand_private_notation(payload: str) -> str:
    """Expand the two local notations whose generated private names cannot move."""
    return payload.replace("𝔼", "(EuclideanSpace ℂ (Fin n))").replace(
        "↑ₐ", "(algebraMap 𝕜 A)"
    )


def render_route(
    engine,
    module: str,
    commands: list,
    owner_commands,
    frozen_sources,
    imports: set[str],
    owner_order: list[str],
    notation_counts: Counter,
) -> str:
    payload = module_doc(
        module,
        imports,
        "W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.",
    ) + "\n"
    by_owner = defaultdict(list)
    for command in commands:
        by_owner[command.owner].append(command)
    if set(owner_order) != set(by_owner):
        raise MigrationError(f"{module}: incomplete cross-owner render order")
    for owner in owner_order:
        keep = {command.root for command in by_owner[owner]}
        fragment = render_subset(
            engine,
            frozen_sources[owner],
            owner_commands[owner],
            keep,
        )
        notation_counts[(owner, "euclidean")] += fragment.count("𝔼")
        notation_counts[(owner, "algebra_map")] += fragment.count("↑ₐ")
        payload += expand_private_notation(fragment)
    return payload


def historical_imports(owner: str, imports: set[str]) -> set[str]:
    """Apply the exact accepted-W05 import routing authorized for W06 owners."""
    result = set(imports)
    h16 = "NumStability.Algorithms.Sylvester.Higham16"
    inverse = "NumStability.Analysis.InverseOpNorm2"
    schur_old = "NumStability.Analysis.SchurTriangulation"
    real_schur_old = "NumStability.Analysis.RealQuasiSchur"
    if owner == "NumStability.Algorithms.Sylvester.Higham16NormEstimator":
        result.discard(h16)
        result.add("NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds")
    if owner == "NumStability.Algorithms.Sylvester.Higham16VecPermutationNotes":
        result.discard(h16)
        result.add("NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization")
    if owner in {
        "NumStability.Algorithms.Sylvester.Higham16LyapunovSigmaMin",
        "NumStability.Algorithms.Sylvester.Higham16PsiSigmaMin",
    }:
        result.discard(inverse)
        result.add("NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue")
    if owner == "NumStability.Algorithms.Sylvester.Higham16PerturbationSigmaMin":
        result.discard(inverse)
        result.update({
            h16,
            "NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue",
        })
    if owner == "NumStability.Algorithms.Sylvester.Higham16Spectrum":
        result.discard(real_schur_old)
        result.add("NumStability.Analysis.LinearOperators.Schur.Real.QuasiTriangular.API")
    if owner in {
        "NumStability.Analysis.MatrixPowersSchur",
        "NumStability.Analysis.SylvesterSchurExistence",
    }:
        result.discard(schur_old)
        result.add("NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation")
    if owner == "NumStability.Analysis.MatrixPowersHenrici":
        result.discard(schur_old)
    if owner == "NumStability.Algorithms.MatrixPowers":
        result.add("NumStability.Algorithms.PolynomialEvaluation.MatrixNorms")
    return result


# The format-2 graph records declaration edges, not ambient syntax/typeclass
# context supplied by an import.  These three reviewed replacements preserve
# genuine C0005 ambient context while keeping canonical leaves independent of
# historical facades.
AMBIENT_ROUTE_IMPORTS: dict[str, set[str]] = {
    "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.DepartureFromNormality": {
        "NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation",
    },
    "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalMatrices": {
        "NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation",
    },
    "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAlgebra": {
        "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational",
    },
}


def scoped_write(
    root: Path,
    relative: Path,
    payload: str,
    owned_paths: set[str],
    writable_prefixes: tuple[str, ...],
    check: bool = False,
) -> None:
    normalized = relative.as_posix()
    allowed = normalized in owned_paths or any(
        normalized.startswith(prefix) for prefix in writable_prefixes
    )
    if not allowed:
        raise MigrationError(f"refusing out-of-scope write: {normalized}")
    destination = root / relative
    existing = destination.read_text(encoding="utf-8") if destination.is_file() else None
    if check:
        if existing != payload:
            raise MigrationError(f"generated file is missing or stale: {normalized}")
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    if existing != payload:
        destination.write_text(payload, encoding="utf-8", newline="\n")


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the exact W06 migration tree.")
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_arguments()
    root = args.project_root.resolve()
    control = args.control_root.resolve()
    delivery = root / "docs/architecture/deliveries/W06"
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    selector_path = phase / "selectors/W06.tsv"
    projection_path = phase / "projections/P0007.tsv.gz"
    review_path = phase / "branches/B0006-overlap-review.md"
    contract_path = phase / "branches/B0006.json"
    closure_path = delivery / "PRIVATE_CLOSURE.tsv"
    combined_path = control / "benchmark-results/C0005-combined.tsv"

    owners, selector_paths = read_selector(selector_path)
    owner_set = set(owners)
    engine = load_engine(root, owners)
    if engine.git(root, "rev-parse", f"{BASE}^{{commit}}") != BASE:
        raise MigrationError("frozen C0005 code base is unavailable")
    if sha256_file(projection_path) != PROJECTION_SHA256:
        raise MigrationError("P0007 projection hash differs")
    if sha256_file(combined_path) != COMBINED_SHA256:
        raise MigrationError("C0005 combined format-2 graph hash differs")
    if sha256_file(review_path) != OVERLAP_REVIEW_SHA256:
        raise MigrationError("B0006 overlap-review hash differs")

    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    expected_contract = {
        "status": "active",
        "base_checkpoint_id": "C0005",
        "base_sha": BASE,
        "branch_name": "codex/reorg-2026-08-w06-ch16-ch18-remaining",
        "lane_id": "remote-lane",
        "owner_id": "remote-human",
        "operator_ids": ["codex-remote"],
        "baseline_projection_id": "P0007",
    }
    for field, expected in expected_contract.items():
        if contract.get(field) != expected:
            raise MigrationError(
                f"B0006 {field} differs: expected {expected!r}, found {contract.get(field)!r}"
            )
    owned_paths = {item["path"] for item in contract["owned_paths"]}
    if owned_paths != set(selector_paths.values()) or len(owned_paths) != 67:
        raise MigrationError("B0006 owned paths differ from the exact W06 selector")
    destination_prefixes = tuple(
        item["path"] for item in contract["destination_prefixes"]
        if item["path"].startswith("NumStability/")
    )
    production_prefixes = tuple(
        prefix for prefix in destination_prefixes
        if not prefix.startswith("NumStabilityTest/")
    )
    if len(production_prefixes) != 49:
        raise MigrationError(
            f"expected 49 production destination prefixes, found {len(production_prefixes)}"
        )
    writable_prefixes = tuple(item["path"] for item in contract["destination_prefixes"])

    declarations, edges = engine.read_projection(projection_path)
    edge_counts = Counter(edge.kind for edge in edges)
    union_edges = len({(edge.source, edge.target) for edge in edges})
    if len(declarations) != EXPECTED_DECLARATIONS:
        raise MigrationError(f"P0007 selected {len(declarations)} declarations")
    if edge_counts != Counter(
        signature=EXPECTED_SIGNATURE_EDGES, body=EXPECTED_BODY_EDGES
    ):
        raise MigrationError(f"P0007 typed-edge counts differ: {dict(edge_counts)}")
    if union_edges != EXPECTED_UNION_EDGES:
        raise MigrationError(f"P0007 union-edge count differs: {union_edges}")
    kind_counts = Counter(item.kind for item in declarations.values())
    if kind_counts != Counter(
        theorem=3_180, definition=317, inductive=5, constructor=5, recursor=5
    ):
        raise MigrationError(f"P0007 declaration-kind counts differ: {dict(kind_counts)}")
    visibility_counts = Counter(item.visibility for item in declarations.values())
    if visibility_counts != Counter(public=3_418, private=94):
        raise MigrationError(
            f"P0007 declaration-visibility counts differ: {dict(visibility_counts)}"
        )
    source_line_count = sum(
        len(str(engine.git(root, "show", f"{BASE}:{relative}")).splitlines())
        for relative in selector_paths.values()
    )
    if source_line_count != EXPECTED_SOURCE_LINES:
        raise MigrationError(
            f"frozen W06 owners have {source_line_count} source lines"
        )

    commands, closure_paths = engine.read_closure(closure_path)
    if set(closure_paths) != owner_set or closure_paths != selector_paths:
        raise MigrationError("private-closure ledger owner paths differ from W06 selector")
    if len(commands) != EXPECTED_COMMANDS:
        raise MigrationError(f"private ledger has {len(commands)} commands")
    command_for_declaration: dict[str, tuple[str, str]] = {}
    owner_commands = defaultdict(list)
    for key, command in commands.items():
        owner_commands[command.owner].append(command)
        for name in command.declarations:
            if name in command_for_declaration:
                raise MigrationError(f"duplicate command assignment for {name}")
            command_for_declaration[name] = key
    if set(command_for_declaration) != set(declarations):
        raise MigrationError("private ledger does not cover every P0007 declaration")
    private_count = sum(item.visibility == "private" for item in declarations.values())
    if private_count != EXPECTED_PRIVATE:
        raise MigrationError(f"found {private_count} private declarations")
    graph_retained = {
        name for key, command in commands.items()
        if command.decision == "retain_historical" for name in command.declarations
    }
    if len(graph_retained) != EXPECTED_GRAPH_RETAINED:
        raise MigrationError(f"graph retention floor differs: {len(graph_retained)}")
    extra_keys = {key for key, command in commands.items() if extra_retained(command)}
    if {commands[key].root for key in extra_keys} != EXTRA_RETAINED_ROOTS:
        raise MigrationError("Problem16_2 extra context-retention roots differ")
    if any(commands[key].decision != "move_candidate" for key in extra_keys):
        raise MigrationError("extra context retention overlaps the graph floor")

    routes = parse_review_routes(review_path, owners)
    reviewed_leaves = {
        module for groups in routes.values() for group in groups for module in group
    }
    if len(reviewed_leaves) != EXPECTED_REVIEWED_LEAVES:
        raise MigrationError(
            f"reviewed declaration-leaf inventory is {len(reviewed_leaves)}"
        )

    def prefix_for_module(module: str) -> str:
        path = engine.module_path(module).as_posix()
        matches = [prefix for prefix in production_prefixes if path.startswith(prefix)]
        if len(matches) != 1:
            raise MigrationError(
                f"{module}: expected exactly one B0006 production prefix, found {matches}"
            )
        return matches[0]

    for module in sorted(reviewed_leaves):
        prefix_for_module(module)
    prefix_for_module(SPECTRUM_EQ29_SOURCE)

    source_set, source_labels = compute_sylvester_source_closure(
        commands, edges, command_for_declaration, routes
    )
    intended: dict[tuple[str, str], str] = {}
    final_owner: dict[str, str] = {}
    route_commands = defaultdict(list)
    partition = Counter()
    per_owner_partition = defaultdict(Counter)
    for key, command in commands.items():
        if command.decision == "retain_historical" or key in extra_keys:
            destination = command.owner
            tier = "retained"
        elif key in source_set:
            destination = choose_inherited_source_destination(
                command, source_labels[key], routes
            )
            tier = "source"
            intended[key] = destination
            route_commands[destination].append(command)
        else:
            destination = route_matrix_algorithms(command, routes)
            if destination is None:
                destination = route_analysis(command, routes)
            if destination is None and (
                ".Sylvester." in command.owner
                or command.owner.endswith(".SylvesterSchurExistence")
            ):
                destination = route_sylvester_reusable(command, routes)
            if destination is None:
                raise MigrationError(
                    f"unrouted movable command: {command.owner} {command.root}"
                )
            tier = "source" if destination.startswith("NumStability.Source.") else "reusable"
            intended[key] = destination
            route_commands[destination].append(command)
        prefix_for_module(destination) if destination not in owner_set else None
        declaration_count = len(command.declarations)
        partition[tier] += declaration_count
        per_owner_partition[command.owner.rsplit(".", 1)[-1]][tier] += declaration_count
        for name in command.declarations:
            final_owner[name] = destination

    if partition != Counter(retained=775, reusable=2_114, source=623):
        raise MigrationError(f"final retained closure differs: {dict(partition)}")
    if sum(partition.values()) != EXPECTED_DECLARATIONS:
        raise MigrationError(f"routing partition is incomplete: {dict(partition)}")
    for leaf, expected in {**SYLVESTER_EXPECTED, **NON_SYLVESTER_EXPECTED}.items():
        actual = per_owner_partition[leaf]
        triple = (actual["retained"], actual["reusable"], actual["source"])
        if triple != expected:
            raise MigrationError(
                f"{leaf}: reviewed Sylvester partition {triple} differs from {expected}"
            )
    if set(intended) != {
        key for key, command in commands.items()
        if command.decision == "move_candidate" and key not in extra_keys
    }:
        raise MigrationError("command routing does not exactly cover the movable set")

    full_modules = engine.read_full_declarations(combined_path)
    outgoing = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge)

    with (phase / "scope.tsv").open(encoding="utf-8", newline="") as stream:
        scope_rows = list(csv.DictReader(stream, delimiter="\t"))
    live_owner_modules = {
        row["module"] for row in scope_rows if row.get("wave_id", "").startswith("W")
    }
    frozen_direct_imports = {
        owner: engine.direct_imports(root, owner) for owner in owners
    }
    dependencies: dict[str, set[str]] = {}
    dependency_witnesses = defaultdict(list)
    for module, routed in route_commands.items():
        reusable = not module.startswith("NumStability.Source.")
        imports: set[str] = set()
        for owner in {command.owner for command in routed}:
            imports.update(
                item for item in frozen_direct_imports[owner]
                if item not in live_owner_modules and item not in owner_set
            )
        if reusable:
            imports = {
                item for item in imports if not item.startswith("NumStability.Source.")
            }
        for command in routed:
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target_module = (
                        final_owner.get(edge.target)
                        if edge.target in final_owner
                        else full_modules.get(edge.target)
                    )
                    if not target_module or target_module == module:
                        continue
                    if target_module in owner_set:
                        raise MigrationError(
                            f"canonical route depends on W06 historical facade: "
                            f"{name} -> {edge.target} ({target_module})"
                        )
                    if reusable and target_module.startswith("NumStability.Source."):
                        raise MigrationError(
                            f"reusable-to-Source edge: {name} -> {edge.target} ({target_module})"
                        )
                    if target_module.startswith("NumStability."):
                        imports.add(target_module)
                        dependency_witnesses[(module, target_module)].append(
                            (edge.kind, name, edge.target)
                        )
        imports.discard(module)
        imports.update(AMBIENT_ROUTE_IMPORTS.get(module, set()))
        dependencies[module] = imports

    route_modules = set(route_commands)
    route_graph = {
        module: {item for item in imports if item in route_modules}
        for module, imports in dependencies.items()
    }
    cycle = engine.topological_cycle(route_graph)
    if cycle:
        details = []
        for source, target in zip(cycle, cycle[1:]):
            witnesses = dependency_witnesses[(source, target)][:3]
            details.append(
                f"{source} -> {target}: "
                + "; ".join(
                    f"{kind} {left} -> {right}" for kind, left, right in witnesses
                )
            )
        raise MigrationError(
            "route-module dependency cycle: " + " -> ".join(cycle)
            + "\n" + "\n".join(details)
        )

    declaration_origin = {
        name: commands[key].owner for name, key in command_for_declaration.items()
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
        route_owner_order[module] = topological_owner_order(
            module,
            {command.owner for command in routed},
            route_owner_dependencies[module],
        )

    # Materialize declaration-bearing leaves plus honest Source locators.  A
    # reusable route whose declarations are projection-pinned is deliberately
    # omitted: an empty module would fabricate an API, while importing the
    # historical owner would violate the canonical boundary.  Likewise, a
    # Source locator is emitted only when every public declaration moved and a
    # reusable canonical leaf can honestly carry the source-facing locator.
    used_by_owner = defaultdict(set)
    reviewed_by_module = defaultdict(set)
    for owner, groups in routes.items():
        for group in groups:
            for module in group:
                reviewed_by_module[module].add(owner)
    reviewed_by_module[SPECTRUM_EQ29_SOURCE].add(
        "NumStability.Algorithms.Sylvester.Higham16Spectrum"
    )
    for key, destination in intended.items():
        used_by_owner[commands[key].owner].add(destination)
    retained_public_by_owner = Counter()
    for name, destination in final_owner.items():
        if destination == declarations[name].module and declarations[name].visibility == "public":
            retained_public_by_owner[declarations[name].module] += 1
    honest_source_locators = {
        module for module, module_owners in reviewed_by_module.items()
        if module.startswith("NumStability.Source.")
        and module not in route_modules
        and all(retained_public_by_owner[owner] == 0 for owner in module_owners)
        and any(
            not destination.startswith("NumStability.Source.")
            for owner in module_owners for destination in used_by_owner[owner]
        )
    }
    semantic_leaves = route_modules | honest_source_locators
    locator_modules = honest_source_locators
    omitted_reviewed_leaves = reviewed_leaves - semantic_leaves
    locator_imports: dict[str, set[str]] = {}
    for module in sorted(locator_modules):
        imports = set()
        if module.startswith("NumStability.Source."):
            for owner in reviewed_by_module[module]:
                imports.update(
                    destination for destination in used_by_owner[owner]
                    if not destination.startswith("NumStability.Source.")
                )
        locator_imports[module] = imports

    generated_under_prefix = defaultdict(set)
    for module in semantic_leaves:
        generated_under_prefix[prefix_for_module(module)].add(module)
    all_modules: dict[str, set[str]] = {}
    for prefix in production_prefixes:
        children = generated_under_prefix[prefix]
        all_module = prefix.rstrip("/").replace("/", ".") + ".All"
        prefix_for_module(all_module)
        all_modules[all_module] = set(children)
    if len(all_modules) != 49:
        raise MigrationError("expected one All module for each production prefix")

    generated_imports: dict[str, set[str]] = {
        module: set(imports) for module, imports in dependencies.items()
    }
    generated_imports.update(locator_imports)
    generated_imports.update(all_modules)
    for module, imports in generated_imports.items():
        if not module.startswith("NumStability.Source."):
            bad = sorted(item for item in imports if item.startswith("NumStability.Source."))
            if bad:
                raise MigrationError(f"reusable generated module {module} imports Source: {bad}")
            facades = sorted(item for item in imports if item in owner_set)
            if facades:
                raise MigrationError(f"generated module {module} imports W06 facades: {facades}")

    route_lines = [
        "format\t1",
        "declaration\thistorical_module\tdestination_module\tdecision\tkind\tvisibility\tcommand_root\tstart_line",
    ]
    retention_lines = [
        "format\t1",
        "historical_module\thistorical_path\tselected\tprivate\tretained_public\tretained_private\tretained_total\trelocated\treusable\tsource\tfacade_kind",
    ]
    representatives: dict[str, str] = {}
    for module, routed in route_commands.items():
        public = sorted(
            name for command in routed for name in command.declarations
            if declarations[name].visibility == "public" and not name.startswith("_private.")
        )
        if not public:
            raise MigrationError(f"declaration route has no public representative: {module}")
        representatives[module] = public[0]
    for name in sorted(declarations):
        declaration = declarations[name]
        key = command_for_declaration[name]
        command = commands[key]
        destination = final_owner[name]
        if destination == command.owner:
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
    for owner in owners:
        selected = [name for name, item in declarations.items() if item.module == owner]
        retained = [name for name in selected if final_owner[name] == owner]
        reusable = [
            name for name in selected
            if final_owner[name] != owner
            and not final_owner[name].startswith("NumStability.Source.")
        ]
        source = [
            name for name in selected if final_owner[name].startswith("NumStability.Source.")
        ]
        retained_private = sum(declarations[name].visibility == "private" for name in retained)
        retained_public = len(retained) - retained_private
        retention_lines.append("\t".join((
            owner,
            selector_paths[owner],
            str(len(selected)),
            str(sum(declarations[name].visibility == "private" for name in selected)),
            str(retained_public),
            str(retained_private),
            str(len(retained)),
            str(len(selected) - len(retained)),
            str(len(reusable)),
            str(len(source)),
            "declaration_bearing" if retained else "pure_import_shim",
        )))

    # Representatives propagate through locators/All modules when possible.
    generated_representatives: dict[str, str | None] = {
        module: representatives.get(module) for module in generated_imports
    }
    changed = True
    while changed:
        changed = False
        for module, imports in generated_imports.items():
            if generated_representatives[module] is not None:
                continue
            candidates = sorted(
                generated_representatives.get(item)
                for item in imports
                if generated_representatives.get(item) is not None
            )
            if candidates:
                generated_representatives[module] = candidates[0]
                changed = True

    test_payloads: dict[Path, str] = {}
    test_rows = ["kind\timport_modules\ttest_path\trepresentatives"]
    for index, module in enumerate(sorted(generated_imports), 1):
        representative = generated_representatives[module]
        relative = Path(
            f"NumStabilityTest/Reorganization/W06/Canonical/C{index:03d}.lean"
        )
        body = f"#check {representative}\n" if representative else "example : True := by trivial\n"
        test_payloads[relative] = f"import {module}\n\n{body}"
        test_rows.append("\t".join((
            "canonical",
            module,
            relative.as_posix(),
            representative or "-",
        )))

    for index, owner in enumerate(owners, 1):
        public = sorted(
            name for name, item in declarations.items()
            if item.module == owner and item.visibility == "public"
            and not name.startswith("_private.")
        )
        if not public:
            raise MigrationError(f"historical owner lacks public test representative: {owner}")
        representative = public[0]
        relative = Path(
            f"NumStabilityTest/Reorganization/W06/Compatibility/O{index:02d}.lean"
        )
        test_payloads[relative] = f"import {owner}\n\n#check {representative}\n"
        test_rows.append("\t".join((
            "compatibility", owner, relative.as_posix(), representative
        )))

    focused: dict[str, tuple[set[str], tuple[str, ...]]] = {
        "SylvesterConditioning": ({
            "NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AttainedMinima.All",
            "NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.All",
        }, ()),
        "SylvesterSolvers": ({
            "NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.All",
            "NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.All",
            "NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.All",
        }, ()),
        "RetainedHigham16Bridges": ({
            "NumStability.Algorithms.Sylvester.Higham16Minimizers",
            "NumStability.Algorithms.Sylvester.Higham16Spectrum",
            "NumStability.Algorithms.Sylvester.Higham16VecNorm",
        }, ()),
        "EstimatorAndSeparation": ({
            "NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalEstimator.All",
            "NumStability.Algorithms.NormEstimation.OneNorm.All",
            "NumStability.Algorithms.Sylvester.Higham16NormEstimator",
        }, ()),
        "JordanAndSchur": ({
            "NumStability.Analysis.LinearOperators.Jordan.NormalForm.All",
            "NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.All",
            "NumStability.Analysis.LinearOperators.Schur.Real.Triangularization.All",
        }, ()),
        "BergerHenriciKreissSpijker": ({
            "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.All",
            "NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.All",
            "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.All",
            "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.All",
        }, ()),
        "PseudospectralResolvent": ({
            "NumStability.Analysis.FunctionalCalculus.Resolvent.All",
            "NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.All",
            "NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds.All",
            "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.All",
        }, ()),
        "Chapter16Source": ({
            "NumStability.Source.Higham.Chapter16.Problem02.LyapunovIntegral.All",
            "NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.All",
            "NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation29Extensions.All",
        }, ()),
        "ProtectedW07": ({
            "NumStability.Algorithms.StationaryIteration",
            "NumStability.Algorithms.StationaryIterationDrazin",
            "NumStability.Algorithms.StationaryIterationSemiconvergent",
        }, ()),
        "ProtectedW09": ({
            "NumStability.Algorithms.TestMatrices.Higham28Companion",
        }, ()),
        "ProtectedW11": ({
            "NumStability.Algorithms.RandNLA.ElementwiseTraceMGF",
            "NumStability.Algorithms.RandNLA.RowSamplingTraceMGF",
            "NumStability.Algorithms.RandNLA.UniformRowSamplingMGF",
        }, ()),
        "ProtectedAcceptedAPIs": ({
            "NumStability.Algorithms.PolynomialEvaluation.MatrixNorms",
            "NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue",
            "NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation",
            "NumStability.Analysis.MatrixNorms.Basic",
            "NumStability.Analysis.SingularValues.InverseBounds.OperatorTwo",
        }, (
            "NumStability.infNorm_add_le",
            "NumStability.sigmaMin_mul_vecNorm2_le_matMulVec",
        )),
        "ProtectedW02APIs": ({
            "NumStability.Algorithms.LU.GaussianElimination",
            "NumStability.Algorithms.MatMul",
            "NumStability.Algorithms.MatVec",
            "NumStability.Analysis.FiniteProbability",
            "NumStability.Analysis.MatrixSpectral",
        }, (
            "NumStability.fl_matVec",
            "NumStability.abs_signedMagnitudeForPivot_le",
            "NumStability.HasNonnegLUFactors",
            "NumStability.FiniteProbability",
            "NumStability.abs_finiteHermitianEigenvalues_le_of_finiteOpNorm2Le",
        )),
        "ProtectedW02Consumers": ({
            "NumStability.Analysis.SemiconvergentExistenceGaps",
            "NumStability.Analysis.SemiconvergentLimitGeneral",
            "NumStability.Analysis.SemiconvergentRealSpectrumComplete",
        }, ()),
    }
    for name, (imports, explicit_checks) in focused.items():
        checks = list(explicit_checks)
        for module in sorted(imports):
            representative = generated_representatives.get(module)
            if representative and representative not in checks:
                checks.append(representative)
            if module in owner_set:
                historical_public = sorted(
                    declaration for declaration, item in declarations.items()
                    if item.module == module and item.visibility == "public"
                    and not declaration.startswith("_private.")
                )
                if historical_public and historical_public[0] not in checks:
                    checks.append(historical_public[0])
        relative = Path(f"NumStabilityTest/Reorganization/W06/Focused/{name}.lean")
        body = "".join(f"#check {item}\n" for item in checks)
        if not body:
            body = "example : True := by trivial\n"
        test_payloads[relative] = (
            "".join(f"import {module}\n" for module in sorted(imports))
            + "\n" + body
        )
        test_rows.append("\t".join((
            "focused",
            ",".join(sorted(imports)),
            relative.as_posix(),
            ",".join(checks) or "-",
        )))

    canonical_count = len(generated_imports)
    if canonical_count != len(semantic_leaves) + len(all_modules):
        raise MigrationError("canonical generated-module inventory is inconsistent")
    if len(test_payloads) != canonical_count + 67 + len(focused):
        raise MigrationError("W06 test inventory is inconsistent")

    retained_facades = sorted({
        owner for owner in owners
        if any(
            declaration.module == owner and final_owner[name] == owner
            for name, declaration in declarations.items()
        )
    })
    pure_import_shims = sorted(owner_set - set(retained_facades))
    reusable_declaration_leaves = sorted(
        module for module in route_modules
        if not module.startswith("NumStability.Source.")
    )
    source_declaration_leaves = sorted(
        module for module in route_modules
        if module.startswith("NumStability.Source.")
    )
    prefix_umbrella_paths = sorted(
        prefix.rstrip("/") + ".lean" for prefix in production_prefixes
    )
    test_aggregate_imports = sorted(
        relative.as_posix()[:-5].replace("/", ".")
        for relative in test_payloads
    )
    manifest_counts = {
        "reusable_declaration_leaves": len(reusable_declaration_leaves),
        "source_declaration_leaves": len(source_declaration_leaves),
        "source_locators": len(locator_modules),
        "prefix_all_modules": len(all_modules),
        "pure_import_shims": len(pure_import_shims),
        "declaration_bearing_facades": len(retained_facades),
        "test_aggregate_imports": len(test_aggregate_imports),
    }
    expected_manifest_counts = {
        "reusable_declaration_leaves": 67,
        "source_declaration_leaves": 45,
        "source_locators": 15,
        "prefix_all_modules": 49,
        "pure_import_shims": 44,
        "declaration_bearing_facades": 23,
        "test_aggregate_imports": 257,
    }
    if manifest_counts != expected_manifest_counts:
        raise MigrationError(f"integrator manifest counts differ: {manifest_counts}")
    integrator_manifest = {
        "base_sha": BASE,
        "classifications": {
            "aggregate_worker_all_modules": sorted(all_modules),
            "compatibility_pure_import_shims": pure_import_shims,
            "declaration_bearing_historical_facades": retained_facades,
            "reusable_declaration_leaves": reusable_declaration_leaves,
            "source_declaration_leaves": source_declaration_leaves,
            "source_locators": sorted(locator_modules),
        },
        "counts": manifest_counts,
        "format": 1,
        "prefix_umbrella_paths": prefix_umbrella_paths,
        "test_aggregate_imports": test_aggregate_imports,
    }

    summary = {
        "declarations": len(declarations),
        "retained": partition["retained"],
        "moved": partition["reusable"] + partition["source"],
        "moved_reusable": partition["reusable"],
        "moved_source": partition["source"],
        "route_modules": len(route_modules),
        "reviewed_locator_modules": len(locator_modules),
        "omitted_projection_pinned_reviewed_leaves": len(omitted_reviewed_leaves),
        "all_modules": len(all_modules),
        "canonical_tests": canonical_count,
        "old_path_tests": 67,
        "focused_tests": len(focused),
        "total_tests": len(test_payloads),
    }
    if not args.write and not args.check:
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0

    frozen_sources: dict[str, str] = {}
    for owner, relative in selector_paths.items():
        payload = engine.git(root, "show", f"{BASE}:{relative}", binary=True)
        if not isinstance(payload, bytes):
            raise MigrationError(f"failed to read frozen C0005 bytes for {owner}")
        source = payload.decode("utf-8")
        if owner == "NumStability.Algorithms.MatrixPowers":
            source = blank_matrixpowers_duplicate(engine, source)
        frozen_sources[owner] = source

    notation_counts = Counter()
    rendered_routes = {}
    for module in sorted(route_modules):
        rendered_routes[module] = render_route(
            engine,
            module,
            route_commands[module],
            owner_commands,
            frozen_sources,
            dependencies[module],
            route_owner_order[module],
            notation_counts,
        )
    expected_notation_counts = Counter({
        ("NumStability.Analysis.BergerInequality", "euclidean"): 7,
        ("NumStability.Analysis.BergerResolvent", "euclidean"): 10,
        ("NumStability.Analysis.NumericalRadius", "euclidean"): 20,
        ("NumStability.Analysis.PseudospectralResolvent", "algebra_map"): 9,
    })
    notation_counts = Counter({key: value for key, value in notation_counts.items() if value})
    if notation_counts != expected_notation_counts:
        raise MigrationError(
            f"private-notation expansion inventory differs: {dict(notation_counts)}"
        )
    for module, payload in sorted(rendered_routes.items()):
        scoped_write(
            root, engine.module_path(module), payload, owned_paths, writable_prefixes,
            check=args.check,
        )
    for module, imports in sorted(locator_imports.items()):
        payload = module_doc(
            module,
            imports,
            "Higham source locator for reusable W06 content. Projection-pinned historical declarations are intentionally not imported through this canonical path.",
        )
        scoped_write(
            root, engine.module_path(module), payload, owned_paths, writable_prefixes,
            check=args.check,
        )
    for module, imports in sorted(all_modules.items()):
        note = (
            "W06 reviewed discovery entry point."
            if imports
            else "W06 reviewed empty destination entry point: all candidate declarations are projection-pinned or source-only."
        )
        payload = module_doc(module, imports, note)
        scoped_write(
            root, engine.module_path(module), payload, owned_paths, writable_prefixes,
            check=args.check,
        )

    for owner in owners:
        retained_roots = {
            command.root for key, command in commands.items()
            if command.owner == owner
            and (command.decision == "retain_historical" or key in extra_keys)
        }
        moved_modules = {
            intended[key] for key, command in commands.items()
            if command.owner == owner and key in intended
        }
        imports = historical_imports(owner, frozen_direct_imports[owner])
        imports.update(moved_modules)
        if retained_roots:
            payload = module_doc(
                owner,
                imports,
                "Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.",
            ) + "\n" + render_subset(
                engine,
                frozen_sources[owner],
                owner_commands[owner],
                retained_roots,
            )
        else:
            payload = module_doc(
                owner,
                imports,
                "Historical import-only compatibility facade for the W06 semantic modules.",
            )
        scoped_write(
            root,
            Path(selector_paths[owner]),
            payload,
            owned_paths,
            writable_prefixes,
            check=args.check,
        )

    for relative, payload in sorted(test_payloads.items()):
        scoped_write(
            root, relative, payload, owned_paths, writable_prefixes,
            check=args.check,
        )
    scoped_write(
        root,
        Path("docs/architecture/deliveries/W06/DECLARATION_ROUTES.tsv"),
        "\n".join(route_lines) + "\n",
        owned_paths,
        writable_prefixes,
        check=args.check,
    )
    scoped_write(
        root,
        Path("docs/architecture/deliveries/W06/RETENTION.tsv"),
        "\n".join(retention_lines) + "\n",
        owned_paths,
        writable_prefixes,
        check=args.check,
    )
    scoped_write(
        root,
        Path("docs/architecture/deliveries/W06/TEST_MATRIX.tsv"),
        "\n".join(test_rows) + "\n",
        owned_paths,
        writable_prefixes,
        check=args.check,
    )
    scoped_write(
        root,
        Path("docs/architecture/deliveries/W06/INTEGRATOR_MANIFEST.json"),
        json.dumps(integrator_manifest, indent=2, sort_keys=True) + "\n",
        owned_paths,
        writable_prefixes,
        check=args.check,
    )
    route_status_lines = [
        "format\t1",
        "reviewed_module\tstatus\towners\timports_or_reason",
    ]
    for module in sorted(reviewed_leaves | {SPECTRUM_EQ29_SOURCE}):
        if module in route_modules:
            status = "declaration_bearing"
            detail = str(sum(len(command.declarations) for command in route_commands[module]))
        elif module in locator_modules:
            status = "source_locator"
            detail = ",".join(sorted(locator_imports[module]))
        else:
            status = "omitted_projection_pinned"
            detail = "no facade dependency or fabricated API permitted"
        route_status_lines.append("\t".join((
            module,
            status,
            ",".join(sorted(reviewed_by_module.get(module, ()))),
            detail,
        )))
    scoped_write(
        root,
        Path("docs/architecture/deliveries/W06/REVIEWED_ROUTE_STATUS.tsv"),
        "\n".join(route_status_lines) + "\n",
        owned_paths,
        writable_prefixes,
        check=args.check,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MigrationError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
