#!/usr/bin/env python3
"""Generate the exact command-preserving W04 Chapter 21 migration.

All declaration commands are copied from immutable C0006 blobs.  The P0009
typed graph determines canonical imports; the private-command ledger decides
which commands must remain at historical paths.  The generator refuses every
path outside B0008 and validates reusable/source separation before writing.
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


BASE = "a32095e6e50189f7dcc39312bb4c6a36f421fab5"
PROJECTION_SHA256 = "EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814"
SELECTOR_SHA256 = "92446B8EBF571733212239DBD471A377EA889FC2A7061F1500DE7B03DB96518F"
ENGINE_SHA256 = "3DF117CD4C074B69068F25C196D3112191DA96F5E67B16B6E7888D6FC9A29BBA"
PLANNER_ENGINE_SHA256 = "E353E4BE155CE70D33E272414C4C41CC2E6B3A0C8A8C9618A96CD868558D0BFD"
EXPECTED_DECLARATIONS = 1_238
EXPECTED_SIGNATURE_EDGES = 5_684
EXPECTED_BODY_EDGES = 10_044
EXPECTED_UNION_EDGES = 10_624
EXPECTED_PRIVATE = 40
EXPECTED_RETAINED_DECLARATIONS = 220
EXPECTED_RELOCATED_DECLARATIONS = 1_018
EXPECTED_COMMANDS = 1_073
EXPECTED_RETAINED_COMMANDS = 220
PRIVATE_CLOSURE_SHA256 = "B55744FBEA898C63D34F7D4F81F7C75C65AF69DC5EDAFA359AAF023095FC4AB7"
EXPECTED_DIRECT_EXTERNAL_SOURCE = 105
EXPECTED_EXTERNAL_SOURCE_DEPENDENCY_CLOSURE = 304
EXPECTED_SOURCE_TIER_CLOSURE = 822

R_BEN = "NumStability.Algorithms.LinearSystems.Underdetermined.BackwardError.Normwise"
R_BER = "NumStability.Algorithms.LinearSystems.Underdetermined.BackwardError.Rowwise"
R_COND = "NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise"
R_PSEUDO = "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse"
R_SOLVE = "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers"
R_SPEC = "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications"
R_PCOMP = "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise"
R_PFIX = "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.FixedRadius"
R_PROJ = "NumStability.Algorithms.LinearSystems.Underdetermined.Projectors.ComplementNorm"
R_QRF = "NumStability.Algorithms.LinearSystems.Underdetermined.QR.Foundations"
R_GBE = "NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.BackwardError"
R_GSR = "NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay"
R_MGSC = "NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.CorrectedRecurrence"
R_MGSR = "NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.RoundedReplay"
R_RANK = "NumStability.Algorithms.LinearSystems.Underdetermined.RankStability.FullRowRank"
R_SNECT = "NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ConditionTransfer"
R_SNEFE = "NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError"
R_SNEHC = "NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.HouseholderClosure"
R_SNEQR = "NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer"
R_SNETS = "NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.TriangularSolves"

S = "NumStability.Source.Higham.Chapter21"
S_CORR = f"{S}.Corrections.Problem19_12"
S_EQ = {number: f"{S}.Equation{number:02d}" for number in range(1, 12)}
S_LEMMA = f"{S}.Lemma02.Symmetrization"
S_METHOD = f"{S}.Section03.MethodComparison"
S_T1A = f"{S}.Theorem01.Attainability"
S_T1C = f"{S}.Theorem01.ComponentwisePerturbation"
S_T3 = f"{S}.Theorem03.NormwiseBackwardError"
S_T4G = f"{S}.Theorem04.GivensQMethod"
S_T4H = f"{S}.Theorem04.HouseholderQMethod"
S_T4M = f"{S}.Theorem04.ModifiedGramSchmidtQMethod"
S_T4S = f"{S}.Theorem04.SeminormalEquations"
S_T4C = f"{S}.Theorem04.SourceClosure"

REUSABLE_PREFIXES = {
    R_BEN, R_BER, R_COND, R_PSEUDO, R_SOLVE, R_SPEC, R_PCOMP, R_PFIX,
    R_PROJ, R_QRF, R_GBE, R_GSR, R_MGSC, R_MGSR, R_RANK, R_SNECT,
    R_SNEFE, R_SNEHC, R_SNEQR, R_SNETS,
}
SOURCE_PREFIXES = {
    S_CORR, *S_EQ.values(), S_LEMMA, S_METHOD, S_T1A, S_T1C, S_T3,
    S_T4G, S_T4H, S_T4M, S_T4S, S_T4C,
}
EXTERNAL_SOURCE_MODULES = (
    "NumStability.Source.Higham.Chapter19.Core",
    "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve",
    "NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError",
)


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
            f"accepted migration engine hash differs: expected {ENGINE_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w04_migration_engine", path)
    if spec is None or spec.loader is None:
        raise MigrationError(f"cannot load accepted migration engine at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.BASE = BASE
    module.P0002_SHA256 = PROJECTION_SHA256
    module.EXPECTED_DECLARATIONS = EXPECTED_DECLARATIONS
    module.EXPECTED_PHYSICAL_DECLARATIONS = EXPECTED_DECLARATIONS
    module.PHYSICAL = owners
    module.PHYSICAL_SET = set(owners)
    return module


def load_planner_engine(repo: Path):
    path = repo / "docs/architecture/deliveries/W02/PRIVATE_CLOSURE_PLAN.py"
    found = sha256_file(path)
    if found != PLANNER_ENGINE_SHA256:
        raise MigrationError(
            f"accepted command-span engine hash differs: expected {PLANNER_ENGINE_SHA256}, found {found}"
        )
    spec = importlib.util.spec_from_file_location("w04_source_index_engine", path)
    if spec is None or spec.loader is None:
        raise MigrationError(f"cannot load accepted command-span engine at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.FROZEN_BASE = BASE
    return module


def read_selector(path: Path) -> tuple[tuple[str, ...], dict[str, str]]:
    if sha256_file(path) != SELECTOR_SHA256:
        raise MigrationError("W04 selector hash differs")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["module", "path"] or len(rows) != 30:
        raise MigrationError("W04 selector must contain exactly 29 owners")
    owners = tuple(row[0] for row in rows[1:])
    paths = {row[0]: row[1] for row in rows[1:]}
    if owners != tuple(sorted(owners)) or len(paths) != 29:
        raise MigrationError("W04 selector is duplicated or unsorted")
    return owners, paths


def read_closure(engine, path: Path, owners: tuple[str, ...]):
    found = sha256_file(path)
    if found != PRIVATE_CLOSURE_SHA256:
        raise MigrationError(
            f"private-closure ledger hash differs: expected {PRIVATE_CLOSURE_SHA256}, found {found}"
        )
    metadata: dict[str, str] = {}
    commands = {}
    source_paths = {}
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if row and row[0] == "metadata":
                metadata[row[1]] = row[2]
            elif row and row[0] == "owner":
                source_paths[row[1]] = row[2]
            elif row and row[0] == "command":
                command = engine.Command(
                    owner=row[1], root=row[2], start_line=int(row[4]),
                    start_column=int(row[5]), end_line=int(row[6]),
                    end_column=int(row[7]), decision=row[8],
                    declarations=tuple(json.loads(row[18])),
                )
                if (command.owner, command.root) in commands:
                    raise MigrationError(
                        f"duplicate private-closure command row: {command.owner}:{command.root}"
                    )
                commands[(command.owner, command.root)] = command
    if set(source_paths) != set(owners):
        raise MigrationError("private-closure owner set differs from W04")
    if metadata.get("base_revision") != BASE:
        raise MigrationError("private-closure base differs")
    if metadata.get("projection_id") != "P0009":
        raise MigrationError("private-closure projection id differs")
    if metadata.get("projection_sha256") != PROJECTION_SHA256:
        raise MigrationError("private-closure projection hash differs")
    if metadata.get("selector_sha256") != SELECTOR_SHA256:
        raise MigrationError("private-closure selector hash differs")
    if int(metadata.get("selected_declaration_count", -1)) != EXPECTED_DECLARATIONS:
        raise MigrationError("private-closure selected declaration count differs")
    if int(metadata.get("private_declaration_count", -1)) != EXPECTED_PRIVATE:
        raise MigrationError("private-closure private count differs")
    if int(metadata.get("graph_reverse_closure_count", -1)) != EXPECTED_RETAINED_DECLARATIONS:
        raise MigrationError("private-closure graph floor differs")
    retained = sum(
        len(command.declarations)
        for command in commands.values()
        if command.decision == "retain_historical"
    )
    if retained != EXPECTED_RETAINED_DECLARATIONS:
        raise MigrationError(
            f"command closure retained {retained} declarations, expected {EXPECTED_RETAINED_DECLARATIONS}"
        )
    if sum(len(command.declarations) for command in commands.values()) != EXPECTED_DECLARATIONS:
        raise MigrationError("private-closure commands do not partition P0009")
    if int(metadata.get("command_count", -1)) != len(commands):
        raise MigrationError("private-closure command count metadata differs")
    if len(commands) != EXPECTED_COMMANDS:
        raise MigrationError(
            f"private-closure command count is {len(commands)}, expected {EXPECTED_COMMANDS}"
        )
    retained_commands = sum(
        command.decision == "retain_historical" for command in commands.values()
    )
    if int(metadata.get("retained_command_count", -1)) != retained_commands:
        raise MigrationError("private-closure retained-command metadata differs")
    if retained_commands != EXPECTED_RETAINED_COMMANDS:
        raise MigrationError(
            f"private-closure retained-command count is {retained_commands}, "
            f"expected {EXPECTED_RETAINED_COMMANDS}"
        )
    if int(metadata.get("retained_declaration_count", -1)) != retained:
        raise MigrationError("private-closure retained-declaration metadata differs")
    decisions = {command.decision for command in commands.values()}
    if decisions != {"retain_historical", "move_candidate"}:
        raise MigrationError(f"private-closure decision set differs: {sorted(decisions)}")
    return metadata, commands, source_paths


def owner_leaf(owner: str) -> str:
    return owner.rsplit(".", 1)[-1]


CANONICAL_LEAF = {
    "Higham21Attainability": "Attainability",
    "Higham21Eq21_11Uniform": "UniformClosure",
    "Higham21Eq21_8": "EquationClosure",
    "Higham21Eq21_9": "EquationClosure",
    "Higham21Equation21_11": "Equation",
    "Higham21Equation21_11Scalar": "Scalar",
    "Higham21Givens": "Core",
    "Higham21GivensClosure": "Closure",
    "Higham21GivensRounded": "RoundedReplay",
    "Higham21MGS": "Core",
    "Higham21MGSRounded": "RoundedReplay",
    "Higham21Perturbation": "Perturbation",
    "Higham21PerturbationRadius": "Radius",
    "Higham21ProjectorNorm": "ProjectorNorm",
    "Higham21QRFoundations": "QRFoundations",
    "Higham21RankStability": "RankStability",
    "Higham21SNEActualOutput": "ActualOutput",
    "Higham21SNEClosure": "Closure",
    "Higham21SNEConditionTransfer": "ConditionTransfer",
    "Higham21SNEEnvelopeTransfer": "EnvelopeTransfer",
    "Higham21SNEForward": "Forward",
    "Higham21SNEQRMajorant": "QRMajorant",
    "Higham21SNERemainderBounds": "RemainderBounds",
    "Higham21SNESigned": "Signed",
    "Higham21SNEUniform": "Uniform",
    "Higham21Theorem214SourceClosure": "SourceClosure",
    "UnderdeterminedSolve": "UnderdeterminedSolve",
    "UnderdeterminedSpec": "UnderdeterminedSpec",
}


def between(command, first: int, last: int) -> bool:
    return first <= command.start_line <= last


def route_prefix(command) -> str:
    """Return the reviewed B0008 semantic prefix for one movable command."""
    leaf = owner_leaf(command.owner)
    name = command.root

    if leaf == "Higham21Attainability":
        return S_T1A
    if leaf == "Higham21Eq21_11Uniform":
        return S_EQ[11]
    if leaf == "Higham21Eq21_8":
        return S_EQ[8]
    if leaf == "Higham21Eq21_9":
        return S_EQ[9]
    if leaf in {"Higham21Equation21_11", "Higham21Equation21_11Scalar"}:
        return S_EQ[11]
    if leaf == "Higham21Givens":
        source_roots = {
            "NumStability.higham21_givens_qr_backward_error_to_generic_certificate",
            "NumStability.higham21_givens_qr_gamma_tilde_nonneg",
            "NumStability.Higham21GivensQMethodRowwiseCoefficient",
            "NumStability.higham21_givens_qr_transpose_certificate",
            "NumStability.Higham21GivensQMethodRowwiseCoefficient_nonneg",
        }
        return S_T4G if (name.startswith("NumStability.higham21_theorem21_4_") or name in source_roots) else R_GBE
    if leaf == "Higham21GivensClosure":
        if name == "NumStability.higham21_givens_actual_rounded_action_error":
            return S_EQ[10]
        return R_GSR
    if leaf == "Higham21GivensRounded":
        if name == "NumStability.higham21_givens_stored_replay_action_error":
            return S_EQ[10]
        return S_T4G if name.startswith("NumStability.higham21_theorem21_4_") else R_GSR
    if leaf == "Higham21MGS":
        if name == "NumStability.higham21_mgs_economy_qr_min_norm":
            return S_METHOD
        if name == "NumStability.higham21_mgs_corrected_rowwise_backward_stable":
            return S_T4M
        return S_METHOD if between(command, 17, 79) else R_MGSC
    if leaf == "Higham21MGSRounded":
        correction = (
            name.startswith("NumStability.higham21_mgs_problem1912_")
            or re.search(r"NumStability\.higham21_mgs_(folded_deltaAT|orthonormal_columns|selected_repair)", name)
            or name.startswith("NumStability.Higham21MGSSelectedRepair")
        )
        theorem = (
            re.search(r"NumStability\.higham21_mgs_rounded_.*theorem21_4", name)
            or re.search(r"NumStability\.higham21_mgs_rounded_.*omegaR", name)
        )
        if correction:
            return S_CORR
        if theorem:
            return S_T4M
        if name in {
            "NumStability.higham21_mgs_corrected_rowwise_backward_stable_of_mgs_repair",
            "NumStability.Higham21MGSRoundedActionToSystemTransfer",
        }:
            return S_T4M
        if between(command, 19, 675):
            return R_MGSR
        if between(command, 676, 856):
            return S_CORR
        return R_MGSR
    if leaf == "Higham21Perturbation":
        return S_EQ[6]
    if leaf == "Higham21PerturbationRadius":
        if name.startswith("NumStability.higham21_eq21_7_"):
            return S_EQ[7]
        if name.startswith("NumStability.higham21_theorem21_1_"):
            return S_T1C
        if name.startswith("NumStability.higham21RectKappa2With"):
            return R_COND
        if re.search(r"NumStability\.(higham21PerturbationEntryEnvelopeOfRow|higham21_abs_entry|higham21_undetGramPerturbationComponentBudget)", name):
            return R_PCOMP
        return R_PFIX
    if leaf == "Higham21ProjectorNorm":
        reusable = {
            "NumStability.higham21_exists_nonzero_rectMatMulVec_eq_zero_of_lt",
            "NumStability.higham21_exists_unit_rectMatMulVec_eq_zero_of_lt",
            "NumStability.higham21_lsAugmentedProjectionBlock_eq_complement",
            "NumStability.higham21_complement_projector_exists_unit_fixed_vector_of_lt",
            "NumStability.higham21_one_le_complement_projector_complexMatrixOp2_of_lt",
            "NumStability.higham21_opNorm2_eq_complexMatrixOp2_realRectToCMatrix",
        }
        if name in reusable:
            return R_PROJ
        if name.startswith("NumStability.higham21_eq21_8_"):
            return S_EQ[8]
        if name.startswith("NumStability.higham21_eq21_8_"):
            return S_EQ[8]
        if name.startswith("NumStability.higham21_eq21_9_") or name.startswith("NumStability.higham21_"):
            return S_EQ[9]
        raise MigrationError(f"unrouted ProjectorNorm command: {command.start_line} {name}")
    if leaf == "Higham21QRFoundations":
        if name == "NumStability.higham21_rectGram_det_ne_zero_of_transpose_full_col_rank":
            return S_EQ[1]
        if name.startswith("NumStability.higham21_eq21_1_3_") or name.startswith("NumStability.higham21_eq21_3_"):
            return S_EQ[3]
        if name.startswith("NumStability.higham21_eq21_1_"):
            return S_EQ[1]
        if name.startswith("NumStability.higham21_eq21_4_"):
            return S_EQ[4]
        raise MigrationError(f"unrouted QRFoundations command: {command.start_line} {name}")
    if leaf == "Higham21RankStability":
        return S_T1C
    if leaf == "Higham21SNEActualOutput":
        return S_EQ[11] if name.startswith("NumStability.higham21_eq21_11_") else R_SNEFE
    if leaf == "Higham21SNEClosure":
        if name.startswith("NumStability.higham21_sne_householder_actual_output_signed_reference_bound"):
            return S_EQ[11]
        return S_T4S if (name.startswith("NumStability.higham21_dh1993_") or "_source_" in name) else R_SNEHC
    if leaf == "Higham21SNEConditionTransfer":
        return S_EQ[7]
    if leaf == "Higham21SNEEnvelopeTransfer":
        return R_SNETS if name == "NumStability.higham21_sne_split_triangular_solve_backward_error" else R_SNEQR
    if leaf == "Higham21SNEForward":
        return S_EQ[11] if name.startswith("NumStability.higham21_eq21_11_") else R_SNEFE
    if leaf == "Higham21SNEQRMajorant":
        return R_SNEQR
    if leaf == "Higham21SNERemainderBounds":
        if name.startswith("NumStability.higham21_dh1993_"):
            return S_T4S
        if name.startswith("NumStability.higham21_eq21_11_"):
            return S_EQ[11]
        return R_SNEQR if name.startswith("NumStability.higham21_sne_qr_") else R_SNEFE
    if leaf == "Higham21SNESigned":
        return S_T4S if (name.startswith("NumStability.higham21_dh1993_") or name.startswith("NumStability.higham21SNEDH")) else R_SNEQR
    if leaf == "Higham21SNEUniform":
        source_names = {
            "NumStability.higham21SNEQUniformRelativeSecondOrderCoefficient",
            "NumStability.higham21SNEHouseholderThetaUnitRoundoffCoefficient",
            "NumStability.higham21SNEQUniformUnitRoundoffSecondOrderCoefficient",
        }
        if "_source_" in name or name in source_names:
            return S_T4S
        if re.search(r"InverseDifference|PseudoinverseDifference|ConditionDifference|ConditionTransfer", name):
            return S_EQ[11]
        if name in {
            "NumStability.higham21SNEQUniformBeta",
            "NumStability.higham21SNEQUniformDirectionFrob",
        }:
            return S_EQ[11]
        if re.search(r"Actual|Reference|SecondOrder|RBound|RInvBound|SolveMultiplier|YHat|SignedRemainder|computedNormalSolution", name):
            return R_SNEFE
        return R_SNEHC
    if leaf == "Higham21Theorem214SourceClosure":
        return S_T4C
    if leaf == "UnderdeterminedSolve":
        return route_solve(command)
    if leaf == "UnderdeterminedSpec":
        return route_spec(command)
    raise MigrationError(f"unexpected movable owner {command.owner}: {name}")


def route_solve(command) -> str:
    name = command.root
    exact_qr = {
        "NumStability.higham21_matMulRectLeft_transpose_action_orthogonal",
        "NumStability.higham21_matMulVec_orthogonal_mul_transpose",
        "NumStability.higham21_finAppend_left_right",
        "NumStability.higham21_rectGram_finiteTranspose_matMulRectLeft_orthogonal",
    }
    if name.startswith("NumStability.higham21_eq21_1_"):
        return S_EQ[1]
    if name.startswith("NumStability.higham21_eq21_2_"):
        return S_EQ[2]
    if name == "NumStability.higham21_qhat_left_inverse_of_fixed_accum_error":
        return S_T4H
    if name == "NumStability.higham21_qr_transpose_system_eq":
        return R_SOLVE
    if name in exact_qr:
        return R_QRF
    if name == "NumStability.rectMinNormSolution_zero_of_rhs_zero":
        return R_SPEC
    if re.match(r"NumStability\.undetGramPerturbation(?:ComponentBudget|RowNormBudget)?(?:_|$)", name):
        return R_PCOMP
    if re.match(
        r"NumStability\.higham21_(?:rectRowNorm2_le_of_|rectOpNorm2Le_(?:const_mul_of_nonneg|of_componentwise_data_bound)|sqrt_nat_cast_mul_self$|ch7_first_product_infNorm_le_of_componentwise_le$|frobNorm_le_sqrt_card_sq_mul_infNorm$)",
        name,
    ):
        return R_PCOMP
    if name.startswith("NumStability.UndetRowwiseBackwardErrorFeasible"):
        return R_BER
    if name == "NumStability.UndetRowwiseBackwardErrorBounded" or re.match(
        r"NumStability\.higham21_rowwise_backward_error_bound_(witness|mono)$", name
    ):
        return R_BER
    if (
        name.startswith("NumStability.higham21Cond2With")
        or name == "NumStability.higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds"
        or name == "NumStability.higham21_sqrt_nat_le_nat"
    ):
        return R_COND
    if re.match(r"NumStability\.higham21_(?:thm21_3|theorem21_3)", name) or name.startswith("NumStability.higham21Thm21_3"):
        return S_T3
    if name in {
        "NumStability.higham21_rectRowNorm2_eq_columnFrob_finiteTranspose",
        "NumStability.higham21_row_bounds_of_transposed_qr_column_bounds",
        "NumStability.higham21_matMulRectLeft_transpose_action_of_left_inverse",
    }:
        return R_QRF
    if name.startswith("NumStability.higham21_eq21_10_") or name == "NumStability.Higham21QActionGrowthCoefficient":
        return S_EQ[10]
    equation10_support = {
        "NumStability.Higham21QMethodRowwiseGammaIndex",
        "NumStability.Higham21QMethodRowwiseGammaIndex.validQR",
        "NumStability.Higham21QMethodRowwiseGammaIndex.validM",
        "NumStability.Higham21QMethodRowwiseGammaIndex.valid2M",
        "NumStability.Higham21QMethodComputedGammaIndex",
        "NumStability.Higham21QMethodComputedGammaIndex.validRowwise",
        "NumStability.Higham21QMethodComputedGammaIndex.validQAction",
        "NumStability.Higham21QMethodComputedGammaIndex.rowwiseGamma_le",
        "NumStability.Higham21QMethodComputedGammaIndex.qActionGamma_le",
        "NumStability.Higham21QMethodQhatRadius",
    }
    if name in equation10_support:
        return S_EQ[10]
    if re.match(
        r"NumStability\.(?:higham21_infNormBound_abs_orthogonal_transpose_mul|higham21_qhat_left_inverse_of_|higham21_qhat_exists_left_inverse_of_|higham21_qhat_inverse_opNorm2Le_of_|higham21_qhat_exists_left_inverse_with_opNorm2Le_of_)",
        name,
    ):
        return R_RANK
    if name == "NumStability.sne_backward_error":
        return R_SNETS
    if name in {
        "NumStability.underdetermined_forward_error",
        "NumStability.sne_forward_error_matches_q_method",
    }:
        return R_SNEFE
    for first, last, destination in (
        (40, 232, R_QRF),
        (233, 319, S_EQ[5]),
        (322, 500, S_EQ[3]),
        (504, 1845, S_EQ[7]),
        (1852, 9597, S_LEMMA),
        (9602, 9779, R_BEN),
        (9782, 11297, S_T3),
        (11305, 12768, S_T4H),
        (12774, 15192, S_T4H),
        (15297, 15906, S_EQ[11]),
    ):
        if between(command, first, last):
            return destination
    raise MigrationError(f"unrouted UnderdeterminedSolve command: {command.start_line} {name}")


def route_spec(command) -> str:
    name = command.root
    if name in {
        "NumStability.rectMinNormSolution_eq_of_transpose_solution",
        "NumStability.rectMinNormSolution_eq_transpose_of_gram_normal_eq",
    }:
        return S_EQ[4]
    if name in {
        "NumStability.MinNormSolution",
        "NumStability.RectMinNormSolution",
    } or re.match(r"NumStability\.rectRowNorm2(?:_|$)", name):
        return R_SPEC
    if name == "NumStability.RectMoorePenrosePseudoinverse":
        return R_PSEUDO
    if name == "NumStability.DemmelHighamPerturbation":
        return S_T1C
    if name == "NumStability.KielbasinskiSchwetlickUndet":
        return S_LEMMA
    if name.startswith("NumStability.higham21_eq21_4_"):
        return S_EQ[4]
    if name.startswith("NumStability.higham21_eq21_5_"):
        return S_EQ[5]
    if name.startswith("NumStability.higham21_lemma21_2_"):
        return S_LEMMA
    if re.match(
        r"NumStability\.(?:RectMinNormSolution\.exists_transpose_witness|rectMinNormSolution_|rectMatMulVec_rectTransposeMulVec$|rectTransposeMulVec_solves_of_gram_normal_eq$)",
        name,
    ):
        return R_SOLVE
    if re.match(
        r"NumStability\.(?:rectGram(?:_|$)|rectTransposeMulVec$|rectMoorePenrosePseudoinverse_|rectMatMulVec_undetAplusOfGramInv$|rectOpNorm2Le_undetAplus|undetAplus|undetGramNonsingInv)",
        name,
    ):
        return R_PSEUDO
    raise MigrationError(f"unrouted UnderdeterminedSpec command: {command.start_line} {name}")


def source_fallback(command) -> str:
    """Choose the exact source closure for a Source-dependent command.

    This is used only after P0009 proves that a nominally reusable command
    has a direct or transitive dependency on an existing Source declaration.
    Such a declaration cannot enter the reusable tier without changing its
    statement, which W04 forbids.
    """
    leaf = owner_leaf(command.owner)
    if leaf == "Higham21Givens" or leaf in {
        "Higham21GivensClosure", "Higham21GivensRounded"
    }:
        return S_T4G
    if leaf == "Higham21MGS":
        if command.root == "NumStability.higham21_mgs_economy_qr_min_norm":
            return S_METHOD
        return S_METHOD if between(command, 17, 79) else S_T4M
    if leaf == "Higham21MGSRounded":
        return S_T4M
    if leaf == "Higham21PerturbationRadius":
        return S_T1C
    if leaf == "Higham21ProjectorNorm":
        if command.root.startswith("NumStability.higham21_eq21_8_"):
            return S_EQ[8]
        return S_EQ[9]
    if leaf == "Higham21QRFoundations":
        if command.root == "NumStability.higham21_rectGram_det_ne_zero_of_transpose_full_col_rank":
            return S_EQ[1]
        return S_EQ[3]
    if leaf == "Higham21RankStability":
        return S_T1C
    if leaf == "Higham21SNEConditionTransfer":
        return S_EQ[7]
    if leaf == "Higham21SNEUniform" and re.search(
        r"InverseDifference|PseudoinverseDifference|ConditionDifference|ConditionTransfer",
        command.root,
    ):
        return S_EQ[11]
    if leaf.startswith("Higham21SNE"):
        return S_T4S
    if leaf == "UnderdeterminedSpec":
        if command.root.startswith("NumStability.KielbasinskiSchwetlickUndet"):
            return S_LEMMA
        if command.root.startswith("NumStability.DemmelHighamPerturbation"):
            return S_T1C
        return S_EQ[4]
    if leaf == "UnderdeterminedSolve":
        if command.start_line < 1858:
            return S_EQ[7]
        if command.start_line <= 9597:
            return S_LEMMA
        if command.start_line <= 11297:
            return S_T3
        if command.start_line <= 15192:
            return S_T4H
        return S_EQ[11]
    raise MigrationError(
        f"no exact source fallback for Source-dependent {command.owner}:{command.root}"
    )


def canonical_module(command, prefix: str) -> str:
    leaf = owner_leaf(command.owner)
    if leaf not in CANONICAL_LEAF:
        raise MigrationError(f"missing canonical leaf for {leaf}")
    return f"{prefix}.{CANONICAL_LEAF[leaf]}"


def expanded_wrapper_start(source: str, start: int) -> int:
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


def command_offsets(engine, source: str, command) -> tuple[int, int]:
    lines = source.splitlines(keepends=True)
    starts = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    start = engine.utf16_offset(lines, starts, command.start_line, command.start_column)
    end = engine.utf16_offset(lines, starts, command.end_line, command.end_column)
    start = engine.expanded_doc_start(source, start)
    start = expanded_wrapper_start(source, start)
    return start, end


def render_subset(engine, source: str, commands: list, keep: set[str]) -> str:
    chars = list(source)
    for match in engine.IMPORT_RE.finditer(source):
        engine.blank_region(chars, match.start(), match.end())
    prior_end = -1
    for command in sorted(
        commands,
        key=lambda item: (item.start_line, item.start_column, item.end_line, item.end_column),
    ):
        start, end = command_offsets(engine, source, command)
        if start < prior_end:
            raise MigrationError(f"overlapping expanded command span at {command.root}")
        prior_end = end
        if command.root not in keep:
            engine.blank_region(chars, start, end)
    rendered = "".join(chars)
    rendered = re.sub(r"[ \t]+(?=\r?$)", "", rendered, flags=re.MULTILINE)
    return rendered.rstrip(" \t\r\n") + "\n"


def module_doc(module: str, imports: set[str], note: str) -> str:
    return (
        "".join(f"import {item}\n" for item in sorted(imports))
        + f"\n/-!\n# {module.removeprefix('NumStability.')}\n\n{note}\n-/\n"
    )


def scoped_write(
    root: Path,
    relative: Path,
    payload: str,
    owned_paths: set[str],
    writable_prefixes: tuple[str, ...],
    check: bool,
) -> None:
    normalized = relative.as_posix()
    if normalized not in owned_paths and not any(
        normalized.startswith(prefix) for prefix in writable_prefixes
    ):
        raise MigrationError(f"refusing out-of-contract write: {normalized}")
    destination = root / relative
    existing = destination.read_text(encoding="utf-8") if destination.is_file() else None
    if check:
        if existing != payload:
            raise MigrationError(f"generated file is missing or stale: {normalized}")
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    if existing != payload:
        destination.write_text(payload, encoding="utf-8", newline="\n")


def topological_cycle(graph: dict[str, set[str]]) -> list[str] | None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(node: str) -> list[str] | None:
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


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the exact W04 migration tree.")
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
    phase = control / "docs/architecture/phases/2026-08-repository-reorganization"
    delivery = root / "docs/architecture/deliveries/W04"
    contract_path = phase / "branches/B0008.json"
    selector_path = phase / "selectors/W04.tsv"
    projection_path = phase / "projections/P0009.tsv.gz"

    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if (
        contract.get("status") != "active"
        or contract.get("base_sha") != BASE
        or contract.get("base_checkpoint_id") != "C0006"
        or contract.get("baseline_projection_id") != "P0009"
        or contract.get("branch_name") != "codex/reorg-2026-08-w04-ch21-underdetermined"
        or contract.get("operator_ids") != ["codex-remote"]
    ):
        raise MigrationError("B0008 is not the exact active W04 contract")
    owners, source_paths = read_selector(selector_path)
    owner_set = set(owners)
    engine = load_engine(root, owners)
    if engine.git(root, "rev-parse", f"{BASE}^{{commit}}") != BASE:
        raise MigrationError("frozen C0006 base is unavailable")
    declarations, edges = engine.read_projection(projection_path)
    edge_counts = Counter(edge.kind for edge in edges)
    if edge_counts != Counter(signature=EXPECTED_SIGNATURE_EDGES, body=EXPECTED_BODY_EDGES):
        raise MigrationError(f"P0009 typed-edge counts differ: {dict(edge_counts)}")
    if len({(edge.source, edge.target) for edge in edges}) != EXPECTED_UNION_EDGES:
        raise MigrationError("P0009 union-edge count differs")
    if Counter(item.visibility for item in declarations.values()) != Counter(public=1198, private=40):
        raise MigrationError("P0009 visibility counts differ")

    metadata, commands, closure_paths = read_closure(
        engine, delivery / "PRIVATE_CLOSURE.tsv", owners
    )
    if closure_paths != source_paths:
        raise MigrationError("selector and closure source paths differ")
    command_for_declaration = {}
    for command in commands.values():
        for name in command.declarations:
            if name in command_for_declaration:
                raise MigrationError(f"duplicate command assignment for {name}")
            command_for_declaration[name] = command
    if set(command_for_declaration) != set(declarations):
        raise MigrationError("private-closure ledger does not cover P0009 exactly")
    for name, declaration in declarations.items():
        command = command_for_declaration[name]
        if declaration.module != command.owner:
            raise MigrationError(f"{name}: projection/command owner mismatch")
        if declaration.visibility == "private" and command.decision != "retain_historical":
            raise MigrationError(f"private declaration marked movable: {name}")

    prefix_paths = tuple(
        item["path"] for item in contract["destination_prefixes"]
        if item["path"].startswith("NumStability/")
    )
    contract_prefixes = {item.rstrip("/").replace("/", ".") for item in prefix_paths}
    if contract_prefixes != REUSABLE_PREFIXES | SOURCE_PREFIXES or len(contract_prefixes) != 42:
        raise MigrationError("B0008 production prefixes differ from the reviewed 20+22 set")
    allowed_writes = tuple(
        item["path"] for item in contract["destination_prefixes"]
    ) + tuple(source_paths.values())
    owned_paths = set(source_paths.values())

    owner_commands: dict[str, list] = defaultdict(list)
    for key, command in commands.items():
        owner_commands[command.owner].append(command)

    outgoing = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge)

    # P0009's external Source incidence is confined to these three exact
    # modules.  Build a command-root index from their C0006 sources and rebuilt
    # C0006 `.ilean` files; generated structure-family names are recognized by
    # their atomic command-root prefix.
    planner_engine = load_planner_engine(root)
    external_source_roots: dict[str, tuple[str, ...]] = {}
    for module in EXTERNAL_SOURCE_MODULES:
        relative = engine.module_path(module)
        payload_bytes = engine.git(
            root, "show", f"{BASE}:{relative.as_posix()}", binary=True
        )
        assert isinstance(payload_bytes, bytes)
        payload = payload_bytes.decode("utf-8")
        ilean_path = root / ".lake/build/lib/lean" / engine.module_path(module, ".ilean")
        ilean, _ = planner_engine.read_ilean(ilean_path, module)
        indexed = planner_engine.commands_from_ilean(module, ilean, payload)
        external_source_roots[module] = tuple(
            sorted((root_name for _, root_name in indexed), key=lambda item: (-len(item), item))
        )

    def external_source_module(name: str) -> str | None:
        matches = [
            module for module, roots in external_source_roots.items()
            if any(name == root_name or name.startswith(root_name + ".") for root_name in roots)
        ]
        if len(matches) > 1:
            raise MigrationError(f"ambiguous external Source owner for {name}: {matches}")
        return matches[0] if matches else None

    direct_external_source = {
        name for name in declarations
        if any(external_source_module(edge.target) for edge in outgoing.get(name, ()))
    }
    if len(direct_external_source) != EXPECTED_DIRECT_EXTERNAL_SOURCE:
        raise MigrationError(
            f"direct external Source incidence is {len(direct_external_source)}, "
            f"expected {EXPECTED_DIRECT_EXTERNAL_SOURCE}"
        )

    base_imports = {}
    for path in (root / "NumStability").rglob("*.lean"):
        relative = path.relative_to(root)
        module = ".".join(relative.with_suffix("").parts)
        base_imports[module] = set(
            engine.DIRECT_IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        )
    frozen_owner_imports = {
        owner: set(engine.direct_imports(root, owner)) for owner in owners
    }
    base_imports.update(frozen_owner_imports)
    for module in list(base_imports):
        if module not in owner_set and any(
            module == prefix or module.startswith(prefix + ".")
            for prefix in contract_prefixes
        ):
            del base_imports[module]
    source_reaching = {
        module for module in base_imports
        if module.startswith("NumStability.Source.")
    }
    source_changed = True
    while source_changed:
        source_changed = False
        for module, imported in base_imports.items():
            if module not in source_reaching and imported & source_reaching:
                source_reaching.add(module)
                source_changed = True

    unsafe_reaching = set(source_reaching) | owner_set
    unsafe_changed = True
    while unsafe_changed:
        unsafe_changed = False
        for module, imported in base_imports.items():
            if module not in unsafe_reaching and imported & unsafe_reaching:
                unsafe_reaching.add(module)
                unsafe_changed = True

    def import_boundary(module: str, reusable: bool, seen: set[str] | None = None) -> set[str]:
        """Expand forbidden historical/Source imports to immutable safe boundaries."""
        if module not in owner_set and (not reusable or module not in unsafe_reaching):
            return {module}
        active = set() if seen is None else set(seen)
        if module in active:
            return set()
        active.add(module)
        imported = frozen_owner_imports.get(module, base_imports.get(module, set()))
        boundary = set()
        for target in imported:
            boundary.update(import_boundary(target, reusable, active))
        return boundary

    # Begin with the reviewed semantic route, then close the Source side
    # upward over typed dependencies (including dependencies outside W04).
    intended_prefix: dict[tuple[str, str], str] = {}
    for key, command in commands.items():
        if command.decision == "move_candidate":
            prefix = route_prefix(command)
            if prefix not in contract_prefixes:
                raise MigrationError(f"route outside B0008: {prefix}")
            intended_prefix[key] = prefix

    external_source_dependency_closure = set(direct_external_source)
    reverse_selected = defaultdict(set)
    for edge in edges:
        if edge.source in declarations and edge.target in declarations:
            reverse_selected[edge.target].add(edge.source)
    closure_queue = list(external_source_dependency_closure)
    while closure_queue:
        target = closure_queue.pop()
        for source in reverse_selected.get(target, ()):
            if source not in external_source_dependency_closure:
                external_source_dependency_closure.add(source)
                closure_queue.append(source)
    if len(external_source_dependency_closure) != EXPECTED_EXTERNAL_SOURCE_DEPENDENCY_CLOSURE:
        raise MigrationError(
            f"selected external-Source dependency closure is "
            f"{len(external_source_dependency_closure)}, "
            f"expected {EXPECTED_EXTERNAL_SOURCE_DEPENDENCY_CLOSURE}"
        )

    source_dependency_closure = set(external_source_dependency_closure)
    source_dependency_closure.update(
        name for key, prefix in intended_prefix.items()
        if prefix in SOURCE_PREFIXES
        for name in commands[key].declarations
    )
    closure_queue = list(source_dependency_closure)
    while closure_queue:
        target = closure_queue.pop()
        for source in reverse_selected.get(target, ()):
            if source not in source_dependency_closure:
                source_dependency_closure.add(source)
                closure_queue.append(source)
    if len(source_dependency_closure) != EXPECTED_SOURCE_TIER_CLOSURE:
        raise MigrationError(
            f"selected Source dependency closure is {len(source_dependency_closure)}, "
            f"expected {EXPECTED_SOURCE_TIER_CLOSURE}"
        )
    changed = True
    while changed:
        changed = False
        for key, command in commands.items():
            if (
                command.decision != "move_candidate"
                or intended_prefix[key] in SOURCE_PREFIXES
            ):
                continue
            source_dependency = False
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target_command = command_for_declaration.get(edge.target)
                    if target_command is not None:
                        target_key = (target_command.owner, target_command.root)
                        if (
                            target_command.decision == "move_candidate"
                            and intended_prefix[target_key] in SOURCE_PREFIXES
                        ):
                            source_dependency = True
                    else:
                        target_module = external_source_module(edge.target)
                        if target_module:
                            source_dependency = True
                    if source_dependency:
                        break
                if source_dependency:
                    break
            if source_dependency:
                intended_prefix[key] = source_fallback(command)
                changed = True

    route_commands: dict[str, list] = defaultdict(list)
    intended: dict[tuple[str, str], str] = {}
    prefix_for_command: dict[tuple[str, str], str] = {}
    for key, command in commands.items():
        if command.decision == "move_candidate":
            prefix = intended_prefix[key]
            module = canonical_module(command, prefix)
            intended[key] = module
            prefix_for_command[key] = prefix
            route_commands[module].append(command)

    retained_declarations = {
        name for command in commands.values()
        if command.decision == "retain_historical"
        for name in command.declarations
    }
    if len(retained_declarations) != EXPECTED_RETAINED_DECLARATIONS:
        raise MigrationError("retained declaration total differs")
    if len(declarations) - len(retained_declarations) != EXPECTED_RELOCATED_DECLARATIONS:
        raise MigrationError("relocated declaration total differs")
    for module, items in route_commands.items():
        if len({item.owner for item in items}) != 1:
            raise MigrationError(f"{module}: canonical leaf combines historical owners")

    final_owner = {}
    for key, command in commands.items():
        destination = command.owner if command.decision == "retain_historical" else intended[key]
        for name in command.declarations:
            final_owner[name] = destination

    dependencies: dict[str, set[str]] = {}
    dependency_witnesses = defaultdict(list)
    for module, items in route_commands.items():
        historical_owner = items[0].owner
        reusable = module.startswith("NumStability.Algorithms.")
        imports = set()
        for item in frozen_owner_imports[historical_owner]:
            imports.update(import_boundary(item, reusable))
        for command in items:
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target_module = final_owner.get(
                        edge.target, external_source_module(edge.target)
                    )
                    if not target_module or target_module == module:
                        continue
                    if target_module in owner_set:
                        raise MigrationError(
                            f"movable {name} depends on retained historical declaration {edge.target}"
                        )
                    if (
                        module.startswith("NumStability.Algorithms.")
                        and target_module in source_reaching
                    ):
                        raise MigrationError(f"reusable-to-Source edge {name} -> {edge.target}")
                    if target_module.startswith("NumStability."):
                        imports.add(target_module)
                        dependency_witnesses[(module, target_module)].append(
                            (edge.kind, name, edge.target)
                        )
        imports.discard(historical_owner)
        imports.discard(module)
        dependencies[module] = imports

    # The protected shared consumer needs a single exact source endpoint.
    eq4_locator = f"{S_EQ[4]}.Pseudoinverse"
    eq4_leaves = {
        module for module in route_commands if module.startswith(S_EQ[4] + ".")
    }
    pseudo_leaves = {
        module for module in route_commands if module.startswith(R_PSEUDO + ".")
    }
    if not eq4_leaves or not pseudo_leaves:
        raise MigrationError("Equation04 pseudoinverse endpoint lacks source or reusable leaves")
    dependencies[eq4_locator] = eq4_leaves | pseudo_leaves
    canonical_modules = set(dependencies)

    used_prefixes = {
        prefix for prefix in contract_prefixes
        if any(module.startswith(prefix + ".") for module in canonical_modules)
    }
    graph = {
        module: {target for target in imports if target in canonical_modules}
        for module, imports in dependencies.items()
    }
    cycle = topological_cycle(graph)
    if cycle:
        details = []
        for source, target in zip(cycle, cycle[1:]):
            witnesses = dependency_witnesses[(source, target)][:5]
            details.append(
                f"{source} -> {target}: "
                + "; ".join(
                    f"{kind} {left} -> {right}"
                    for kind, left, right in witnesses
                )
            )
        cycle_modules = set(cycle)
        cycle_keys = {
            (command.owner, command.root)
            for module in cycle_modules
            for command in route_commands.get(module, ())
        }
        command_graph = {key: set() for key in cycle_keys}
        for edge in edges:
            source_command = command_for_declaration.get(edge.source)
            target_command = command_for_declaration.get(edge.target)
            if source_command is None or target_command is None:
                continue
            source_key = (source_command.owner, source_command.root)
            target_key = (target_command.owner, target_command.root)
            if source_key in cycle_keys and target_key in cycle_keys:
                command_graph[source_key].add(target_key)

        index = 0
        indices = {}
        lowlinks = {}
        stack = []
        on_stack = set()
        cross_route_components = []

        def visit_command(key):
            nonlocal index
            indices[key] = index
            lowlinks[key] = index
            index += 1
            stack.append(key)
            on_stack.add(key)
            for target in command_graph[key]:
                if target not in indices:
                    visit_command(target)
                    lowlinks[key] = min(lowlinks[key], lowlinks[target])
                elif target in on_stack:
                    lowlinks[key] = min(lowlinks[key], indices[target])
            if lowlinks[key] == indices[key]:
                component = []
                while True:
                    target = stack.pop()
                    on_stack.remove(target)
                    component.append(target)
                    if target == key:
                        break
                modules = {
                    final_owner[name]
                    for item in component
                    for name in commands[item].declarations
                }
                if len(modules) > 1:
                    cross_route_components.append(component)

        for key in sorted(command_graph):
            if key not in indices:
                visit_command(key)
        for component in cross_route_components:
            details.append(
                "cross-route command SCC: "
                + ", ".join(sorted(key[1] for key in component))
            )
        raise MigrationError(
            "canonical module cycle: " + " -> ".join(cycle)
            + "\n" + "\n".join(details)
        )

    # Assert the seven known standalone wrappers are moved/blanked atomically.
    frozen_sources = {}
    wrapper_counts = Counter()
    for owner, relative in source_paths.items():
        payload = engine.git(root, "show", f"{BASE}:{relative}", binary=True)
        assert isinstance(payload, bytes)
        frozen_sources[owner] = payload.decode("utf-8")
    for command in commands.values():
        source = frozen_sources[command.owner]
        lines = source.splitlines(keepends=True)
        starts, offset = [], 0
        for line in lines:
            starts.append(offset)
            offset += len(line)
        raw = engine.utf16_offset(lines, starts, command.start_line, command.start_column)
        documented = engine.expanded_doc_start(source, raw)
        expanded = expanded_wrapper_start(source, documented)
        if expanded < documented:
            wrapper_counts[owner_leaf(command.owner)] += 1
    expected_wrappers = Counter(
        UnderdeterminedSolve=4,
        Higham21MGSRounded=1,
        Higham21GivensClosure=2,
    )
    if wrapper_counts != expected_wrappers:
        raise MigrationError(
            f"standalone wrapper inventory differs: {dict(wrapper_counts)}"
        )

    route_lines = [
        "format\t1",
        "declaration\thistorical_module\tdestination_module\tdecision\tkind\tvisibility\tcommand_root\tstart_line",
    ]
    for name in sorted(declarations):
        declaration = declarations[name]
        command = command_for_declaration[name]
        destination = final_owner[name]
        if command.decision == "retain_historical":
            decision = "retain_historical"
        elif destination.startswith("NumStability.Source."):
            decision = "relocate_source"
        else:
            decision = "relocate_reusable"
        route_lines.append("\t".join((
            name, declaration.module, destination, decision, declaration.kind,
            declaration.visibility, command.root, str(command.start_line),
        )))

    retention_lines = [
        "format\t1",
        "historical_module\thistorical_path\tselected\tprivate\tretained_public\tretained_private\tretained_total\trelocated\treusable\tsource\tfacade_kind",
    ]
    owner_public_representatives = {}
    for owner in owners:
        selected = [name for name, item in declarations.items() if item.module == owner]
        retained = [name for name in selected if name in retained_declarations]
        moved = [name for name in selected if name not in retained_declarations]
        private = [name for name in selected if declarations[name].visibility == "private"]
        retained_private = [name for name in retained if declarations[name].visibility == "private"]
        retained_public = [name for name in retained if declarations[name].visibility == "public"]
        reusable = [name for name in moved if final_owner[name].startswith("NumStability.Algorithms.")]
        source = [name for name in moved if final_owner[name].startswith("NumStability.Source.")]
        facade = "declaration_bearing" if retained else "pure_import_shim"
        retention_lines.append("\t".join((
            owner, source_paths[owner], str(len(selected)), str(len(private)),
            str(len(retained_public)), str(len(retained_private)), str(len(retained)),
            str(len(moved)), str(len(reusable)), str(len(source)), facade,
        )))
        public = sorted(name for name in selected if declarations[name].visibility == "public")
        owner_public_representatives[owner] = public[0] if public else None

    test_rows = ["kind\timport_modules\ttest_path\trepresentatives"]
    test_payloads: dict[Path, str] = {}
    module_public = defaultdict(list)
    for name, destination in final_owner.items():
        if destination in canonical_modules and declarations[name].visibility == "public":
            module_public[destination].append(name)
    module_public[eq4_locator] = sorted(
        name for module in eq4_leaves for name in module_public.get(module, ())
    )
    for index, module in enumerate(sorted(canonical_modules), 1):
        representative = sorted(module_public.get(module, ()))[0] if module_public.get(module) else None
        relative = Path(f"NumStabilityTest/Reorganization/W04/Canonical/C{index:03d}.lean")
        payload = f"import {module}\n"
        if representative:
            payload += f"\n#check {representative}\n"
        test_payloads[relative] = payload
        test_rows.append("\t".join((
            "canonical", module, relative.as_posix(), representative or "-",
        )))
    for index, owner in enumerate(owners, 1):
        representative = owner_public_representatives[owner]
        relative = Path(f"NumStabilityTest/Reorganization/W04/OldPath/O{index:03d}.lean")
        payload = f"import {owner}\n"
        if representative:
            payload += f"\n#check {representative}\n"
        test_payloads[relative] = payload
        test_rows.append("\t".join((
            "compatibility", owner, relative.as_posix(), representative or "-",
        )))

    def modules_below(prefixes: set[str]) -> list[str]:
        return sorted(
            module for module in canonical_modules
            if any(module.startswith(prefix + ".") for prefix in prefixes)
        )

    focused = {
        "SpecificationsAndSolvers": modules_below({R_SPEC, R_PSEUDO, R_SOLVE}),
        "QRGivensModifiedGramSchmidt": modules_below({R_QRF, R_GBE, R_GSR, R_MGSC, R_MGSR}),
        "SeminormalEquationsPipeline": modules_below({R_SNECT, R_SNEFE, R_SNEHC, R_SNEQR, R_SNETS}),
        "PerturbationConditioningProjectorsRankStability": modules_below({R_PCOMP, R_PFIX, R_COND, R_PROJ, R_RANK, R_BEN, R_BER}),
        "Chapter21SourceEndpoints": modules_below(SOURCE_PREFIXES),
        "ProtectedAcceptedInterfaces": [
            "NumStability.Algorithms.RankOneUpdate",
            "NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation",
            "NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec",
            "NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic",
        ],
        "ProtectedW90Consumers": [
            "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic",
            "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation",
            "NumStability.Source.Higham.Chapter20.Lemma11",
            "NumStability.Source.Higham.Chapter20.Theorem08",
        ],
        "ProtectedW90Dependencies": [
            "NumStability.Analysis.MatrixAlgebra",
            "NumStability.FloatingPoint.Model",
            "NumStability.Source.Higham.Chapter19.Core",
            "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve",
        ],
        "IntegratorCanonicalRetarget": [eq4_locator],
        "RetainedPrivateClosure": sorted(
            owner for owner in owners
            if any(command.decision == "retain_historical" for command in owner_commands[owner])
        ),
        "ReusableUnderdeterminedApi": modules_below(REUSABLE_PREFIXES),
    }
    focused_checks = {
        "ProtectedAcceptedInterfaces": [
            "NumStability.rankOneUpdateExact",
            "NumStability.problem7_1_neumann_componentwise_inequality_bound",
            "NumStability.CholeskyFactSpec",
            "NumStability.cholesky_solve_backward_error",
        ],
        "ProtectedW90Consumers": [
            "NumStability.theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint",
            "NumStability.theorem20_8MaxRelativePerturbation",
            "NumStability.higham20_lemma20_11_pseudoinverse_op2_le_recip_rankSingular",
            "NumStability.LSENullIntersectionTrivial",
        ],
        "ProtectedW90Dependencies": [
            "NumStability.matMul",
            "NumStability.FPModel",
            "H19.Problem19_1.householder_mul_defining_vector_neg",
            "NumStability.LSAugmentedNormalSystem.iff_rectLSNormalEquations",
        ],
        "IntegratorCanonicalRetarget": [
            "NumStability.RectMoorePenrosePseudoinverse",
            "NumStability.higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero",
            "NumStability.higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero",
            "NumStability.rectGram",
            "NumStability.rectMatMulVec_rectTransposeMulVec",
            "NumStability.rectTransposeMulVec",
            "NumStability.undetAplusOfGramInv_eq_rectMatMul_finiteTranspose",
            "NumStability.undetAplusOfGramNonsingInv",
            "NumStability.undetAplusOfGramNonsingInv_domain_projection_symmetric",
            "NumStability.undetGramNonsingInv",
        ],
    }
    for title, imports in focused.items():
        imports = sorted(imports)
        if not imports:
            raise MigrationError(f"focused test {title} has no imports")
        relative = Path(f"NumStabilityTest/Reorganization/W04/Focused/{title}.lean")
        payload = "".join(f"import {module}\n" for module in imports)
        representatives = []
        for module in imports:
            candidates = module_public.get(module, ())
            if candidates:
                representatives.append(sorted(candidates)[0])
        representatives.extend(focused_checks.get(title, ()))
        if representatives:
            for name in sorted(set(representatives)):
                payload += f"\n#check {name}"
            payload += "\n"
        test_payloads[relative] = payload
        test_rows.append("\t".join((
            "focused", ",".join(imports), relative.as_posix(),
            ",".join(sorted(set(representatives))) or "-",
        )))

    expected_generated_paths = {
        engine.module_path(module).as_posix() for module in canonical_modules
    } | {path.as_posix() for path in test_payloads}
    existing_generated_paths = {
        path.relative_to(root).as_posix()
        for path in root.rglob("*.lean")
        if (
            any(path.relative_to(root).as_posix().startswith(prefix) for prefix in prefix_paths)
            or path.relative_to(root).as_posix().startswith("NumStabilityTest/Reorganization/W04/")
        )
    }
    stale = sorted(existing_generated_paths - expected_generated_paths)
    if stale:
        raise MigrationError("stale W04 generated paths: " + ", ".join(stale))

    if not args.write and not args.check:
        print(json.dumps({
            "commands": len(commands),
            "retained_commands": int(metadata["retained_command_count"]),
            "retained_declarations": len(retained_declarations),
            "relocated_declarations": EXPECTED_RELOCATED_DECLARATIONS,
            "canonical_modules": len(canonical_modules),
            "tests": len(test_payloads),
            "used_prefixes": len(used_prefixes),
            "facades": len(owners),
        }, indent=2))
        return 0

    check = args.check
    for module in sorted(canonical_modules):
        if module == eq4_locator:
            payload = module_doc(
                module,
                dependencies[module],
                "Exact Chapter 21 equation 21.4 pseudoinverse endpoint.",
            )
        else:
            items = route_commands[module]
            owner = items[0].owner
            payload = module_doc(
                module,
                dependencies[module],
                "W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.",
            ) + "\n" + render_subset(
                engine,
                frozen_sources[owner],
                owner_commands[owner],
                {command.root for command in items},
            )
        scoped_write(
            root, engine.module_path(module), payload, owned_paths, allowed_writes, check
        )

    for owner in owners:
        retained_roots = {
            command.root for command in owner_commands[owner]
            if command.decision == "retain_historical"
        }
        moved_modules = {
            intended[(command.owner, command.root)]
            for command in owner_commands[owner]
            if command.decision == "move_candidate"
        }
        imports = set(engine.direct_imports(root, owner)) | moved_modules
        if retained_roots:
            payload = module_doc(
                owner,
                imports,
                "Historical W04 compatibility facade retaining the exact private reverse closure.",
            ) + "\n" + render_subset(
                engine, frozen_sources[owner], owner_commands[owner], retained_roots
            )
        else:
            payload = module_doc(
                owner,
                imports,
                "Import-only historical compatibility facade for the W04 migration.",
            )
        scoped_write(
            root, Path(source_paths[owner]), payload, owned_paths, allowed_writes, check
        )

    for relative, payload in sorted(test_payloads.items()):
        scoped_write(root, relative, payload, owned_paths, allowed_writes, check)
    for relative, payload in (
        (Path("docs/architecture/deliveries/W04/DECLARATION_ROUTES.tsv"), "\n".join(route_lines) + "\n"),
        (Path("docs/architecture/deliveries/W04/RETENTION.tsv"), "\n".join(retention_lines) + "\n"),
        (Path("docs/architecture/deliveries/W04/TEST_MATRIX.tsv"), "\n".join(test_rows) + "\n"),
    ):
        scoped_write(root, relative, payload, owned_paths, allowed_writes, check)
    action = "verified" if check else "wrote"
    print(
        f"{action} {len(canonical_modules)} canonical modules, 29 historical facades, "
        f"{len(test_payloads)} tests, and 1,238 declaration routes"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MigrationError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
