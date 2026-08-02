#!/usr/bin/env python3
"""Generate the reviewed W02 command-preserving module split.

The generator consumes the frozen P0002 graph and ``PRIVATE_CLOSURE.tsv``.
It copies complete Lean commands byte-for-byte into reviewed semantic leaves,
keeps genuine-private reverse closures in their historical owners, creates
``All`` entry points and focused import tests, and emits the delivery ledgers.

This script is intentionally W02-specific.  It refuses a projection, source
base, closure ledger, or destination outside the active B0002 contract.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import io
import json
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


BASE = "e6ef0107edb873f7a05ad8282df7efdf41a986d3"
P0002_SHA256 = "EA781015CD00CDC9EC152D71BE9D6F2993148294E8B3EBEF28B56E81C9C002DB"
EXPECTED_DECLARATIONS = 4_195
EXPECTED_PHYSICAL_DECLARATIONS = 2_478
EXPECTED_COMMANDS = 2_268
EXPECTED_RETAINED = 258

PHYSICAL = (
    "NumStability.Algorithms.HighamChapter8",
    "NumStability.Algorithms.HighamChapter8FanInClosure",
    "NumStability.Algorithms.IterativeRefinement",
    "NumStability.Algorithms.LU.Doolittle",
    "NumStability.Algorithms.NeumaierCompensatedFiniteFormat",
    "NumStability.Algorithms.PriestFiniteFormat",
    "NumStability.Algorithms.TriangularArbitraryOrder",
    "NumStability.Algorithms.TriangularNoGuard",
    "NumStability.Analysis.CramersRule",
    "NumStability.Analysis.DoubleRounding",
    "NumStability.Analysis.Error",
    "NumStability.Analysis.FusedMultiplyAdd",
    "NumStability.Analysis.HighamChapter7",
    "NumStability.Analysis.HighamChapter7Rectangular",
    "NumStability.Analysis.Midpoint",
    "NumStability.Analysis.ProblemDependentStability",
    "NumStability.Analysis.RoundingProductBounds",
    "NumStability.Analysis.SampleVariance",
    "NumStability.Analysis.TrigCancellation",
)
PHYSICAL_SET = set(PHYSICAL)


class MigrationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class Edge:
    kind: str
    source: str
    target: str


@dataclass(frozen=True)
class Command:
    owner: str
    root: str
    start_line: int
    start_column: int
    end_line: int
    end_column: int
    decision: str
    declarations: tuple[str, ...]


@dataclass(frozen=True)
class Interval:
    owner: str
    start: int
    end: int
    destination: str


def I(owner: str, start: int, end: int, destination: str) -> Interval:
    return Interval(owner, start, end, destination)


A = "NumStability.Algorithms"
N = "NumStability.Analysis"
S = "NumStability.Source.Higham"

INTERVALS = (
    I(f"{N}.CramersRule", 25, 128, f"{A}.LinearSystems.CramersRule.Core"),
    I(f"{N}.CramersRule", 128, 419, f"{S}.Chapter01.Section10.CramersRule.PrintedComparison"),
    I(f"{N}.CramersRule", 419, 999999, f"{S}.Chapter01.Problem09.CramersRule.ForwardError"),

    I(f"{N}.DoubleRounding", 31, 206, f"{N}.FloatingPointArithmetic.DoubleRounding.ToyBinary"),
    I(f"{N}.DoubleRounding", 206, 218, f"{S}.Chapter02.Section03.DoubleRounding.Counterexample"),
    I(f"{N}.DoubleRounding", 218, 271, f"{N}.FloatingPointArithmetic.DoubleRounding.FiniteNormalRange"),
    I(f"{N}.DoubleRounding", 271, 999999, f"{S}.Chapter02.Problem09.DoubleRounding.Counterexample"),

    I(f"{N}.Error", 25, 47, f"{N}.Error.Measures.ScalarDefinitions"),
    I(f"{N}.Error", 47, 78, f"{N}.FloatingPointArithmetic.ErrorModels.Additive"),
    I(f"{N}.Error", 78, 220, f"{N}.FloatingPointArithmetic.ErrorModels.NoGuardBasic"),
    I(f"{N}.Error", 220, 245, f"{S}.Chapter02.Section04.NoGuardModel.BinaryT3Example"),
    I(f"{N}.Error", 245, 388, f"{N}.FloatingPointArithmetic.ErrorModels.NoGuardModel"),
    I(f"{N}.Error", 388, 490, f"{N}.Error.Measures.ScalarProperties"),
    I(f"{N}.Error", 490, 514, f"{S}.Chapter01.Problem01.RelativeError.Bounds"),
    I(f"{N}.Error", 514, 573, f"{N}.Error.Measures.ScalarWitnesses"),
    I(f"{N}.Error", 573, 639, f"{N}.FloatingPointArithmetic.ErrorModels.AdditiveProperties"),
    I(f"{N}.Error", 639, 692, f"{N}.Error.Measures.Componentwise"),
    I(f"{N}.Error", 692, 716, f"{S}.Chapter01.Section03.ErrorSources.Core"),
    I(f"{N}.Error", 716, 809, f"{N}.Error.Measures.AccuracyPrecision"),
    I(f"{N}.Error", 809, 999999, f"{S}.Chapter01.Section07.Cancellation.Basic"),

    I(f"{N}.FusedMultiplyAdd", 21, 123, "NumStability.FloatingPoint.FusedMultiplyAdd.Core"),
    I(f"{N}.FusedMultiplyAdd", 123, 222, f"{S}.Chapter02.Problem26.ExactProduct.Discrepancy"),
    I(f"{N}.FusedMultiplyAdd", 222, 299, "NumStability.FloatingPoint.FusedMultiplyAdd.DotProductCounts"),
    I(f"{N}.FusedMultiplyAdd", 299, 999999, f"{S}.Chapter02.Section06.FusedMultiplyAdd.DotProductCount"),

    I(f"{N}.Midpoint", 29, 256, f"{N}.FloatingPointArithmetic.MidpointRounding.DecimalTieExamples"),
    I(f"{N}.Midpoint", 256, 999999, f"{S}.Chapter02.Problem08.MidpointRounding.Counterexample"),
    I(f"{N}.TrigCancellation", 27, 341, f"{N}.FloatingPointArithmetic.TrigonometricCancellation.Core"),
    I(f"{N}.TrigCancellation", 341, 410, f"{S}.Chapter01.Problem03.CancellationRewrites.Algebra"),
    I(f"{N}.TrigCancellation", 410, 999999, f"{S}.Chapter01.Section07.TrigonometricCancellation.Example"),
    I(f"{N}.RoundingProductBounds", 25, 382, f"{N}.Error.RoundingProducts.Core"),
    I(f"{N}.RoundingProductBounds", 382, 999999, f"{S}.Chapter03.Problem02.ProductBounds.PositiveFactors"),

    I(f"{N}.ProblemDependentStability", 28, 844, f"{N}.ProblemDependentStability.HessenbergDeterminant"),
    I(f"{N}.ProblemDependentStability", 844, 1190, f"{S}.Chapter01.Section16.ProblemDependentStability.ExactExample"),
    I(f"{N}.ProblemDependentStability", 1190, 999999, f"{S}.Chapter01.Section16.ProblemDependentStability.Table13IeeeSingle"),

    I(f"{N}.SampleVariance", 34, 141, f"{N}.Statistics.SampleVariance.Core"),
    I(f"{N}.SampleVariance", 141, 718, f"{N}.Statistics.SampleVariance.TwoPass"),
    I(f"{N}.SampleVariance", 718, 1031, f"{S}.Chapter01.Problem10.TwoPassSampleVariance.Bounds"),
    I(f"{N}.SampleVariance", 1031, 1891, f"{N}.Statistics.SampleVariance.Updating"),
    I(f"{N}.SampleVariance", 1891, 3221, f"{S}.Chapter01.Section09.SampleVariance.Examples"),
    I(f"{N}.SampleVariance", 3221, 999999, f"{S}.Chapter01.Problem07.SampleVarianceConditioning.ConditionNumbers"),

    I(f"{A}.LU.Doolittle", 34, 67, f"{A}.LinearSystems.LU.Doolittle.Basic"),
    I(f"{A}.LU.Doolittle", 67, 558, f"{A}.LinearSystems.LU.Doolittle.RoundedEntries"),
    I(f"{A}.LU.Doolittle", 558, 1547, f"{A}.LinearSystems.LU.Doolittle.Budgets"),
    I(f"{A}.LU.Doolittle", 1547, 2110, f"{A}.LinearSystems.LU.Doolittle.Certificates"),
    I(f"{A}.LU.Doolittle", 2110, 999999, f"{A}.LinearSystems.LU.Doolittle.BackwardError"),

    I(f"{A}.NeumaierCompensatedFiniteFormat", 26, 535, f"{A}.Summation.Compensated.Neumaier.ExactResidual"),
    I(f"{A}.NeumaierCompensatedFiniteFormat", 535, 566, f"{S}.Chapter04.Equation10.Neumaier.ResidualBound"),
    I(f"{A}.NeumaierCompensatedFiniteFormat", 566, 703, f"{A}.Summation.Compensated.Neumaier.AdaptiveFiniteFormat"),
    I(f"{A}.NeumaierCompensatedFiniteFormat", 703, 734, f"{S}.Chapter04.Equation10.Neumaier.AdaptiveBound"),
    I(f"{A}.NeumaierCompensatedFiniteFormat", 734, 972, f"{A}.Summation.Compensated.Neumaier.FiniteExecutor"),
    I(f"{A}.NeumaierCompensatedFiniteFormat", 972, 999999, f"{S}.Chapter04.Equation10.Neumaier.FiniteBound"),

    I(f"{A}.PriestFiniteFormat", 19, 319, f"{A}.Summation.Compensated.Priest.FiniteFormat"),
    I(f"{A}.PriestFiniteFormat", 319, 999999, f"{S}.Chapter04.Algorithm03.Priest.SourceAssumptions"),
    I(f"{A}.IterativeRefinement", 38, 862, f"{A}.LinearSystems.IterativeRefinement.Core"),
    I(f"{A}.IterativeRefinement", 862, 1598, f"{S}.Chapter12.IterativeRefinement.LegacyChapter11Surface"),
    I(f"{A}.IterativeRefinement", 1598, 999999, f"{S}.Chapter12.IterativeRefinement.Chapter12Bounds"),

    I(f"{A}.TriangularArbitraryOrder", 29, 442, f"{A}.Summation.Tree.ArbitraryOrderError.PivotNormalized"),
    I(f"{A}.TriangularArbitraryOrder", 442, 999999, f"{S}.Chapter08.Section03.TriangularSystems.ArbitraryOrder"),
    I(f"{A}.TriangularNoGuard", 16, 473, f"{A}.LinearSystems.Triangular.ErrorAnalysis.NoGuardBackward"),
    I(f"{A}.TriangularNoGuard", 473, 609, f"{S}.Chapter08.Problem01.NoGuardSubstitution.BackwardSubstitution"),
    I(f"{A}.TriangularNoGuard", 609, 656, f"{A}.LinearSystems.Triangular.ErrorAnalysis.NoGuardForward"),
    I(f"{A}.TriangularNoGuard", 656, 999999, f"{S}.Chapter08.Problem01.NoGuardSubstitution.ForwardSubstitution"),

    I(f"{N}.HighamChapter7", 33, 78, f"{S}.Chapter07.LinearSystemsConditioning.ForwardErrorKernels"),
    I(f"{N}.HighamChapter7", 78, 562, f"{S}.Chapter07.LinearSystemsConditioning.Problem01"),
    I(f"{N}.HighamChapter7", 562, 849, f"{N}.Conditioning.LinearSystems.SubordinatePerturbation"),
    I(f"{N}.HighamChapter7", 849, 1216, f"{S}.Chapter07.LinearSystemsConditioning.ConditionNumbers"),
    I(f"{N}.HighamChapter7", 1216, 1583, f"{S}.Chapter07.LinearSystemsConditioning.Problem05"),
    I(f"{N}.HighamChapter7", 1583, 1799, f"{S}.Chapter07.LinearSystemsConditioning.Problem06Rowwise"),
    I(f"{N}.HighamChapter7", 1799, 2038, f"{S}.Chapter07.LinearSystemsConditioning.Problem06Columnwise"),
    I(f"{N}.HighamChapter7", 2038, 3196, f"{S}.Chapter07.LinearSystemsConditioning.Problem09Linearized"),
    I(f"{N}.HighamChapter7", 3196, 5422, f"{S}.Chapter07.Equation25.InverseConditioning.ExactPerturbation"),
    I(f"{N}.HighamChapter7", 5422, 6684, f"{S}.Chapter07.LinearSystemsConditioning.Problem09Exact"),
    I(f"{N}.HighamChapter7", 6684, 6708, f"{S}.Chapter06.Theorem05.DistanceToSingularity.Chapter07Equation26"),
    I(f"{N}.HighamChapter7", 6708, 7472, f"{S}.Chapter07.LinearSystemsConditioning.RowScaling"),
    I(f"{N}.HighamChapter7", 7472, 7625, f"{S}.Chapter07.LinearSystemsConditioning.Problem04"),
    I(f"{N}.HighamChapter7", 7625, 8466, f"{S}.Chapter07.LinearSystemsConditioning.Theorem05.Part01"),
    I(f"{N}.HighamChapter7", 8466, 10102, f"{S}.Chapter07.LinearSystemsConditioning.Theorem05.Part02"),
    I(f"{N}.HighamChapter7", 10102, 11804, f"{S}.Chapter07.LinearSystemsConditioning.Theorem05.Part03"),
    I(f"{N}.HighamChapter7", 11804, 13323, f"{S}.Chapter07.LinearSystemsConditioning.Theorem05.Part04"),
    I(f"{N}.HighamChapter7", 13323, 14073, f"{S}.Chapter07.LinearSystemsConditioning.Theorem05.Part05"),
    I(f"{N}.HighamChapter7", 14073, 15544, f"{S}.Chapter07.LinearSystemsConditioning.Theorem05.Part06"),
    I(f"{N}.HighamChapter7", 15544, 15668, f"{S}.Chapter07.Corollary06.LinearSystemsConditioning.Basic"),
    I(f"{N}.HighamChapter7", 15668, 15951, f"{S}.Chapter07.LinearSystemsConditioning.Theorem07FrobeniusScaling"),
    I(f"{N}.HighamChapter7", 15951, 18057, f"{S}.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part01"),
    I(f"{N}.HighamChapter7", 18057, 19792, f"{S}.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part02"),
    I(f"{N}.HighamChapter7", 19792, 20508, f"{S}.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part03"),
    I(f"{N}.HighamChapter7", 20508, 22799, f"{S}.Chapter07.LinearSystemsConditioning.Problem10OneNorm"),
    I(f"{N}.HighamChapter7", 22799, 23598, f"{S}.Chapter07.LinearSystemsConditioning.Problem15Hadamard"),
    I(f"{N}.HighamChapter7", 23598, 23965, f"{S}.Chapter07.LinearSystemsConditioning.Theorem04"),
    I(f"{N}.HighamChapter7", 23965, 24161, f"{S}.Chapter07.LinearSystemsConditioning.Problem02"),
    I(f"{N}.HighamChapter7", 24161, 24290, f"{S}.Chapter07.LinearSystemsConditioning.Theorem02"),
    I(f"{N}.HighamChapter7", 24290, 24766, f"{S}.Chapter07.LinearSystemsConditioning.Equation05"),
    I(f"{N}.HighamChapter7", 24766, 25137, f"{S}.Chapter07.LinearSystemsConditioning.Problem07"),
    I(f"{N}.HighamChapter7", 25137, 25494, f"{S}.Chapter07.LinearSystemsConditioning.Problem08RectangularBackwardError"),
    I(f"{N}.HighamChapter7", 25494, 25591, f"{S}.Chapter07.LinearSystemsConditioning.Lemma09"),
    I(f"{N}.HighamChapter7", 25591, 25694, f"{S}.Chapter07.LinearSystemsConditioning.ComputedResidual"),
    I(f"{N}.HighamChapter7", 25694, 26022, f"{S}.Chapter07.LinearSystemsConditioning.Problem13SparseResidual"),
    I(f"{N}.HighamChapter7", 26022, 26171, f"{S}.Chapter07.LinearSystemsConditioning.Equation32"),
    I(f"{N}.HighamChapter7", 26171, 26188, f"{S}.Chapter07.LinearSystemsConditioning.Equation33"),
    I(f"{N}.HighamChapter7", 26188, 999999, f"{S}.Chapter07.LinearSystemsConditioning.Theorem08Aliases"),
    I(f"{N}.HighamChapter7Rectangular", 15, 999999, f"{S}.Chapter07.LinearSystemsConditioning.RectangularTheorems"),

    I(f"{A}.HighamChapter8", 27, 144, f"{S}.Chapter08.Section01.BackwardErrorAnalysis.Core"),
    I(f"{A}.HighamChapter8", 144, 550, f"{S}.Chapter08.Section02.ForwardErrorAnalysis.NormBounds"),
    I(f"{A}.HighamChapter8", 550, 2315, f"{S}.Chapter08.Problem09.KahanSingularValues.KahanMatrix"),
    I(f"{A}.HighamChapter8", 2315, 2537, f"{S}.Chapter08.Problem02.ComparisonMatrixWitness.RatioWitness"),
    I(f"{A}.HighamChapter8", 2537, 2568, f"{S}.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBoundsPrelude"),
    I(f"{A}.HighamChapter8", 2568, 2782, f"{S}.Chapter08.Lemma08.CorrectedCondition.RowDominance"),
    I(f"{A}.HighamChapter8", 2782, 3086, f"{S}.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBounds"),
    I(f"{A}.HighamChapter8", 3086, 3210, f"{S}.Chapter08.Problem03.UnitTriangularSubstitution.Bound"),
    I(f"{A}.HighamChapter8", 3210, 3642, f"{S}.Chapter08.Problem04.MMatrixSubstitution.Comparison"),
    I(f"{A}.HighamChapter8", 3642, 4618, f"{S}.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude"),
    I(f"{A}.HighamChapter8", 4618, 4712, f"{S}.Chapter08.Problem05.InverseNormBounds.ZInverse"),
    I(f"{A}.HighamChapter8", 4712, 4840, f"{S}.Chapter08.Section03.TriangularSystems.InverseBoundsUpper"),
    I(f"{A}.HighamChapter8", 4840, 5021, f"{S}.Chapter08.Problem06.ComparisonInverseBounds.VectorBounds"),
    I(f"{A}.HighamChapter8", 5021, 5227, f"{S}.Chapter08.Section03.TriangularSystems.InverseBoundsLower"),
    I(f"{A}.HighamChapter8", 5227, 5708, f"{S}.Chapter08.Section04.FanInCore.Factors"),
    I(f"{A}.HighamChapter8", 5708, 5907, f"{S}.Chapter08.Equation14.FanInExecutor.Executor"),
    I(f"{A}.HighamChapter8", 5907, 6578, f"{S}.Chapter08.Section04.FanInCore.AllOrdersEnvelope"),
    I(f"{A}.HighamChapter8", 6578, 6624, f"{S}.Chapter08.Equation15.GlobalEnvelopeCounterexample.LocalCancellation"),
    I(f"{A}.HighamChapter8", 6624, 7154, f"{S}.Chapter08.Section04.FanInCore.ResidualForwardBounds"),
    I(f"{A}.HighamChapter8", 7154, 7517, f"{S}.Chapter08.Problem07.DiagonalScaling.Bounds"),
    I(f"{A}.HighamChapter8", 7517, 7573, f"{S}.Chapter08.Problem01.NoGuardSubstitution.Aliases"),
    I(f"{A}.HighamChapter8", 7573, 999999, f"{S}.Chapter08.Problem08.SingleEntrySingularity.RankOne"),
    I(f"{A}.HighamChapter8FanInClosure", 15, 999999, f"{S}.Chapter08.Equation15.GlobalEnvelopeCounterexample.RawCube"),
)


CRAMER_CORE = {
    "NumStability.cramer2x2Solution_zero",
    "NumStability.cramer2x2Solution_one",
    "NumStability.cramer2x2Solution_solves",
}

INVERSE_REUSABLE = {
    "NumStability.problem7_1_neumann_componentwise_inequality_bound",
    "NumStability.ch7InverseLinearizedEntry",
    "NumStability.ch7InverseQuadraticRemainderEntry",
    "NumStability.ch7_matMul_of_IsLeftInverse",
    "NumStability.ch7_matMul_of_IsRightInverse",
    "NumStability.ch7InverseLinearizedEntry_eq_matMul",
    "NumStability.ch7_inversePerturbation_decomposition",
    "NumStability.problem7_11_exact_inverse_firstOrder_remainder_identity",
    "NumStability.ch7_matMul_nonneg",
    "NumStability.ch7_matMul_le_of_nonneg_left",
    "NumStability.ch7_matMul_abs_le_of_scaled_abs_le",
    "NumStability.ch7InverseFirstProductSensitivity",
    "NumStability.ch7InverseFirstProductSensitivity_nonneg",
    "NumStability.ch7InverseQuadraticRemainderSensitivityEntry",
    "NumStability.ch7InverseQuadraticRemainderSensitivityEntry_nonneg",
    "NumStability.ch7_inverseFirstProduct_abs_le",
    "NumStability.ch7InverseQuadraticRemainderEntry_abs_le",
    "NumStability.ch7_abs_entry_le_infNorm",
    "NumStability.ch7MatAddId",
    "NumStability.ch7_isRightInverse_of_isLeftInverse",
    "NumStability.ch7_matAdd_id_abs_solution_bound_of_abs_infNorm_bound",
    "NumStability.ch7_matAdd_id_det_ne_zero_of_abs_infNorm_bound",
    "NumStability.ch7_nonsingInv_matAdd_id_entry_abs_le_of_abs_infNorm_bound",
    "NumStability.ch7_nonsingInv_matAdd_id_infNorm_le_of_abs_infNorm_bound",
    "NumStability.ch7Problem711PerturbedInverseCandidate",
    "NumStability.problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound",
    "NumStability.problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound",
    "NumStability.ch7_abs_left_product_infNorm_le_of_componentwise_bound",
    "NumStability.ch7RectMatMulVecLinearMap",
    "NumStability.ch7_exists_rect_left_inverse_of_linear_left_inverse",
    "NumStability.ch7_exists_rect_left_inverse_of_rectMatMulVec_injective",
}

PERRON_REUSABLE = {
    "NumStability.ch7_exists_pos_le_all_fin",
    "NumStability.ch7_perronScalar_nonneg_of_nonneg_eigenvector",
    "NumStability.ch7_exists_pos_entry_of_nonzero_nonneg",
    "NumStability.ch7_perronScalar_nonneg_of_nonzero_nonneg_eigenvector",
    "NumStability.ch7_perronScalar_pos_of_nonneg_eigenvector_entry_pos",
    "NumStability.ch7_infNorm_ge_of_nonneg_right_eigenvector",
    "NumStability.ch7IsComplexEigenvalueRadius",
    "NumStability.ch7ComplexEigenvalueModulusSet",
    "NumStability.ch7_complexEigenvalueModulusSet_isGreatest_of_isComplexEigenvalueRadius",
    "NumStability.ch7_complexEigenvalueModulusSet_sSup_eq_of_isComplexEigenvalueRadius",
    "NumStability.ch7_complexEigenvalueModulusSet_eq_complexMatrixEigenvalueModulusSet",
    "NumStability.ch7_complexEigenvalueModulusSet_eq_toLin_spectrum_modulusSet",
    "NumStability.ch7_isMaxComplexMatrixEigenvalueModulus_of_isComplexEigenvalueRadius",
    "NumStability.ch7_toLin_spectrum_modulusSet_isGreatest_of_isComplexEigenvalueRadius",
    "NumStability.ch7_toLin_exists_spectralRadius_attaining_eigenpair",
    "NumStability.ch7_abs_complex_eigenvector_subeigenvector_of_nonneg_matrix",
    "NumStability.ch7_exists_spectralRadius_attaining_nonneg_subeigenvector",
    "NumStability.ch7_complex_eigenvalue_norm_le_of_positive_real_eigenvector",
    "NumStability.ch7_real_positive_eigenvector_complexified",
    "NumStability.ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector",
    "NumStability.ch7_matrix_mulVec_eq_matMulVec",
    "NumStability.ch7_matrix_pow_mulVec_eigen",
    "NumStability.ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector",
    "NumStability.ch7_irreducible_pow_mulVec_pos_of_nonzero_nonneg",
    "NumStability.ch7_matrix_pow_mulVec_nonneg_of_nonneg",
    "NumStability.ch7_matrix_mulVec_mono_of_nonneg",
    "NumStability.ch7_matrix_pow_mulVec_subeigen_le_of_nonneg",
    "NumStability.ch7_complexVec_norm_eq_coord_of_nonempty",
    "NumStability.ch7_realRectToCMatrix_matrix_pow",
    "NumStability.ch7_realRectToCMatrix_pow_mulVec_complexified",
    "NumStability.ch7_matrix_pow_opNorm_ge_pow_subeigen",
    "NumStability.ch7_matrix_spectralRadius_ge_of_positive_right_subeigenvector",
    "NumStability.ch7_toLin_spectralRadius_eq_matrix_spectralRadius",
    "NumStability.ch7_toLin_spectralRadius_ge_of_positive_right_subeigenvector",
    "NumStability.ch7_matrix_pow_mulVec_subeigen_step_of_nonneg",
    "NumStability.ch7_exists_irreducible_pow_sum_mulVec_pos_of_nonzero_nonneg",
    "NumStability.ch7_exists_positive_subeigenvector_of_irreducible_nonzero_nonneg_subeigen",
    "NumStability.ch7_exists_stronger_positive_subeigenvector_of_strict_subeigen",
    "NumStability.ch7_positive_subeigenvector_eigen_or_exists_stronger",
    "NumStability.ch7_exists_spectralRadius_attaining_positive_subeigenvector",
    "NumStability.ch7_exists_spectralRadius_attaining_positive_eigenvector",
    "NumStability.ch7_matrix_isPrimitive_of_pos_entries",
    "NumStability.ch7_matrix_isIrreducible_of_pos_entries",
}

EXACT_DESTINATION = {
    **{name: f"{A}.LinearSystems.CramersRule.Core" for name in CRAMER_CORE},
    **{name: f"{N}.Conditioning.LinearSystems.InversePerturbation" for name in INVERSE_REUSABLE},
    **{name: f"{N}.Conditioning.LinearSystems.PerronFrobenius" for name in PERRON_REUSABLE},
}

FACADE_EXTRA = {
    f"{A}.Summation.Compensated.Priest": (
        f"{A}.PriestAccuracy", f"{A}.PriestDefectBounded",
    ),
    f"{S}.Chapter01.Section02.ErrorMeasures": (f"{N}.Error.Measures.All",),
    f"{S}.Chapter01.Section04.AccuracyAndPrecision": (f"{N}.Error.Measures.All",),
    f"{S}.Chapter02.Equation06.NoGuardModel": (f"{N}.FloatingPointArithmetic.ErrorModels.All",),
    f"{S}.Chapter02.Equation08.AdditiveError": (f"{N}.FloatingPointArithmetic.ErrorModels.All",),
    f"{S}.Chapter02.Section03.DoubleRounding": (f"{N}.FloatingPointArithmetic.DoubleRounding.All",),
    f"{S}.Chapter02.Section04.NoGuardModel": (f"{N}.FloatingPointArithmetic.ErrorModels.All",),
    f"{S}.Chapter03.Lemma01.RoundingProducts": (f"{N}.Error.RoundingProducts.All",),
    f"{S}.Chapter03.Lemma04.SmallUnitProductBounds": (f"{N}.Error.RoundingProducts.All",),
    f"{S}.Chapter03.Section10.WilkinsonProductBound": (f"{N}.Error.RoundingProducts.All",),
    f"{S}.Chapter04.Algorithm03.Priest": (f"{A}.Summation.Compensated.Priest.All",),
    f"{S}.Chapter04.Equation10.Neumaier": (f"{A}.Summation.Compensated.Neumaier.All",),
    f"{S}.Chapter06.Theorem05.DistanceToSingularity": (f"{N}.Conditioning.DistanceToSingularity",),
    f"{S}.Chapter08.Problem01.NoGuardSubstitution": (f"{A}.LinearSystems.Triangular.ErrorAnalysis.All",),
    f"{S}.Chapter12.IterativeRefinement": (f"{A}.LinearSystems.IterativeRefinement.All",),
}


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def git(repo: Path, *args: str, binary: bool = False) -> str | bytes:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False,
    )
    if result.returncode:
        raise MigrationError(result.stderr.decode("utf-8", "replace").strip())
    return result.stdout if binary else result.stdout.decode("utf-8").strip()


def module_path(module: str, suffix: str = ".lean") -> Path:
    return Path(*module.split(".")).with_suffix(suffix)


def read_projection(path: Path) -> tuple[dict[str, Declaration], tuple[Edge, ...]]:
    payload = path.read_bytes()
    if sha256(payload) != P0002_SHA256:
        raise MigrationError("P0002 hash differs from the B0002 contract")
    declarations: dict[str, Declaration] = {}
    edges: list[Edge] = []
    with gzip.open(io.BytesIO(payload), "rt", encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) == 5 and row[0] == "declaration":
                d = Declaration(*row[1:])
                declarations[d.name] = d
            elif len(row) == 4 and row[0] == "edge":
                edges.append(Edge(*row[1:]))
    if len(declarations) != EXPECTED_DECLARATIONS:
        raise MigrationError(f"expected {EXPECTED_DECLARATIONS} declarations")
    return declarations, tuple(edges)


def read_closure(path: Path) -> tuple[dict[tuple[str, str], Command], dict[str, str]]:
    commands: dict[tuple[str, str], Command] = {}
    source_paths: dict[str, str] = {}
    retained = 0
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if row and row[0] == "owner":
                source_paths[row[1]] = row[2]
            elif row and row[0] == "command":
                command = Command(
                    owner=row[1], root=row[2], start_line=int(row[4]),
                    start_column=int(row[5]), end_line=int(row[6]),
                    end_column=int(row[7]), decision=row[8],
                    declarations=tuple(json.loads(row[18])),
                )
                commands[(command.owner, command.root)] = command
                retained += command.decision == "retain_historical"
    if len(commands) != EXPECTED_COMMANDS or retained != EXPECTED_RETAINED:
        raise MigrationError(
            f"closure ledger differs: commands={len(commands)}, retained={retained}"
        )
    if set(source_paths) != PHYSICAL_SET:
        raise MigrationError("closure owner set differs from the 19 physical owners")
    return commands, source_paths


def read_full_declarations(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) == 5 and row[0] == "declaration":
                result[row[1]] = row[2]
            elif row and row[0] == "edge":
                break
    return result


def destination_for(command: Command) -> str:
    exact = {EXACT_DESTINATION[name] for name in command.declarations if name in EXACT_DESTINATION}
    if command.root.startswith("NumStability.corollary7_6_"):
        exact.add(f"{S}.Chapter07.Corollary06.LinearSystemsConditioning.Results")
    if len(exact) > 1:
        raise MigrationError(f"{command.root}: conflicting exact destinations {exact}")
    if exact:
        return next(iter(exact))
    matches = [
        interval.destination for interval in INTERVALS
        if interval.owner == command.owner
        and interval.start <= command.start_line < interval.end
    ]
    if len(matches) != 1:
        raise MigrationError(
            f"{command.owner}:{command.start_line} {command.root}: interval matches {matches}"
        )
    return matches[0]


def utf16_offset(lines: list[str], starts: list[int], line1: int, column: int) -> int:
    line = line1 - 1
    content = lines[line]
    content = content[:-1] if content.endswith("\n") else content
    if content.endswith("\r"):
        content = content[:-1]
    units = 0
    for index, char in enumerate(content):
        if units == column:
            return starts[line] + index
        units += 2 if ord(char) > 0xFFFF else 1
        if units > column:
            raise MigrationError(f"coordinate splits surrogate pair at {line1}:{column}")
    if units == column:
        return starts[line] + len(content)
    raise MigrationError(f"coordinate exceeds line at {line1}:{column}")


def expanded_doc_start(source: str, start: int) -> int:
    cursor = start
    while cursor and source[cursor - 1].isspace():
        cursor -= 1
    if cursor < 2 or source[cursor - 2:cursor] != "-/":
        return start
    opening = source.rfind("/-", 0, cursor - 2)
    if opening >= 0 and source.startswith("/--", opening):
        return opening
    return start


def blank_region(chars: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if chars[index] not in "\r\n":
            chars[index] = " "


IMPORT_RE = re.compile(r"(?m)^import[ \t]+[^\r\n]+(?:\r?\n|$)")


def render_subset(
    source: str,
    commands: list[Command],
    keep: set[str],
    imports: set[str],
) -> str:
    lines = source.splitlines(keepends=True)
    starts: list[int] = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    chars = list(source)
    for match in IMPORT_RE.finditer(source):
        blank_region(chars, match.start(), match.end())
    prior_end = -1
    for command in sorted(commands, key=lambda item: (item.start_line, item.start_column)):
        start = utf16_offset(lines, starts, command.start_line, command.start_column)
        end = utf16_offset(lines, starts, command.end_line, command.end_column)
        start = expanded_doc_start(source, start)
        if start < prior_end:
            raise MigrationError(f"overlapping expanded command span at {command.root}")
        prior_end = end
        if command.root not in keep:
            blank_region(chars, start, end)
    header = "".join(f"import {module}\n" for module in sorted(imports)) + "\n"
    rendered = header + "".join(chars)
    # Removed command bodies are masked to preserve all source coordinates.
    # Collapse their now-whitespace-only line tails so the committed drafts do
    # not acquire thousands of trailing-space diagnostics.  The frozen inputs
    # themselves pass ``git diff --check``, so this does not alter a retained
    # command byte.
    rendered = re.sub(r"[ \t]+(?=\r?$)", "", rendered, flags=re.MULTILINE)
    if not rendered.endswith("\n"):
        rendered += "\n"
    return rendered


DIRECT_IMPORT_RE = re.compile(
    r"(?m)^(?:public[ \t]+|private[ \t]+)?import[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)


def direct_imports(root: Path, owner: str) -> set[str]:
    """Read imports from the immutable source, never from mutable build state."""
    relative = module_path(owner).as_posix()
    source = git(root, "show", f"{BASE}:{relative}")
    assert isinstance(source, str)
    imports = set(DIRECT_IMPORT_RE.findall(source))
    if not imports:
        raise MigrationError(f"{owner}: frozen source has no direct imports")
    return imports


def safe_write(root: Path, relative: Path, payload: str, allowed: tuple[str, ...]) -> None:
    posix = relative.as_posix()
    if not any(posix.startswith(prefix) for prefix in allowed):
        raise MigrationError(f"refusing out-of-contract write: {posix}")
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding="utf-8", newline="\n")


def lean_doc(title: str, imports: set[str]) -> str:
    return (
        "".join(f"import {module}\n" for module in sorted(imports))
        + "\n/-!\n# " + title + "\n\n"
        + "W02 semantic entry point generated from the reviewed B0002 routing contract.\n-/\n"
    )


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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--control-root", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    root = args.project_root.resolve()
    control = args.control_root.resolve()
    delivery = root / "docs/architecture/deliveries/W02"
    projection_path = control / "docs/architecture/phases/2026-08-repository-reorganization/projections/P0002.tsv.gz"
    combined_path = control / "benchmark-results/C0002-combined.tsv"
    closure_path = delivery / "PRIVATE_CLOSURE.tsv"
    contract_path = control / "docs/architecture/phases/2026-08-repository-reorganization/branches/B0002.json"
    selector_path = control / "docs/architecture/phases/2026-08-repository-reorganization/selectors/W02.tsv"
    scope_path = control / "docs/architecture/phases/2026-08-repository-reorganization/scope.tsv"

    if git(root, "rev-parse", f"{BASE}^{{commit}}") != BASE:
        raise MigrationError("frozen W02 base is unavailable")
    declarations, edges = read_projection(projection_path)
    commands, source_paths = read_closure(closure_path)
    full_modules = read_full_declarations(combined_path)
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if contract["base_sha"] != BASE or contract["branch_name"] != "codex/reorg-2026-08-w02-foundations":
        raise MigrationError("wrong B0002 contract")
    destination_prefixes = tuple(
        item["path"] for item in contract["destination_prefixes"]
        if item["path"].startswith("NumStability/")
    )
    allowed_writes = destination_prefixes + (
        "NumStabilityTest/Reorganization/W02/",
        "docs/architecture/deliveries/W02/",
    ) + tuple(path for path in source_paths.values())

    command_for_declaration: dict[str, Command] = {}
    for command in commands.values():
        for name in command.declarations:
            if name in command_for_declaration:
                raise MigrationError(f"duplicate command assignment for {name}")
            command_for_declaration[name] = command
    physical_selected = {name for name, d in declarations.items() if d.module in PHYSICAL_SET}
    if set(command_for_declaration) != physical_selected or len(physical_selected) != EXPECTED_PHYSICAL_DECLARATIONS:
        raise MigrationError("physical command ledger does not cover P0002 exactly")

    outgoing: dict[str, list[Edge]] = defaultdict(list)
    for edge in edges:
        outgoing[edge.source].append(edge)

    # The reviewed Chapter 7 reusable seeds name the semantic closures, while
    # small unnumbered support commands can sit earlier in the historical
    # source.  Close each reusable route over same-owner command dependencies
    # before assigning final owners.  This keeps the reusable layer free of
    # imports from ``Source`` without changing any declaration or proof.
    intended = {key: destination_for(command) for key, command in commands.items()}
    queue = [
        key for key, module in intended.items()
        if not module.startswith("NumStability.Source.")
        and commands[key].decision == "move_candidate"
    ]
    cursor = 0
    while cursor < len(queue):
        key = queue[cursor]
        cursor += 1
        command = commands[key]
        module = intended[key]
        for name in command.declarations:
            for edge in outgoing.get(name, ()):
                target_command = command_for_declaration.get(edge.target)
                if target_command is None or target_command.owner != command.owner:
                    continue
                target_key = (target_command.owner, target_command.root)
                if target_command.decision == "retain_historical":
                    raise MigrationError(
                        f"reusable command {command.root} depends on retained {target_command.root}"
                    )
                target_module = intended[target_key]
                if target_module.startswith("NumStability.Source."):
                    intended[target_key] = module
                    queue.append(target_key)

    final_owner: dict[str, str] = {}
    for key, command in commands.items():
        owner = command.owner if command.decision == "retain_historical" else intended[key]
        for name in command.declarations:
            final_owner[name] = owner

    route_commands: dict[str, list[Command]] = defaultdict(list)
    owner_commands: dict[str, list[Command]] = defaultdict(list)
    for key, command in commands.items():
        owner_commands[command.owner].append(command)
        if command.decision == "move_candidate":
            route_commands[intended[key]].append(command)
    route_modules = set(interval.destination for interval in INTERVALS) | set(EXACT_DESTINATION.values())
    route_modules.add(f"{S}.Chapter07.Corollary06.LinearSystemsConditioning.Results")

    dependencies: dict[str, set[str]] = {module: set() for module in route_modules}
    for module, owned_commands in route_commands.items():
        historical = {command.owner for command in owned_commands}
        if len(historical) != 1:
            raise MigrationError(f"{module}: commands from multiple historical owners")
        historical_owner = next(iter(historical))
        imports = direct_imports(root, historical_owner)
        imports = {
            item for item in imports
            if item not in PHYSICAL_SET
            and (module.startswith("NumStability.Source.") or not item.startswith("NumStability.Source."))
        }
        for command in owned_commands:
            for name in command.declarations:
                for edge in outgoing.get(name, ()):
                    target = edge.target
                    if target in final_owner:
                        target_module = final_owner[target]
                        if target_module in PHYSICAL_SET:
                            raise MigrationError(
                                f"movable {name} still depends on retained {target}"
                            )
                    else:
                        target_module = full_modules.get(target)
                    if not target_module or target_module == module:
                        continue
                    if target_module in PHYSICAL_SET:
                        raise MigrationError(f"unmapped physical dependency {name} -> {target}")
                    if target_module.startswith("NumStability.Source.") and not module.startswith("NumStability.Source."):
                        raise MigrationError(f"reusable-to-source edge {name} -> {target}")
                    if target_module.startswith("NumStability."):
                        imports.add(target_module)
        imports.discard(historical_owner)
        dependencies[module] = imports

    graph = {module: {item for item in imports if item in route_modules} for module, imports in dependencies.items()}
    cycle = topological_cycle(graph)
    if cycle:
        raise MigrationError("route-module dependency cycle: " + " -> ".join(cycle))

    # Every B0002 production prefix receives a descendant All entry point.
    all_modules: dict[str, set[str]] = {}
    for prefix in destination_prefixes:
        base = prefix.rstrip("/").replace("/", ".")
        leaves = {module for module in route_modules if module.startswith(base + ".")}
        leaves.update(FACADE_EXTRA.get(base, ()))
        if not leaves:
            raise MigrationError(f"destination prefix has no reviewed content: {prefix}")
        all_modules[base + ".All"] = leaves

    # A leaf may safely import another generated All only when explicitly reviewed.
    generated_graph = {**graph, **{module: {x for x in imports if x in all_modules} for module, imports in all_modules.items()}}
    cycle = topological_cycle(generated_graph)
    if cycle:
        raise MigrationError("generated umbrella cycle: " + " -> ".join(cycle))

    # Delivery declaration routes cover all 73 owners / all 4,195 declarations.
    route_lines = [
        "format\t1",
        "declaration\thistorical_module\tdestination_module\tdecision\tkind\tvisibility\tcommand_root\tstart_line",
    ]
    for name in sorted(declarations):
        declaration = declarations[name]
        command = command_for_declaration.get(name)
        if command is None:
            destination = declaration.module
            decision = "canonical_in_place"
            root_name = "-"
            start_line = "-"
        else:
            destination = final_owner[name]
            decision = command.decision
            root_name = command.root
            start_line = str(command.start_line)
        route_lines.append("\t".join((
            name, declaration.module, destination, decision, declaration.kind,
            declaration.visibility, root_name, start_line,
        )))

    # Classification ledger comes from the immutable phase scope.
    scope_rows: dict[str, list[str]] = {}
    with scope_path.open(encoding="utf-8", newline="") as stream:
        reader = csv.reader(stream, delimiter="\t")
        header = next(reader)
        columns = {name: index for index, name in enumerate(header)}
        for row in reader:
            if row[columns["wave_id"]] == "W02":
                scope_rows[row[columns["module"]]] = row
    selector: list[tuple[str, str]] = []
    with selector_path.open(encoding="utf-8", newline="") as stream:
        reader = csv.reader(stream, delimiter="\t")
        next(reader)
        selector.extend((row[0], row[1]) for row in reader)
    if len(selector) != 73 or set(scope_rows) != {module for module, _ in selector}:
        raise MigrationError("W02 selector/scope does not contain exactly 73 owners")
    class_lines = ["module\tpath\tplanned_action\toutcome\trationale"]
    for module, path in selector:
        row = scope_rows[module]
        action = row[columns["planned_actions"]]
        outcome = "split_with_compatibility" if module in PHYSICAL_SET else "canonical_in_place"
        class_lines.append("\t".join((module, path, action, outcome, row[columns["rationale"]])))

    test_rows = ["kind\timport_module\ttest_path\trepresentatives"]
    test_payloads: dict[Path, str] = {}
    for module in sorted(route_modules):
        public = []
        for command in route_commands.get(module, ()):
            public.extend(
                name for name in command.declarations
                if declarations[name].visibility == "public" and not name.startswith("_private.")
            )
        if not public:
            continue
        representative = sorted(public)[0]
        relative = Path("NumStabilityTest/Reorganization/W02/Canonical") / (module.replace(".", "_") + ".lean")
        payload = f"import {module}\n\n#check {representative}\n"
        test_payloads[relative] = payload
        test_rows.append(f"canonical\t{module}\t{relative.as_posix()}\t{representative}")
    for owner in PHYSICAL:
        representatives: list[str] = []
        by_route: dict[str, list[str]] = defaultdict(list)
        for command in owner_commands[owner]:
            route = owner if command.decision == "retain_historical" else intended[(command.owner, command.root)]
            by_route[route].extend(
                name for name in command.declarations
                if declarations[name].visibility == "public" and not name.startswith("_private.")
            )
        for route in sorted(by_route):
            if by_route[route]:
                representatives.append(sorted(by_route[route])[0])
        relative = Path("NumStabilityTest/Reorganization/W02/Compatibility") / (owner.replace(".", "_") + ".lean")
        payload = f"import {owner}\n\n" + "".join(f"#check {name}\n" for name in representatives)
        test_payloads[relative] = payload
        test_rows.append(f"compatibility\t{owner}\t{relative.as_posix()}\t{','.join(representatives)}")

    if not args.write:
        print(json.dumps({
            "commands": len(commands), "retained": EXPECTED_RETAINED,
            "route_modules": len(route_modules), "all_modules": len(all_modules),
            "tests": len(test_payloads), "declarations": len(declarations),
        }, indent=2))
        return 0

    frozen_sources: dict[str, str] = {}
    for owner, relative in source_paths.items():
        payload = git(root, "show", f"{BASE}:{relative}", binary=True)
        assert isinstance(payload, bytes)
        frozen_sources[owner] = payload.decode("utf-8")

    # Write declaration-bearing semantic leaves.
    for module in sorted(route_modules):
        owned = route_commands.get(module, [])
        if owned:
            historical_owner = owned[0].owner
            keep = {command.root for command in owned}
            payload = render_subset(
                frozen_sources[historical_owner], owner_commands[historical_owner],
                keep, dependencies[module],
            )
        else:
            payload = lean_doc(module.removeprefix("NumStability."), dependencies[module])
        safe_write(root, module_path(module), payload, allowed_writes)

    for module, imports in sorted(all_modules.items()):
        payload = lean_doc(module.removeprefix("NumStability."), imports)
        safe_write(root, module_path(module), payload, allowed_writes)

    # Historical modules are import-only unless their genuine-private closure
    # must retain exact source identity.
    for owner in PHYSICAL:
        retained_roots = {
            command.root for command in owner_commands[owner]
            if command.decision == "retain_historical"
        }
        moved_modules = {intended[(command.owner, command.root)] for command in owner_commands[owner] if command.decision == "move_candidate"}
        if retained_roots:
            # Retained commands still live in the historical module and may
            # use declarations from earlier historical owners (for example,
            # the rectangular Chapter 7 closure uses `signInd` from the main
            # Chapter 7 facade).  Preserve that original acyclic import DAG.
            # Only newly generated leaves are forbidden from importing a
            # physical compatibility owner.
            imports = direct_imports(root, owner)
            imports.update(moved_modules)
            payload = render_subset(
                frozen_sources[owner], owner_commands[owner], retained_roots, imports,
            )
        else:
            payload = lean_doc(
                owner.removeprefix("NumStability.") + " compatibility facade",
                moved_modules,
            )
        safe_write(root, Path(source_paths[owner]), payload, allowed_writes)

    for relative, payload in sorted(test_payloads.items()):
        safe_write(root, relative, payload, allowed_writes)
    safe_write(root, Path("docs/architecture/deliveries/W02/DECLARATION_ROUTES.tsv"), "\n".join(route_lines) + "\n", allowed_writes)
    safe_write(root, Path("docs/architecture/deliveries/W02/CLASSIFICATION.tsv"), "\n".join(class_lines) + "\n", allowed_writes)
    safe_write(root, Path("docs/architecture/deliveries/W02/TEST_MATRIX.tsv"), "\n".join(test_rows) + "\n", allowed_writes)
    print(f"wrote {len(route_modules)} leaves, {len(all_modules)} entry points, {len(test_payloads)} tests")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MigrationError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
