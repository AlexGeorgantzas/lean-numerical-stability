#!/usr/bin/env python3
"""Generate and check the frozen Analysis.Norms Phase 11B1 ownership map."""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path


CORE = "NumStability.Analysis.Norms.Core"
ANALYSIS = "NumStability.Analysis."

V_BASIC = ANALYSIS + "VectorNorms.Basic"
V_INTERP = ANALYSIS + "VectorNorms.Interpolation"
V_DUAL = ANALYSIS + "VectorNorms.Duality"
V_ATTAIN = ANALYSIS + "VectorNorms.Attainment"
L_BASIC = ANALYSIS + "LinearOperators.Basic"
L_TRIANGULAR = ANALYSIS + "LinearOperators.Triangularization"
O_BASIC = ANALYSIS + "OperatorNorms.Basic"
O_ATTAIN = ANALYSIS + "OperatorNorms.Attainment"
M_BASIC = ANALYSIS + "MatrixNorms.Basic"
M_SPECTRAL = ANALYSIS + "MatrixNorms.SpectralRadius"
M_LP = ANALYSIS + "MatrixNorms.Lp"
SV_BASIC = ANALYSIS + "SingularValues.Basic"
SV_REAL = ANALYSIS + "SingularValues.Realification"
M_COMPARE = ANALYSIS + "MatrixNorms.Comparisons"
M_UNITARY = ANALYSIS + "MatrixNorms.UnitarilyInvariant"
M_HADAMARD = ANALYSIS + "MatrixNorms.Hadamard"
M_ATTAIN = ANALYSIS + "MatrixNorms.Attainment"
C_DISTANCE = ANALYSIS + "Conditioning.DistanceToSingularity"
C_INVERSE = ANALYSIS + "Conditioning.InversePerturbation"
A_BOUNDS = ANALYSIS + "Asymptotics.Bounds"
P01 = "NumStability.Source.Higham.Chapter06.Problem01"
P05 = "NumStability.Source.Higham.Chapter06.Problem05"
P09 = "NumStability.Source.Higham.Chapter06.Problem09"
P10 = "NumStability.Source.Higham.Chapter06.Problem10"

OWNERS = (
    V_BASIC,
    V_INTERP,
    V_DUAL,
    V_ATTAIN,
    L_BASIC,
    L_TRIANGULAR,
    O_BASIC,
    O_ATTAIN,
    M_BASIC,
    M_SPECTRAL,
    M_LP,
    SV_BASIC,
    SV_REAL,
    M_COMPARE,
    M_UNITARY,
    M_HADAMARD,
    M_ATTAIN,
    C_DISTANCE,
    C_INVERSE,
    A_BOUNDS,
    P01,
    P05,
    P09,
    P10,
)
SOURCE_OWNERS = {P01, P05, P09, P10}
REUSABLE_OWNERS = set(OWNERS) - SOURCE_OWNERS

STRUCTURAL_OWNERS = {
    "NumStability.Analysis.VectorNorms",
    "NumStability.Analysis.Asymptotics",
    "NumStability.Analysis.LinearOperators",
    "NumStability.Analysis.OperatorNorms",
    "NumStability.Analysis.MatrixNorms",
    "NumStability.Analysis.SingularValues",
    "NumStability.Analysis.Conditioning",
    CORE,
    "NumStability.Analysis.Norms",
    "NumStability.Source.Higham.Chapter06.Norms",
    "NumStability.Source.Higham.Chapter06",
}

FOUNDATION_IMPORTS = {"NumStability.Analysis.MatrixAlgebra"}
ALLOWED_EXTERNAL_IMPORTS = {
    "Mathlib.Analysis.Complex.Basic",
    "Mathlib.Analysis.Complex.Hadamard",
    "Mathlib.Analysis.Complex.Polynomial.Basic",
    "Mathlib.Analysis.Calculus.DiffContOnCl",
    "Mathlib.Analysis.CStarAlgebra.Matrix",
    "Mathlib.Analysis.InnerProductSpace.Positive",
    "Mathlib.Analysis.InnerProductSpace.Trace",
    "Mathlib.Analysis.Matrix.PosDef",
    "Mathlib.Analysis.MeanInequalitiesPow",
    "Mathlib.Analysis.Normed.Lp.PiLp",
    "Mathlib.Analysis.Normed.Module.FiniteDimension",
    "Mathlib.Analysis.Normed.Module.HahnBanach",
    "Mathlib.Analysis.Normed.Operator.NNNorm",
    "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
    "Mathlib.Algebra.BigOperators.Group.Finset.Basic",
    "Mathlib.Algebra.Field.GeomSum",
    "Mathlib.Algebra.Group.TransferInstance",
    "Mathlib.Algebra.Module.TransferInstance",
    "Mathlib.Data.Fintype.BigOperators",
    "Mathlib.Data.Fin.Tuple.Basic",
    "Mathlib.LinearAlgebra.Basis.Flag",
    "Mathlib.LinearAlgebra.Dimension.Constructions",
    "Mathlib.LinearAlgebra.Eigenspace.Matrix",
    "Mathlib.LinearAlgebra.Eigenspace.Triangularizable",
    "Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs",
    "Mathlib.LinearAlgebra.Matrix.Rank",
    "Mathlib.RingTheory.RootsOfUnity.Complex",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.Ring",
    "Mathlib.Topology.MetricSpace.ProperSpace",
    "Mathlib.Topology.Order.Compact",
}
ALLOWED_OWNER_IMPORTS = {
    V_BASIC: set(),
    V_INTERP: {V_BASIC},
    V_DUAL: {V_BASIC},
    V_ATTAIN: {V_BASIC},
    L_BASIC: {V_BASIC},
    L_TRIANGULAR: set(),
    O_BASIC: {L_BASIC},
    O_ATTAIN: {O_BASIC, V_DUAL},
    M_BASIC: {O_BASIC, V_DUAL, V_INTERP},
    M_SPECTRAL: {M_BASIC, L_TRIANGULAR},
    M_LP: {M_BASIC},
    SV_BASIC: {M_BASIC},
    SV_REAL: {SV_BASIC},
    M_COMPARE: {M_LP, SV_REAL},
    M_UNITARY: {SV_BASIC},
    M_HADAMARD: {M_COMPARE},
    M_ATTAIN: {M_COMPARE, O_ATTAIN, V_ATTAIN},
    C_DISTANCE: {M_ATTAIN},
    C_INVERSE: {A_BOUNDS, C_DISTANCE},
    A_BOUNDS: set(),
    P01: {M_HADAMARD},
    P05: {M_UNITARY},
    P09: {SV_BASIC},
    P10: {SV_BASIC},
}

CORE_SHA256 = "534C3D858667B5DD7D1461DC35148FCC4C92219E6B10DBA271799C12E962ACA2"
BASELINE_TSV_SHA256 = (
    "7FFBDD7F54F4DD19C0FCD5962D41A01A09ED55F6E251DB7F4240B42D340E6A09"
)
EXPECTED_MANIFEST_ROWS = 1_783
EXPECTED_MANIFEST_BYTES = 218_032
EXPECTED_MANIFEST_SHA256 = (
    "8CDC351C6BC9CE9952318B4E154B034E0F3713E1F9BDAB7DD52EECD5FA8F3E23"
)
EXPECTED_MANIFEST_FILE_BYTES = 218_041
EXPECTED_MANIFEST_FILE_SHA256 = (
    "5C1E9E020FE6D7665EAF8E92314C60AA0F8300EAE0A520C2C34D18AEC315E99A"
)

EXPECTED_INCIDENT_EDGES = 18_895
EXPECTED_SIGNATURE_INCIDENT_EDGES = 7_403
EXPECTED_BODY_INCIDENT_EDGES = 11_492
EXPECTED_INCIDENT_EDGE_BYTES = 2_266_462
EXPECTED_INCIDENT_EDGE_SHA256 = (
    "0C10D731ED3654D863518B70D6BB4842E3BAE6824CBEC6E848AAA27DC0FE1DD3"
)
EXPECTED_INTERNAL_EDGES = 12_625
EXPECTED_INTERNAL_EDGE_BYTES = 1_436_975
EXPECTED_INTERNAL_EDGE_SHA256 = (
    "542908FA07DB01630D126EFB3812D04783DF5524D82988DC1FA3D46179CC8B7A"
)

EXPECTED_COUNTS = {
    V_BASIC: (199, 147, 52, 0),
    V_INTERP: (103, 97, 6, 0),
    V_DUAL: (58, 41, 17, 0),
    V_ATTAIN: (7, 7, 0, 0),
    L_BASIC: (31, 24, 7, 0),
    L_TRIANGULAR: (13, 8, 5, 0),
    O_BASIC: (28, 21, 7, 0),
    O_ATTAIN: (57, 33, 24, 0),
    M_BASIC: (109, 91, 18, 0),
    M_SPECTRAL: (31, 24, 7, 0),
    M_LP: (208, 129, 79, 0),
    SV_BASIC: (232, 186, 45, 1),
    SV_REAL: (38, 33, 5, 0),
    M_COMPARE: (152, 142, 10, 0),
    M_UNITARY: (69, 60, 9, 0),
    M_HADAMARD: (53, 44, 9, 0),
    M_ATTAIN: (67, 55, 12, 0),
    C_DISTANCE: (52, 31, 21, 0),
    C_INVERSE: (114, 78, 36, 0),
    A_BOUNDS: (3, 3, 0, 0),
    P01: (79, 75, 4, 0),
    P05: (30, 27, 3, 0),
    P09: (1, 1, 0, 0),
    P10: (49, 28, 18, 3),
}

EXPECTED_OWNER_SHA256 = {
    V_BASIC: "F8D42B0523541B61F7EF55591E898C1305C4C97BBF6AE036F149C989F3E626A0",
    V_INTERP: "3422D162DDA4C42CC3AF98C5ADFC3D5DB0E5A5B9330C2696F94E766A658BEC2B",
    V_DUAL: "E26A7B7EBC315AC56ECD64B937163844F994DCBF091A121C7814D934185F56DF",
    V_ATTAIN: "C6C62D07B4EEB4759F31FA50E4E07D09A34CD8EEA53ADCB6E3B7245207946687",
    L_BASIC: "8223B6637B07663D66584FA0B569368D1BC8BF0A226C66814754E1750857D241",
    L_TRIANGULAR: "EE9B006D9121C6C7EEBB91249000819E87FEBBF70CDCCAD60B18D296A476D075",
    O_BASIC: "11C3D135285F672BE7BF58CAF5C02923DB91F120E2D7C48108B120287B3722A2",
    O_ATTAIN: "E0B1C2C852477B7701EF09A2DCC95A559CF94E7526574AE6A6EC8FF11A5C06B5",
    M_BASIC: "8A71588D90A86B9F3A7A93ED4B1969CA9A5411F5F8FB76166E912C6666EE9197",
    M_SPECTRAL: "8DDB828C027DC1CFFC37FDD602FF5C8D00B296A5D9CEBB2C0A28BCBB6651F632",
    M_LP: "3BC27DFA936D06B50DCB53FF9DC1E6695E233349355FB6D242152F0765845F01",
    SV_BASIC: "9879AEF5B45FE85DA19966F2BB5612CB9B32103E9AD6992149E247FCA0B26717",
    SV_REAL: "92BD2285A780DE39CFDA728770CC72B00C843DA7B3C5742B164680A10B4C9D3F",
    M_COMPARE: "A7397D9A9FADF1571E5A21DB272C253E16D7229A525E60F021D87851F296CB64",
    M_UNITARY: "B0883F2A6EE9254AE66BAAA521488F0329919E42CA664C9B9FF03629D0DDCF6C",
    M_HADAMARD: "1C0BF2C01E7DFB4EE61984A1A0F31BBC5DAD2E84F8B9128F980AB1E8AB117DDB",
    M_ATTAIN: "9573A70437ABEF112210A812DA67AFA6AED83EE3B5DCBC99842FE61122E6B9DB",
    C_DISTANCE: "8B682F0D3AB2C8E56D4E55F67F5B1D7CE3FB67C4B7C9B746A6CF8470D0DA1E64",
    C_INVERSE: "07AE2C2D098420D772AFC89B2D771B29AD503FEA5410519848921C5263E8FEAA",
    A_BOUNDS: "BD99CC7DD9B414DA010B1D059EF765321A00A4B0514BE8DDF2CAA743C6E51E5E",
    P01: "8E34E2E61B3E1E99DA4A05500CE612E243E46E117C8E7D9089446A3A0F9FDE1A",
    P05: "145C2F094EE29060209F61F9B9979240AAB292CC2F6C2AD145B13C780A8C784D",
    P09: "F403422C573E4308AE71B43A09468C845E8B1943D2E38F0854C435FCFF00E153",
    P10: "E5B79F5D9245FE81616FE6AEA07BA0CBC26F9E1D3E307B3BD11092BC37E0BA65",
}

DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(def|theorem|lemma|abbrev|opaque|axiom|inductive|structure|class|instance)"
    r"\b(?:\s+([^\s:{(\[]+))?"
)

P05_EXTRA_ROOTS = {
    "NumStability.complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_of_perm",
    "NumStability.complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_basisPerm",
    "NumStability.ComplexMatrixFixedUnitaryInvariantNorm.toOperatorIdealNormOfSVD",
}

SV_EXTRA_ROOTS = {
    "NumStability.ComplexSquareContractionMidpointProperty",
    "NumStability.complexMatrixSingularValue_ne_zero_of_rank_eq_card",
}

UNITARY_PREFIXES = (
    "NumStability.ComplexMatrixFixedUnitaryInvariantNorm",
    "NumStability.ComplexMatrixFixedOperatorIdealNorm",
    "NumStability.ComplexMatrixOperatorIdealNormFamily",
    "NumStability.complexFrobeniusFixedOperatorIdealNorm",
    "NumStability.complexFrobeniusOperatorIdealNormFamily",
)

HADAMARD_PREFIXES = (
    "NumStability.IsRealHadamardMatrix",
    "NumStability.realHadamardScaled",
    "NumStability.IsComplexHadamardMatrix",
    "NumStability.IsScalarMultipleComplexHadamardMatrix",
    "NumStability.complexFourierVandermonde",
    "NumStability.complexMatrixNormalizeByReal_isComplexHadamard",
    "NumStability.complexMatrixFullRankS2Equality_isScalarMultipleComplexHadamard",
)

LINEAR_OPERATOR_ROOTS = {
    "NumStability.ComplexVectorMap",
    "NumStability.IsComplexVectorMapLinear",
    "NumStability.complexVectorMapComp",
    "NumStability.complexVectorMapAdd",
    "NumStability.complexVectorMapSMul",
    "NumStability.complexVectorMapNeg",
    "NumStability.complexVectorMapSub",
    "NumStability.IsSingularComplexVectorMap",
    "NumStability.complexVectorMapComp_linear",
    "NumStability.complexVectorMapAdd_linear",
    "NumStability.complexVectorMapSMul_linear",
    "NumStability.complexVectorMapNeg_linear",
    "NumStability.complexVectorMapSub_linear",
    "NumStability.IsComplexVectorMapLinear.map_zero",
    "NumStability.complexVectorMapLinearMap",
    "NumStability.complexVectorMapLinearMap_apply",
    "NumStability.complexVectorNorm_pullback_of_linear_injective",
}

LINEAR_OPERATOR_TRIANGULARIZATION_ROOTS = {
    "NumStability.basisUpperTriangularizes",
    "NumStability.basisUpperTriangularizes_blockTriangular_toMatrix",
    "NumStability.sumQuotFinBasis",
    "NumStability.sumQuotFinBasis_blockTriangular_toMatrix",
    "NumStability.eigenvector_span_le_comap",
    "NumStability.finOne_blockTriangular",
    "NumStability.blockTriangular_reindex_finCongr",
    "NumStability.exists_blockTriangular_toMatrix_of_finrank",
}

OPERATOR_NORM_BASIC_ROOTS = {
    "NumStability.MixedSubordinateBound",
    "NumStability.IsMixedSubordinateNormValue",
    "NumStability.mixedSubordinateBound_nonneg_of_nonempty",
    "NumStability.mixedSubordinateNormValue_nonneg_of_nonempty",
    "NumStability.ComplexVectorMapEigenvalueModulusSet",
    "NumStability.IsMaxComplexVectorMapEigenvalueModulus",
    "NumStability.eigenvalueModulus_le_mixedSubordinateNormValue",
    "NumStability.maxEigenvalueModulus_le_mixedSubordinateNormValue",
    "NumStability.mixedSubordinateBound_add",
    "NumStability.mixedSubordinateBound_smul",
    "NumStability.mixedSubordinateBound_neg",
    "NumStability.mixedSubordinateBound_sub",
    "NumStability.mixedSubordinateBound_comp",
    "NumStability.mixedSubordinateNormValue_add_le",
    "NumStability.mixedSubordinateNormValue_smul_le",
    "NumStability.mixedSubordinateNormValue_sub_le",
    "NumStability.mixedSubordinateNormValue_comp_le",
    "NumStability.mixedSubordinateNormValue_right_le_add_of_add_eq",
    "NumStability.mixedSubordinateNormValue_left_le_add_of_add_eq",
    "NumStability.mixedSubordinateNormValue_smul_real_pos",
    "NumStability.exists_mixedSubordinateNormValue_of_bound_nonempty",
}

OPERATOR_NORM_ATTAINMENT_ROOTS = {
    "NumStability.MixedUnitImageNormSet",
    "NumStability.IsMaxMixedUnitImageNormValue",
    "NumStability.MixedNonzeroImageRatioSet",
    "NumStability.IsMaxMixedNonzeroImageRatioValue",
    "NumStability.IsMinMixedNonzeroImageRatioValue",
    "NumStability.MixedDualUnitPairingRealSet",
    "NumStability.IsMaxMixedDualUnitPairingRealValue",
    "NumStability.isMixedSubordinateNormValue_of_isMaxMixedUnitImageNormValue",
    "NumStability.isMaxMixedNonzeroImageRatioValue_of_isMaxMixedUnitImageNormValue",
    "NumStability.isMaxMixedUnitImageNormValue_of_isMaxMixedNonzeroImageRatioValue",
    "NumStability.isMaxMixedNonzeroImageRatioValue_iff_unitImageNormValue",
    "NumStability.exists_unit_vector_attaining_mixedSubordinateNormValue",
    "NumStability.dualFunctionalAsVectorMap",
    "NumStability.dualFunctionalAsVectorMap_linear",
    "NumStability.complexVecOneNorm_dualFunctionalAsVectorMap_apply",
    "NumStability.dualFunctional_as_mixedSubordinateNormValue",
    "NumStability.isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_pos",
    "NumStability.isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_zero",
    "NumStability.isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue",
    "NumStability.isMaxDualNonzeroFunctionalRatioValue_of_dualFunctionalNormValue",
    "NumStability.isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue",
    "NumStability.isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue_nonempty",
    "NumStability.isMinMixedNonzeroImageRatioValue_inv_of_inverseNormValue",
    "NumStability.isMaxMixedDualUnitPairingRealValue_of_mixedSubordinateNormValue_nonempty",
    "NumStability.rankOneOperator",
    "NumStability.rankOneOperator_linear",
    "NumStability.rankOneOperator_apply_norm",
    "NumStability.rankOneOperator_isMixedSubordinateNormValue_of_dualFunctionalNormValue",
    "NumStability.rankOneOperator_apply_of_norming_value",
    "NumStability.mixedSubordinateNormValue_one_of_bound_attained",
    "NumStability.rankOne_isMixedSubordinateNormValue_one_of_normingFunctional",
    "NumStability.exists_rankOne_isMixedSubordinateNormValue_one",
    "NumStability.exists_unit_vector_norm_apply_eq_opNorm_finiteDimensional",
}

MATRIX_NORM_COMPARISON_EXTRA_ROOTS = {
    "NumStability.complexMatrixOneNorm_hasComplexMatrixLpBound",
    "NumStability.complexMatrixInfNorm_hasComplexMatrixLpBound",
    "NumStability.complexMatrixLpNormOfReal_rieszThorin_one_two_of_gt_one",
    "NumStability.complexMatrixLpNormOfReal_rieszThorin_one_two",
}

MATRIX_NORM_SPECTRAL_RADIUS_ROOTS = {
    "NumStability.exists_complexMatrixVecMul_blockTriangular_toMatrix",
    "NumStability.ComplexMatrixEigenvalueModulusSet",
    "NumStability.IsMaxComplexMatrixEigenvalueModulus",
    "NumStability.complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet",
    "NumStability.toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest",
    "NumStability.toLin_spectralRadius_toReal_eq_of_spectrum_modulusSet_isGreatest",
    "NumStability.complexMatrix_toLin_spectralRadius_eq_of_isMaxComplexMatrixEigenvalueModulus",
    "NumStability.complexMatrixEigenvalueModulusSet_coordinateMatrix_subset",
    "NumStability.upperTriangular_diagonal_mem_complexMatrixEigenvalueModulusSet",
    "NumStability.upperTriangular_diagonal_norm_le_maxComplexMatrixEigenvalueModulus",
    "NumStability.complexMatrixEigenvalueModulus_le_mixedSubordinateMatrixNormValue",
    "NumStability.maxComplexMatrixEigenvalueModulus_le_mixedSubordinateMatrixNormValue",
    "NumStability.geomWeight_later_le",
    "NumStability.complexVecWeightedInfNorm_matrix_bound_of_weighted_rows",
    "NumStability.complexMatrixStrictUpperMass",
    "NumStability.complexMatrixStrictUpperMass_nonneg",
    "NumStability.complexMatrixStrictUpperRowSum_le_mass",
    "NumStability.spectralRadiusScale_pos_le_one",
    "NumStability.spectralRadiusScale_mul_mass_le_delta",
    "NumStability.complexMatrixUpperTriangular_weighted_row_bound",
    "NumStability.complexMatrixUpperTriangular_weighted_subordinate_bound_of_delta",
    "NumStability.exists_mixedSubordinateMatrixNormValue_le_of_upperTriangular_similarity",
    "NumStability.exists_mixedSubordinateMatrixNormValue_le_of_maxComplexMatrixEigenvalueModulus",
    "NumStability.exists_mixedSubordinateMatrixNormValue_lt_one_of_maxComplexMatrixEigenvalueModulus_lt_one",
}

MATRIX_NORM_BASIC_EXTRA_ROOTS = {
    "NumStability.mixedSubordinateMatrixBound_pullback",
    "NumStability.mixedSubordinateMatrixNormValue_nonneg_of_nonempty",
    "NumStability.exists_mixedSubordinateMatrixNormValue_of_bound_nonempty",
}

MATRIX_NORM_ATTAINMENT_EXTRA_ROOTS = {
    "NumStability.RealImagMatrixUnitNormSet",
    "NumStability.IsMaxRealImagMatrixNormValue",
    "NumStability.complexMatrixRealImagOneNorm_isMaxRealImagMatrixNormValue",
    "NumStability.ComplexMatrixInfOneQuadraticUnitSet",
    "NumStability.IsMaxComplexMatrixInfOneQuadraticUnitValue",
    "NumStability.complexMatrix_oneNorm_mulVec_le_quadratic_max_of_unit",
    "NumStability.complexMatrix_infOneNormValue_eq_quadraticUnitMax_of_posSemidef",
    "NumStability.complexMatrix_infOneNormValue_eq_quadraticUnitMax_of_posDef",
}

ASYMPTOTIC_BOUND_ROOTS = {
    "NumStability.tendsto_of_eventually_abs_sub_le_tendsto_zero",
    "NumStability.tendsto_of_eventually_between_tendsto",
    "NumStability.tendsto_const_mul_of_tendsto_zero_of_eventually_abs_le",
}

VECTOR_NORM_DUALITY_EXTRA_ROOTS = {
    "NumStability.IsComplexLinearForm",
    "NumStability.IsComplexLinearForm.map_zero",
    "NumStability.IsComplexLinearForm.apply_sum",
    "NumStability.IsComplexLinearForm.apply_eq_sum_basis",
}

HADAMARD_EXACT_ROOTS = {
    "NumStability.real_sqrt_nat_inv_sq_mul_self",
    "NumStability.real_rpow_abs_inv_sub_half_mul_sqrt_eq_left",
    "NumStability.real_rpow_abs_inv_sub_half_mul_sqrt_eq_right",
    "NumStability.complexMatrixNormalizeByReal",
    "NumStability.complexMatrixFrobeniusSq_eq_card_mul_flatEntryNorm_scale_sq",
    "NumStability.complexMatrixFullRankS2Equality_flatEntryScale_pos_and_op2_sq_eq",
    "NumStability.complex_fin_geometric_sum_eq_zero",
    "NumStability.complex_star_eq_inv_of_norm_eq_one",
    "NumStability.complex_star_pow_mul_pow_eq_one_of_isPrimitiveRoot",
    "NumStability.complex_pow_mul_order_of_isPrimitiveRoot",
}

MANUAL_SV_LOGICAL_NAMES = {
    "Function.Embedding.toEquivRange.eq_1",
    "basisOfOrthonormalOfCardEqFinrank.congr_simp",
    "_private.<module>.NumStability.complex_re_star_mul_ofReal_mul",
}

MANUAL_P10_LOGICAL_NAMES = {
    "_private.<module>.NumStability.complexTwoBlockBuild.match_1.eq_1",
    "_private.<module>.NumStability.complexTwoBlockBuild.match_1.eq_2",
    "_private.<module>.NumStability.complexTwoBlockBuild.match_1.splitter",
}

EXPECTED_MANUAL_NAMES = MANUAL_SV_LOGICAL_NAMES | MANUAL_P10_LOGICAL_NAMES


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str
    visibility: str


@dataclass(frozen=True)
class ManifestRow:
    logical_name: str
    expected_module: str
    kind: str
    visibility: str


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Remove nested block comments and line comments from the frozen source."""
    result: list[str] = []
    depth = 0
    for source_line in lines:
        output: list[str] = []
        index = 0
        while index < len(source_line):
            if depth:
                if source_line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source_line.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            else:
                if source_line.startswith("--", index):
                    break
                if source_line.startswith("/-", index):
                    depth = 1
                    index += 2
                else:
                    output.append(source_line[index])
                    index += 1
        result.append("".join(output))
    if depth != 0:
        raise ValueError("unterminated Lean block comment")
    return result


def source_roots(source: Path) -> list[tuple[int, str]]:
    clean = strip_lean_comments(source.read_text(encoding="utf-8").splitlines())
    namespaces: list[str] = []
    roots: list[tuple[int, str]] = []

    for line_number, line in enumerate(clean, 1):
        match = re.match(r"^\s*namespace\s+(\S+)", line)
        if match:
            namespaces.append(match.group(1))
            continue

        if re.match(r"^\s*end(?:\s+\S+)?\s*$", line):
            if namespaces:
                namespaces.pop()
            continue

        match = DECL_RE.match(line)
        if not match:
            continue
        name = match.group(2)
        if not name or name == ":":
            continue

        qualified = name if name.startswith("NumStability.") else ".".join(namespaces + [name])
        roots.append((line_number, qualified))

    if len(roots) != 1_182:
        raise ValueError(f"expected 1182 named source commands, found {len(roots)}")
    return roots


def owner_for_root(line: int, name: str) -> str:
    if 125 <= line <= 486:
        return V_INTERP

    if line == 2391 or 2610 <= line <= 2687:
        return V_BASIC

    if name in LINEAR_OPERATOR_ROOTS:
        return L_BASIC

    if name in LINEAR_OPERATOR_TRIANGULARIZATION_ROOTS:
        return L_TRIANGULAR

    if name in OPERATOR_NORM_BASIC_ROOTS:
        return O_BASIC

    if name in OPERATOR_NORM_ATTAINMENT_ROOTS:
        return O_ATTAIN

    if name in MATRIX_NORM_COMPARISON_EXTRA_ROOTS:
        return M_COMPARE

    if name in MATRIX_NORM_SPECTRAL_RADIUS_ROOTS:
        return M_SPECTRAL

    if name in MATRIX_NORM_BASIC_EXTRA_ROOTS:
        return M_BASIC

    if name in MATRIX_NORM_ATTAINMENT_EXTRA_ROOTS:
        return M_ATTAIN

    if name in ASYMPTOTIC_BOUND_ROOTS:
        return A_BOUNDS

    if name in VECTOR_NORM_DUALITY_EXTRA_ROOTS:
        return V_DUAL

    if name in {
        "NumStability.IsComplexVectorNorm.sum_le",
        "NumStability.complexVecSupport_mul_left_card_le",
        "NumStability.complexVecSupport_mul_left_subset",
        "NumStability.complexVecInfNorm_conj_eq",
        "NumStability.complexVecConjInfNorm_mul_oneNorm_pairing_le",
        "NumStability.complexVecWeightedInfNorm",
        "NumStability.complexVecWeightedInfNorm_coord_le",
        "NumStability.complexVecWeightedInfNorm_isComplexVectorNorm",
        "NumStability.complexVecNormSqSum_const_one",
        "NumStability.complexVecNormSqSum_standardBasisCVec",
        "NumStability.complexVecOneNorm_const_one",
    }:
        return V_BASIC

    if name == "NumStability.complexVecLpNorm_le_of_rowFunctional_bound":
        return V_INTERP

    if name == "NumStability.exists_unit_infNorm_pairing_oneNorm":
        return V_DUAL

    if name in {
        "NumStability.VectorNormRatioSet",
        "NumStability.IsMaxVectorNormRatioValue",
        "NumStability.isMaxVectorNormRatioValue_nonneg",
        "NumStability.isMaxVectorNormRatioValue_pos",
        "NumStability.vectorNorm_le_mul_of_isMaxVectorNormRatioValue",
        "NumStability.complexVecLpNorm_ratio_max_one_of_exponent_le",
        "NumStability.complexVecLpNorm_ratio_max_card_rpow_of_exponent_le",
    }:
        return V_ATTAIN

    for start, end, owner in (
        (56, 1803, V_BASIC),
        (1804, 2390, V_INTERP),
        (2391, 2830, V_DUAL),
        (2831, 5126, M_BASIC),
        (5127, 9594, M_LP),
    ):
        if start <= line <= end:
            return owner

    if 9595 <= line <= 12124:
        return SV_BASIC

    for start, end, owner in (
        (18434, 20207, M_ATTAIN),
        (20208, 20876, C_DISTANCE),
        (20877, 23630, C_INVERSE),
    ):
        if start <= line <= end:
            return owner

    if name.startswith("NumStability.HighamProblem61") or name.startswith(
        "NumStability.highamProblem61_"
    ):
        return P01

    if name.startswith("NumStability.highamProblem69"):
        return P09

    if 14521 <= line <= 14910:
        return P10

    if name.startswith("NumStability.highamProblem65") or name in P05_EXTRA_ROOTS:
        return P05

    if name in SV_EXTRA_ROOTS:
        return SV_BASIC

    if (
        15393 <= line <= 15479
        or 16112 <= line <= 16458
        or name
        in {
            "NumStability.complexNorm_ofReal_eq_abs",
            "NumStability.opNorm2Le_to_rectOpNorm2Le",
        }
    ):
        return SV_REAL

    if name in HADAMARD_EXACT_ROOTS or name.startswith(HADAMARD_PREFIXES):
        return M_HADAMARD

    if (
        name.startswith(UNITARY_PREFIXES)
        and name
        != "NumStability.ComplexMatrixFixedUnitaryInvariantNorm.toOperatorIdealNormOfSVD"
    ):
        return M_UNITARY

    return M_COMPARE


def logical_name(name: str, actual_module: str) -> str:
    prefix = f"_private.{actual_module}."
    if not name.startswith(prefix):
        return name

    private_scope, separator, suffix = name[len(prefix) :].partition(".")
    if not separator or not private_scope.isdigit() or not suffix:
        raise ValueError(f"unexpected private name: {name}")
    return "_private.<module>." + suffix


def read_tsv(path: Path) -> tuple[list[Declaration], list[tuple[str, str, str]]]:
    declarations: list[Declaration] = []
    edges: list[tuple[str, str, str]] = []

    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if not row or row == ["format", "2"]:
                continue
            if row[0] == "declaration":
                if len(row) != 5:
                    raise ValueError(f"malformed declaration row: {row!r}")
                declarations.append(Declaration(*row[1:]))
            elif row[0] == "edge":
                if len(row) != 4:
                    raise ValueError(f"malformed edge row: {row!r}")
                edges.append((row[1], row[2], row[3]))
            else:
                raise ValueError(f"unexpected TSV row: {row!r}")

    return declarations, edges


def manifest_payload(records: dict[str, ManifestRow]) -> bytes:
    text = "".join(
        "\t".join((row.logical_name, row.expected_module, row.kind, row.visibility))
        + "\n"
        for _, row in sorted(records.items())
    )
    return text.encode("utf-8")


def validate_counts(records: dict[str, ManifestRow]) -> None:
    owner_set = set(OWNERS)
    for label, configured in (
        ("count", set(EXPECTED_COUNTS)),
        ("owner hash", set(EXPECTED_OWNER_SHA256)),
        ("import allowlist", set(ALLOWED_OWNER_IMPORTS)),
    ):
        if configured != owner_set:
            raise ValueError(
                f"{label} owner configuration mismatch: "
                f"{sorted(configured ^ owner_set)}"
            )

    by_owner: dict[str, Counter[str]] = defaultdict(Counter)
    for row in records.values():
        by_owner[row.expected_module]["total"] += 1
        by_owner[row.expected_module][row.visibility] += 1

    if set(by_owner) != set(OWNERS):
        raise ValueError(f"unexpected owner set: {sorted(set(by_owner) ^ set(OWNERS))}")

    for owner, expected in EXPECTED_COUNTS.items():
        actual = (
            by_owner[owner]["total"],
            by_owner[owner]["public"],
            by_owner[owner]["internal"],
            by_owner[owner]["private"],
        )
        if actual != expected:
            raise ValueError(f"{owner}: expected {expected}, got {actual}")

        owner_records = {
            name: row for name, row in records.items() if row.expected_module == owner
        }
        digest = sha256_bytes(manifest_payload(owner_records))
        if digest != EXPECTED_OWNER_SHA256[owner]:
            raise ValueError(f"{owner}: unexpected inventory hash {digest}")

    if sum(counter["total"] for counter in by_owner.values()) != EXPECTED_MANIFEST_ROWS:
        raise ValueError("manifest total does not equal 1783")


def validate_manifest_payload(records: dict[str, ManifestRow]) -> bytes:
    validate_counts(records)
    payload = manifest_payload(records)
    if len(records) != EXPECTED_MANIFEST_ROWS:
        raise ValueError(f"expected 1783 manifest rows, found {len(records)}")
    if len(payload) != EXPECTED_MANIFEST_BYTES:
        raise ValueError(f"expected {EXPECTED_MANIFEST_BYTES} payload bytes, found {len(payload)}")
    digest = sha256_bytes(payload)
    if digest != EXPECTED_MANIFEST_SHA256:
        raise ValueError(f"unexpected manifest payload hash {digest}")
    return payload


def generate_manifest(
    source: Path, dependency_tsv: Path
) -> tuple[
    dict[str, ManifestRow],
    dict[str, str],
    list[Declaration],
    list[tuple[str, str, str]],
]:
    if sha256_file(source) != CORE_SHA256:
        raise ValueError("Core source hash does not match the frozen Phase 11A input")
    if sha256_file(dependency_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("dependency TSV hash does not match the frozen Phase 11A input")

    roots = source_roots(source)
    root_owner = {name: owner_for_root(line, name) for line, name in roots}
    declarations, edges = read_tsv(dependency_tsv)
    core = [declaration for declaration in declarations if declaration.module == CORE]
    if len(core) != EXPECTED_MANIFEST_ROWS:
        raise ValueError(f"expected 1783 Core constants, found {len(core)}")

    records: dict[str, ManifestRow] = {}
    actual_to_logical: dict[str, str] = {}
    manually_assigned: set[str] = set()
    root_names = tuple(root_owner)

    for declaration in core:
        candidates = [
            root
            for root in root_names
            if declaration.name == root or declaration.name.startswith(root + ".")
        ]
        logical = logical_name(declaration.name, declaration.module)

        if candidates:
            expected = root_owner[max(candidates, key=len)]
        elif logical in MANUAL_SV_LOGICAL_NAMES:
            expected = SV_BASIC
            manually_assigned.add(logical)
        elif logical in MANUAL_P10_LOGICAL_NAMES:
            expected = P10
            manually_assigned.add(logical)
        else:
            raise ValueError(f"unassigned compiled constant: {declaration.name}")

        if logical in records:
            raise ValueError(f"duplicate logical name: {logical}")
        records[logical] = ManifestRow(
            logical, expected, declaration.kind, declaration.visibility
        )
        actual_to_logical[declaration.name] = logical

    if manually_assigned != EXPECTED_MANUAL_NAMES:
        raise ValueError(
            f"manual-name mismatch: {sorted(manually_assigned ^ EXPECTED_MANUAL_NAMES)}"
        )

    validate_manifest_payload(records)
    validate_owner_edges(declarations, edges, actual_to_logical, records)
    validate_edge_evidence(edges, actual_to_logical)
    return records, actual_to_logical, declarations, edges


def read_manifest(path: Path) -> dict[str, ManifestRow]:
    raw = path.read_bytes()
    if len(raw) != EXPECTED_MANIFEST_FILE_BYTES:
        raise ValueError(
            f"expected {EXPECTED_MANIFEST_FILE_BYTES} manifest bytes, found {len(raw)}"
        )
    if sha256_bytes(raw) != EXPECTED_MANIFEST_FILE_SHA256:
        raise ValueError("raw ownership-manifest hash does not match the frozen file")

    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, delimiter="\t"))
    if not rows or rows[0] != ["format", "1"]:
        raise ValueError("ownership manifest must start with 'format\\t1'")

    records: dict[str, ManifestRow] = {}
    for row in rows[1:]:
        if len(row) != 4:
            raise ValueError(f"malformed ownership row: {row!r}")
        record = ManifestRow(*row)
        if record.logical_name in records:
            raise ValueError(f"duplicate ownership row: {record.logical_name}")
        records[record.logical_name] = record
    validate_manifest_payload(records)
    return records


def write_manifest(path: Path, records: dict[str, ManifestRow]) -> None:
    payload = b"format\t1\n" + validate_manifest_payload(records)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)


def owner_graph(
    declarations: list[Declaration],
    edges: list[tuple[str, str, str]],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> dict[str, set[str]]:
    module_by_name = {declaration.name: declaration.module for declaration in declarations}
    logical_to_owner = {
        logical: record.expected_module for logical, record in records.items()
    }
    graph: dict[str, set[str]] = {owner: set() for owner in OWNERS}

    for edge_kind, source, target in edges:
        source_logical = actual_to_logical.get(source)
        if source_logical is None:
            continue
        source_owner = logical_to_owner[source_logical]

        target_logical = actual_to_logical.get(target)
        if target_logical is not None:
            target_owner = logical_to_owner[target_logical]
            if source_owner != target_owner:
                graph[source_owner].add(target_owner)
            if source_owner in REUSABLE_OWNERS and target_owner in SOURCE_OWNERS:
                raise ValueError(
                    f"reusable-to-source {edge_kind} edge: {source} -> {target}"
                )
            continue

        target_module = module_by_name.get(target)
        if (
            source_owner in REUSABLE_OWNERS
            and target_module is not None
            and target_module.startswith("NumStability.Source.")
        ):
            raise ValueError(
                f"reusable-to-external-source {edge_kind} edge: {source} -> {target}"
            )

    temporary: set[str] = set()
    permanent: set[str] = set()

    def visit(owner: str) -> None:
        if owner in permanent:
            return
        if owner in temporary:
            raise ValueError(f"owner cycle through {owner}")
        temporary.add(owner)
        for dependency in graph[owner]:
            visit(dependency)
        temporary.remove(owner)
        permanent.add(owner)

    for owner in OWNERS:
        visit(owner)

    def reachable(start: str) -> set[str]:
        seen: set[str] = set()
        pending = list(graph[start])
        while pending:
            item = pending.pop()
            if item in seen:
                continue
            seen.add(item)
            pending.extend(graph[item] - seen)
        return seen

    for owner in REUSABLE_OWNERS:
        bad = reachable(owner) & SOURCE_OWNERS
        if bad:
            raise ValueError(f"{owner} reaches source owners: {sorted(bad)}")

    return graph


def validate_owner_edges(
    declarations: list[Declaration],
    edges: list[tuple[str, str, str]],
    actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> None:
    graph = owner_graph(declarations, edges, actual_to_logical, records)

    def reachable(start: str) -> set[str]:
        seen: set[str] = set()
        pending = list(graph[start])
        while pending:
            item = pending.pop()
            if item in seen:
                continue
            seen.add(item)
            pending.extend(graph[item] - seen)
        return seen

    closure = {owner: reachable(owner) for owner in OWNERS}
    reduction: dict[str, set[str]] = {}
    for owner, dependencies in graph.items():
        reduction[owner] = {
            dependency
            for dependency in dependencies
            if not any(
                dependency == alternative
                or dependency in closure[alternative]
                for alternative in dependencies - {dependency}
            )
        }

    if reduction != ALLOWED_OWNER_IMPORTS:
        details = []
        for owner in OWNERS:
            missing = sorted(reduction[owner] - ALLOWED_OWNER_IMPORTS[owner])
            extra = sorted(ALLOWED_OWNER_IMPORTS[owner] - reduction[owner])
            if missing or extra:
                details.append(f"{owner}: missing={missing}, extra={extra}")
        raise ValueError(
            "owner import allowlist is not the exact transitive reduction: "
            + "; ".join(details)
        )


def incident_edge_payload(
    edges: list[tuple[str, str, str]], actual_to_logical: dict[str, str]
) -> tuple[bytes, Counter[str]]:
    rows: list[str] = []
    kinds: Counter[str] = Counter()
    for edge_kind, source, target in edges:
        if source not in actual_to_logical and target not in actual_to_logical:
            continue
        kinds[edge_kind] += 1
        rows.append(
            "\t".join(
                (
                    "edge",
                    edge_kind,
                    actual_to_logical.get(source, source),
                    actual_to_logical.get(target, target),
                )
            )
        )
    return ("\n".join(sorted(rows)) + "\n").encode("utf-8"), kinds


def internal_edge_payload(
    edges: list[tuple[str, str, str]], actual_to_logical: dict[str, str]
) -> bytes:
    rows: list[str] = []
    for edge_kind, source, target in edges:
        if source in actual_to_logical and target in actual_to_logical:
            rows.append(
                "\t".join(
                    (
                        "edge",
                        edge_kind,
                        actual_to_logical[source],
                        actual_to_logical[target],
                    )
                )
            )
    return ("\n".join(sorted(rows)) + "\n").encode("utf-8")


def validate_edge_evidence(
    edges: list[tuple[str, str, str]], actual_to_logical: dict[str, str]
) -> None:
    incident, kinds = incident_edge_payload(edges, actual_to_logical)
    if sum(kinds.values()) != EXPECTED_INCIDENT_EDGES:
        raise ValueError(f"expected 18895 incident edges, found {sum(kinds.values())}")
    if kinds["signature"] != EXPECTED_SIGNATURE_INCIDENT_EDGES:
        raise ValueError(f"unexpected signature incident count: {kinds['signature']}")
    if kinds["body"] != EXPECTED_BODY_INCIDENT_EDGES:
        raise ValueError(f"unexpected body incident count: {kinds['body']}")
    if len(incident) != EXPECTED_INCIDENT_EDGE_BYTES:
        raise ValueError(f"unexpected incident payload bytes: {len(incident)}")
    if sha256_bytes(incident) != EXPECTED_INCIDENT_EDGE_SHA256:
        raise ValueError("incident-edge hash does not match Phase 11A")

    internal = internal_edge_payload(edges, actual_to_logical)
    internal_count = sum(
        1
        for _, source, target in edges
        if source in actual_to_logical and target in actual_to_logical
    )
    if internal_count != EXPECTED_INTERNAL_EDGES:
        raise ValueError(f"expected 12625 internal edges, found {internal_count}")
    if len(internal) != EXPECTED_INTERNAL_EDGE_BYTES:
        raise ValueError(f"unexpected internal payload bytes: {len(internal)}")
    if sha256_bytes(internal) != EXPECTED_INTERNAL_EDGE_SHA256:
        raise ValueError("internal-edge hash does not match Phase 11A")


def check_post_split(
    records: dict[str, ManifestRow],
    declarations: list[Declaration],
    edges: list[tuple[str, str, str]],
) -> dict[str, str]:
    structural = [
        declaration
        for declaration in declarations
        if declaration.module in STRUCTURAL_OWNERS
    ]
    if structural:
        raise ValueError(
            "structural modules own declarations: "
            + ", ".join(declaration.name for declaration in structural[:10])
        )

    actual_to_logical: dict[str, str] = {}
    actual_records: dict[str, Declaration] = {}
    for declaration in declarations:
        if declaration.module not in OWNERS:
            continue
        logical = logical_name(declaration.name, declaration.module)
        if logical in actual_records:
            raise ValueError(f"duplicate post-split logical name: {logical}")
        actual_records[logical] = declaration
        actual_to_logical[declaration.name] = logical

    if set(actual_records) != set(records):
        missing = sorted(set(records) - set(actual_records))
        extra = sorted(set(actual_records) - set(records))
        raise ValueError(f"post-split missing={missing[:20]}; extra={extra[:20]}")

    for logical, expected in records.items():
        actual = actual_records[logical]
        actual_tuple = (actual.module, actual.kind, actual.visibility)
        expected_tuple = (
            expected.expected_module,
            expected.kind,
            expected.visibility,
        )
        if actual_tuple != expected_tuple:
            raise ValueError(f"{logical}: expected {expected_tuple}; got {actual_tuple}")

    validate_owner_edges(declarations, edges, actual_to_logical, records)
    validate_edge_evidence(edges, actual_to_logical)
    return actual_to_logical


def module_path(project_root: Path, module: str) -> Path:
    return project_root / (module.replace(".", "/") + ".lean")


def direct_imports(path: Path) -> set[str]:
    imports: set[str] = set()
    source_lines = path.read_text(encoding="utf-8").splitlines()
    for line, code in zip(source_lines, strip_lean_comments(source_lines), strict=True):
        match = re.match(r"^\s*(?:public\s+)?import\s+(\S+)\s*$", code)
        if match:
            imports.add(match.group(1))
        elif re.match(r"^\s*(?:public\s+)?import\b", code):
            raise ValueError(f"unparsed import command in {path}: {line!r}")
    return imports


def check_project_imports(project_root: Path) -> None:
    for owner, family_dependencies in ALLOWED_OWNER_IMPORTS.items():
        path = module_path(project_root, owner)
        if not path.is_file():
            raise ValueError(f"missing post-split owner file: {path}")
        imports = direct_imports(path)
        allowed = family_dependencies | FOUNDATION_IMPORTS | ALLOWED_EXTERNAL_IMPORTS
        unexpected = sorted(imports - allowed)
        if unexpected:
            raise ValueError(
                f"{owner} has imports outside the frozen allowlist: {unexpected}"
            )

    bilinear = project_root / "NumStability/Source/Higham/Chapter23/BilinearAlgorithm.lean"
    bilinear_imports = direct_imports(bilinear)
    expected_bilinear_imports = {
        "Mathlib.Data.Matrix.Mul",
        "Mathlib.Data.Real.Basic",
    }
    if bilinear_imports != expected_bilinear_imports:
        raise ValueError(
            "BilinearAlgorithm import set differs from the frozen stale-Core cleanup: "
            f"expected {sorted(expected_bilinear_imports)}, got {sorted(bilinear_imports)}"
        )


def compare_full_graph(
    baseline_tsv: Path,
    candidate_tsv: Path,
    candidate_actual_to_logical: dict[str, str],
    records: dict[str, ManifestRow],
) -> None:
    if sha256_file(baseline_tsv) != BASELINE_TSV_SHA256:
        raise ValueError("baseline graph hash does not match frozen Phase 11A TSV")

    baseline_declarations, _ = read_tsv(baseline_tsv)
    baseline_name_by_logical = {
        logical_name(declaration.name, declaration.module): declaration.name
        for declaration in baseline_declarations
        if declaration.module == CORE
    }
    if set(baseline_name_by_logical) != set(records):
        raise ValueError("baseline Core logical-name set differs from manifest")

    candidate_name_to_baseline = {
        actual: baseline_name_by_logical[logical]
        for actual, logical in candidate_actual_to_logical.items()
    }

    delta: Counter[str] = Counter()
    with baseline_tsv.open(encoding="utf-8") as stream:
        for raw in stream:
            delta[raw.rstrip("\r\n")] += 1

    with candidate_tsv.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\r\n").split("\t")
            if fields[0] == "declaration" and fields[1] in candidate_name_to_baseline:
                fields[1] = candidate_name_to_baseline[fields[1]]
                fields[2] = CORE
            elif fields[0] == "edge":
                fields[2] = candidate_name_to_baseline.get(fields[2], fields[2])
                fields[3] = candidate_name_to_baseline.get(fields[3], fields[3])
            row = "\t".join(fields)
            delta[row] -= 1
            if delta[row] == 0:
                del delta[row]

    missing = sum(count for count in delta.values() if count > 0)
    extra = -sum(count for count in delta.values() if count < 0)
    if delta:
        details = "; ".join(
            f"{count:+d} {row}" for row, count in sorted(delta.items())[:10]
        )
        raise ValueError(
            f"full graph differs: missing={missing}, extra={extra}; {details}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "post"), required=True)
    parser.add_argument("--dependency-tsv", type=Path, required=True)
    parser.add_argument(
        "--baseline-tsv",
        type=Path,
        help="optional frozen Phase 11A TSV for the post-split full-graph check",
    )
    parser.add_argument(
        "--source",
        type=Path,
        default=Path("NumStability/Analysis/Norms/Core.lean"),
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=Path(
            "docs/architecture/declaration-ownership/norms-phase11b1.tsv"
        ),
    )
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help="write the frozen manifest; valid only in pre-migration mode",
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path("."),
        help="repository root used to enforce the frozen direct-import DAG",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.write_manifest and args.mode != "pre":
        raise ValueError("--write-manifest is valid only with --mode pre")

    if args.mode == "pre":
        records, actual_to_logical, _, _ = generate_manifest(
            args.source, args.dependency_tsv
        )
        if args.write_manifest:
            write_manifest(args.manifest, records)
        tracked = read_manifest(args.manifest)
        if tracked != records:
            raise ValueError("tracked manifest differs from the frozen generator output")
        print(
            "Phase 11B1 pre-migration ownership passed: "
            f"{len(records)} constants, inventory {EXPECTED_MANIFEST_SHA256}, "
            f"{len(actual_to_logical)} exact baseline names"
        )
        return 0

    records = read_manifest(args.manifest)
    declarations, edges = read_tsv(args.dependency_tsv)
    actual_to_logical = check_post_split(records, declarations, edges)
    check_project_imports(args.project_root)
    if args.baseline_tsv is not None:
        compare_full_graph(
            args.baseline_tsv,
            args.dependency_tsv,
            actual_to_logical,
            records,
        )
        graph_status = " and exact full graph preserved"
    else:
        graph_status = " and frozen incident/internal edge digests preserved"
    print(
        "Phase 11B1 post-migration ownership passed: "
        f"{len(records)} constants{graph_status}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f"ownership check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
