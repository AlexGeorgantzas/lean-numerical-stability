import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonal
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.BlockDiagonalCompression
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPair
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairPinching
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeProjection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ColumnPairRangeReflection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteDimensional
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteMatrixOrder
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealEmbedding
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.FiniteRealOrder
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ProjectionReflection
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularCompression
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.RectangularMultiplication
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.ReflectionAverage
import NumStability.Analysis.CStarMatrices.FiniteMatrixAlgebra.StrictPositivity
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers
import NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur
import NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ArcLengthPowerBounds.FiniteDimension
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.FiniteDimensionalPowerBounds.Kreiss
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarCrossingBounds.Polynomial
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ResolventCoefficients.Analytic
import NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers
import NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo
import NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation
import NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation
import NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation
import NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional.Bounds

/-!
# R07 private normalization (exhaustive)

Requires every one of the 44 approved destination-private names to be
present, every historical private name to be absent, and every public
member of the reviewed 77-row private reverse closure to elaborate.
-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers" "NumStability.bergerGeneral_smul_pow" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers" "NumStability.bergerGeneral_sum_p" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers" "NumStability.bergerGeneral_telescoping" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers" "NumStability.bergerGeneral_unit_root" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.Powers" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Internal.HermitianEuclideanSpaceNotation" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo" "NumStability.exists_unit_sq_mul" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo" "NumStability.inner_diag_diff" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_apply_eq_zero" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_eq_zero_of_ge" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_eq_zero_of_lt" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_succ_succ" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_succ_zero" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_zero_succ" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.Ppiece_zero_zero" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.norm_Ppiece_le" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.opNorm_one" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.opNorm_unitary" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.opNorm_unitary_conj" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SchurBinomialBounds.Estimates" "NumStability.sum_Ppiece" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal" "NumStability.conjTranspose_mul_diag" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers" "NumStability.l2_opNorm_of_mem_unitaryGroup" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers" "NumStability.l2_opNorm_one" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers" "NumStability.l2_opNorm_unitary_conj" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal" "NumStability.mul_conjTranspose_diag" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers" "NumStability.pi_norm_pow" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarCrossingBounds.Polynomial" "NumStability.natDegree_C_mul_mul_le_two_mul" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.exists_spijkerPartitionCrossing" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.integral_abs_deriv_le_eVariationOn" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.lintegral_spijkerPartitionLevelMultiplicity" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.measurable_spijkerPartitionLevelMultiplicity" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerActiveIncrements" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerActiveIncrements_card_le_of_crossing_bound" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerLevelInterval" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerPartitionEndpointValues" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerPartitionLevelMultiplicity" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerPartitionLevelMultiplicity_eq_card" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerPartitionLevelMultiplicity_le" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijkerPartition_edist_sum_le" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation" "NumStability.spijker_eVariationOn_le" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.NumericalRadius.Core.Internal.EuclideanSpaceNotation" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.Internal.ScalarNotation" "NumStability.term↑ₐ" 0,
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Analysis.BergerGeneral" "NumStability.bergerGeneral_smul_pow" 0,
  mangledPrivateName "NumStability.Analysis.BergerGeneral" "NumStability.bergerGeneral_sum_p" 0,
  mangledPrivateName "NumStability.Analysis.BergerGeneral" "NumStability.bergerGeneral_telescoping" 0,
  mangledPrivateName "NumStability.Analysis.BergerGeneral" "NumStability.bergerGeneral_unit_root" 0,
  mangledPrivateName "NumStability.Analysis.BergerGeneral" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.BergerInequality" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.BergerResolvent" "NumStability.exists_unit_sq_mul" 0,
  mangledPrivateName "NumStability.Analysis.BergerResolvent" "NumStability.inner_diag_diff" 0,
  mangledPrivateName "NumStability.Analysis.BergerResolvent" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_apply_eq_zero" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_eq_zero_of_ge" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_eq_zero_of_lt" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_succ_succ" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_succ_zero" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_zero_succ" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.Ppiece_zero_zero" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.norm_Ppiece_le" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.opNorm_one" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.opNorm_unitary" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.opNorm_unitary_conj" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersBinomialBound" "NumStability.sum_Ppiece" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSchur" "NumStability.conjTranspose_mul_diag" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSchur" "NumStability.l2_opNorm_of_mem_unitaryGroup" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSchur" "NumStability.l2_opNorm_one" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSchur" "NumStability.l2_opNorm_unitary_conj" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSchur" "NumStability.mul_conjTranspose_diag" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSchur" "NumStability.pi_norm_pow" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanar" "NumStability.natDegree_C_mul_mul_le_two_mul" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.exists_spijkerPartitionCrossing" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.integral_abs_deriv_le_eVariationOn" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.lintegral_spijkerPartitionLevelMultiplicity" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.measurable_spijkerPartitionLevelMultiplicity" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerActiveIncrements" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerActiveIncrements_card_le_of_crossing_bound" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerLevelInterval" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerPartitionEndpointValues" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerPartitionLevelMultiplicity" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerPartitionLevelMultiplicity_eq_card" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerPartitionLevelMultiplicity_le" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijkerPartition_edist_sum_le" 0,
  mangledPrivateName "NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis" "NumStability.spijker_eVariationOn_le" 0,
  mangledPrivateName "NumStability.Analysis.NumericalRadius" "NumStability.term𝔼" 0,
  mangledPrivateName "NumStability.Analysis.PseudospectralResolvent" "NumStability.term↑ₐ" 0,
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R07 private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R07 private normalization: retired name {name} still present"

#check @NumStability.RationalOrderCertificate.arcLength_le
#check @NumStability.RationalOrderCertificate.arcLength_le_of_planar_analyticBridge
#check @NumStability.RationalOrderCertificate.projection_crossing_finset_card_le_two_mul
#check @NumStability.exists_schur_powerBounds
#check @NumStability.higham18_kreiss_two_sided_proved
#check @NumStability.higham18_kreiss_upper_proved
#check @NumStability.norm_apply_sq_add_norm_inner_sq_le
#check @NumStability.norm_pow_eq_norm_schur_pow
#check @NumStability.norm_pow_le_exp_mul_dim_proved
#check @NumStability.norm_pow_le_two_mul_numericalRadius_pow
#check @NumStability.norm_pow_nilpotent
#check @NumStability.norm_pow_normal_eq
#check @NumStability.norm_pow_two_le_two_mul_numericalRadius_sq
#check @NumStability.normal_iff_strictUpper_eq_zero_unconditional
#check @NumStability.normal_schur_strictUpper_eq_zero
#check @NumStability.normal_upperTriangular_isDiag
#check @NumStability.numericalRadiusCLM_pow_le
#check @NumStability.numericalRadiusCLM_pow_le_one_of_le_one
#check @NumStability.numericalRadiusCLM_pow_pointwise_le_of_le_one
#check @NumStability.numericalRadiusCLM_pow_two_le
#check @NumStability.numericalRadiusCLM_pow_two_le_one_of_le_one
#check @NumStability.numericalRadiusCLM_pow_two_pow_le
#check @NumStability.numericalRadius_pow_le
#check @NumStability.numericalRadius_pow_two_le
#check @NumStability.numericalRadius_pow_two_pow_le
#check @NumStability.opNorm_schurpow_le_binomial
#check @NumStability.powerBound_exp_mul_dim_proved
#check @NumStability.schurNormalImpliesStrictUpperZero_holds
#check @NumStability.spijkerArcLengthBound_proved
#check @NumStability.spijkerPlanarAnalyticBridge
#check @NumStability.spijkerProjectionCrossingPolynomial_natDegree_le
#check @NumStability.spijker_crossing_variation
#check @NumStability.spijker_projection_crossing_finset_card_le_two_mul
