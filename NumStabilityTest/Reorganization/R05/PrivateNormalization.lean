import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Radius.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.Rounded.Core
import NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation
import NumStability.Analysis.Perturbation.LeastSquares.Equality.RowwiseBackwardError
import NumStability.Source.Higham.Chapter20.Equations.Core.Results
import NumStability.Source.Higham.Chapter20.Lemma11.Core.Results
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter20.Theorem04.Core.Results
import NumStability.Source.Higham.Chapter21.Attainability.Results
import NumStability.Source.Higham.Chapter21.Equation09.Results.Core
import NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core

/-!
# R05 approved private normalization (exhaustive)

Constructs all 106 approved post-delivery private names and requires
each present in the environment AND its pre-delivery name absent.
-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Attainability.Results" "NumStability.higham21_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Attainability.Results" "NumStability.higham21_theorem21_1_gramDual_eq_pseudoinverseTranspose" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Attainability.Results" "NumStability.higham21_vecNorm2_le_holderFactor_mul_lpNorm" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Attainability.Results" "NumStability.higham21_vecNorm2_left_le_add_of_inner_eq_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Attainability.Results" "NumStability.higham21_vecNorm2_right_le_add_of_inner_eq_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11UniformDirectionEnvelope_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11UniformDirectionFrobBound_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11UniformGramContraction_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11UniformGramInverseBound_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_direction_entry_le_uniform_envelope" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_direction_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_firstProduct_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_fixedRadiusCoefficient_le_uniform" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_frobNorm_absMatrix" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_frobNorm_smul_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_gramAbs_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_gramLinear_eq_products" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_gramLinear_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_gramQuadratic_eq_product" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_gramQuadratic_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_linearized_eq_product" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_linearized_frobNorm_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core" "NumStability.higham21Eq21_11_rectRowNorm2_le_frobNormRect" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation09.Results.Core" "NumStability.higham21_eq21_9_dimensions_pos_of_rhs_ne_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter21.Equation09.Results.Core" "NumStability.higham21_eq21_9_rectOpNorm2Le_const_mul_abs" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.Rounded.Core" "NumStability.higham21_vecNorm2Sq_ne_zero_of_fun_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.Rounded.Core" "NumStability.higham21_vecNorm2_ne_zero_of_fun_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_baseSolution_norm_pos_of_rhs_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_domainProjection_residual_abs_le_scaled_majorant" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_realVecToComplex_norm_le_vecNorm2_mul_norm_one" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_realVecToComplex_norm_smul" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_rectTransposeMulVec_abs_le_scaled_majorant" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_scaled_data_majorant" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Bounds.Core" "NumStability.higham21_theorem21_1_exact_remainder_numerator_bound" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Radius.Core" "NumStability.higham21PerturbationRadius_mul_max_le_half" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core" "NumStability.higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core" "NumStability.higham21_matMulRectRight_projector_transpose_mulVec" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core" "NumStability.higham21_rectMatMulVec_matMulRectRight" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core" "NumStability.higham21_right_nonneg_le_sqrt_sq_add_sq" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.Executor.Core" "NumStability.higham21_sqrt_sq_add_sq_le_sqrt_two_mul" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations.Core.Results" "NumStability.higham20Eq20_19_abs_minus_le_balanced_of_balanced_le_alpha" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations.Core.Results" "NumStability.higham20Eq20_19_plus_div_antitone_until_balanced" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations.Core.Results" "NumStability.higham20Eq20_19_plus_mono_alpha" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations.Core.Results" "NumStability.higham20_cholesky_coefficient_le_gamma_3n1" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.complexMatrixRank_adjoint" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.complex_penrose1" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.complex_penrose2" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.complexification_eq_adjoint_of_symmetric" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.domainProjection_fixes_adjointRange" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.finrank_leadSpan" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.gramRange_eq_adjointRange" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.leadSpan_eq_gramRange_of_rankIndex" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.pseudoinverse_eq_zero_of_complexMatrixRank_eq_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.pseudoinverse_output_mem_gramRange" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.rangeProjection_complex_action_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.rangeProjection_idempotent" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.rangeProjection_rectOpNorm2Le_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.realRect_diff_euclideanLin_bound" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.realRect_eq_zero_of_complexMatrixRank_eq_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11.Core.Results" "NumStability.singularValue_ne_zero_iff_le_rankIndex" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem04.Core.Results" "NumStability.higham20Theorem20_4_matMulRect_mono_left" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.isInverse_rectMatMulVec_bijective" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.isOrthogonal_of_column_orthonormal" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.isRightInverse_of_isLeftInverse_square" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lseConstraintLinearMap_basis" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lseDotDual" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lseDotDual_basis" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lseDual_eval_eq_sum" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lseKernelFactorDual" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lseKernelFactorDual_apply_constraint" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.lse_linear_term_eq_zero_of_quadratic_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.theorem20_7_finProdUniv_nonempty_of_pos" 0,
  mangledPrivateName "NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic" "NumStability.theorem20_7_finUniv_nonempty_of_pos" 0,
  mangledPrivateName "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation" "NumStability.continuous_lsObjective" 0,
  mangledPrivateName "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation" "NumStability.continuous_lseConstraintResidual_apply" 0,
  mangledPrivateName "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation" "NumStability.lsObjective_gqrAQBlock_eq" 0,
  mangledPrivateName "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation" "NumStability.lsResidual_gqrAQBlock" 0,
  mangledPrivateName "NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation" "NumStability.vecNorm2Sq_append" 0,
  mangledPrivateName "NumStability.Analysis.Perturbation.LeastSquares.Equality.RowwiseBackwardError" "NumStability.theorem20_7_finRectProdUniv_nonempty_of_pos" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.complexMatrixEuclideanLin_ker_eq_bot_of_rank_eq_card" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.complexMatrixRank_eq_card_of_euclideanLin_ker_eq_bot" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.complexMatrixRank_ne_card_of_euclideanLin_ker_nonzero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.finiteTranspose_formulaMatrix_real_kernel_eq_zero_of_not_isLeastSquaresMinimizer" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.frobNormSqRect_add_eq_add_of_inner_eq_zero_lsq" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.frobNormSqRect_rankOne_real" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsAugmentedEq20_7LeftMajorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsAugmentedEq20_7Majorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsAugmentedEq20_7RightMajorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsAugmentedEq20_8LeftMajorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsAugmentedEq20_8Majorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsAugmentedEq20_8RightMajorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsComponentwiseDataMajorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsComponentwiseTransposeMajorant_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsEq20_6_rhsBottom_abs_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsEq20_6_rhsTop_abs_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsLemma20_6Perturbation_left_decomp" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsLemma20_6Perturbation_transpose_action_self" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.lsResidualHigham_column_sum_eq_neg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.matMulVec_absMatrix_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.realRectToCMatrix_finiteTranspose_formulaMatrix_left_panel_kernel" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.realVecToEuclidean_ne_zero_of_vecNorm2Sq_ne_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.rectMatMulVec_absMatrixRect_nonneg" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.rectMatMulVec_add_matrix_lsq" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.vecNorm2Sq_add_eq_add_of_inner_eq_zero_lsq" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.vecNorm2Sq_pos_of_ne_zero_lsq" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem03.QRSolve" "NumStability.vecNorm2_pos_of_ne_zero_lsq" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Attainability" "NumStability.higham21_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Attainability" "NumStability.higham21_theorem21_1_gramDual_eq_pseudoinverseTranspose" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Attainability" "NumStability.higham21_vecNorm2_le_holderFactor_mul_lpNorm" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Attainability" "NumStability.higham21_vecNorm2_left_le_add_of_inner_eq_zero" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Attainability" "NumStability.higham21_vecNorm2_right_le_add_of_inner_eq_zero" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11UniformDirectionEnvelope_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11UniformDirectionFrobBound_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11UniformGramContraction_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11UniformGramInverseBound_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_direction_entry_le_uniform_envelope" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_direction_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_firstProduct_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_fixedRadiusCoefficient_le_uniform" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_frobNorm_absMatrix" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_frobNorm_smul_nonneg" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_gramAbs_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_gramLinear_eq_products" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_gramLinear_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_gramQuadratic_eq_product" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_gramQuadratic_frobNorm_le_uniform" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_linearized_eq_product" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_linearized_frobNorm_le" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_11Uniform" "NumStability.higham21Eq21_11_rectRowNorm2_le_frobNormRect" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_9" "NumStability.higham21_eq21_9_dimensions_pos_of_rhs_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Eq21_9" "NumStability.higham21_eq21_9_rectOpNorm2Le_const_mul_abs" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21MGSRounded" "NumStability.higham21_vecNorm2Sq_ne_zero_of_fun_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21MGSRounded" "NumStability.higham21_vecNorm2_ne_zero_of_fun_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_baseSolution_norm_pos_of_rhs_ne_zero" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_domainProjection_residual_abs_le_scaled_majorant" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_realVecToComplex_norm_le_vecNorm2_mul_norm_one" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_realVecToComplex_norm_smul" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_rectTransposeMulVec_abs_le_scaled_majorant" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_scaled_data_majorant" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21Perturbation" "NumStability.higham21_theorem21_1_exact_remainder_numerator_bound" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.Higham21PerturbationRadius" "NumStability.higham21PerturbationRadius_mul_max_le_half" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve" "NumStability.higham21_lemma21_2_symmetrized_perturbation_eq_deltaA2_add_H_projector" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve" "NumStability.higham21_matMulRectRight_projector_transpose_mulVec" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve" "NumStability.higham21_rectMatMulVec_matMulRectRight" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve" "NumStability.higham21_right_nonneg_le_sqrt_sq_add_sq" 0,
  mangledPrivateName "NumStability.Algorithms.Underdetermined.UnderdeterminedSolve" "NumStability.higham21_sqrt_sq_add_sq_le_sqrt_two_mul" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations" "NumStability.higham20Eq20_19_abs_minus_le_balanced_of_balanced_le_alpha" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations" "NumStability.higham20Eq20_19_plus_div_antitone_until_balanced" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations" "NumStability.higham20Eq20_19_plus_mono_alpha" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Equations" "NumStability.higham20_cholesky_coefficient_le_gamma_3n1" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.complexMatrixRank_adjoint" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.complex_penrose1" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.complex_penrose2" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.complexification_eq_adjoint_of_symmetric" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.domainProjection_fixes_adjointRange" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.finrank_leadSpan" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.gramRange_eq_adjointRange" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.leadSpan_eq_gramRange_of_rankIndex" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.pseudoinverse_eq_zero_of_complexMatrixRank_eq_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.pseudoinverse_output_mem_gramRange" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.rangeProjection_complex_action_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.rangeProjection_idempotent" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.rangeProjection_rectOpNorm2Le_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.realRect_diff_euclideanLin_bound" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.realRect_eq_zero_of_complexMatrixRank_eq_zero" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Lemma11" "NumStability.singularValue_ne_zero_iff_le_rankIndex" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter20.Theorem04" "NumStability.higham20Theorem20_4_matMulRect_mono_left" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R05 private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R05 private normalization: retired name {name} still present"
