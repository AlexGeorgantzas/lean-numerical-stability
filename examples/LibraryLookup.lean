import LeanFpAnalysis.FP
import LeanFpAnalysis.FP.Analysis.HighamChapter7
import LeanFpAnalysis.FP.Analysis.Norms
import LeanFpAnalysis.FP.Algorithms.Horner
import LeanFpAnalysis.FP.Algorithms.HighamChapter8
import LeanFpAnalysis.FP.Algorithms.HighamChapter9
import LeanFpAnalysis.FP.Algorithms.HighamChapter10
import LeanFpAnalysis.FP.Algorithms.HighamChapter11
import LeanFpAnalysis.FP.Algorithms.HighamChapter12
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR
import LeanFpAnalysis.FP.Algorithms.QR.QRSolve

set_option pp.maxSteps 1000

open LeanFpAnalysis.FP

/-!
Curated executable lookup for library exploration.

Run it with:

  lake env lean examples/LibraryLookup.lean

The exhaustive human-readable map is `docs/LIBRARY_LOOKUP.md`. This file stays
small enough to serve as a smoke check for representative public declarations.
-/

-- Floating-point model and gamma calculus.
#check FPModel
#check BasicOp
#check gamma
#check gammaValid
#check gamma_nonneg
#check prod_error_bound
#check prod_signed_error_bound

-- Error, conditioning, and norm foundations from Split 1.
#check absError
#check relError
#check normwiseBackwardErrorBoundedVec
#check normwiseConditionNumberBoundedVec
#check complexVecLpNorm
#check complexVecLpNorm_holder
#check complexMatrixLpNorm_le_rieszThorin_of_closedCase

-- Polynomial and QR infrastructure from the updated upstream branch.
#check hornerDesc_eq_polyDesc
#check fl_hornerDesc_forward_error_bound
#check householderConstructApplyBound_le_gamma
#check fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid

-- Core algorithmic stability results.
#check dotProduct_error_bound
#check matVec_backward_error
#check matMul_error_bound
#check fl_backSub
#check backSub_backward_error
#check fl_forwardSub
#check forwardSub_backward_error
#check triangularSolve_backward_error
#check lu_solve_backward_error
#check cholesky_solve_backward_error

-- Higham Chapter 7 source-facing wrappers.
#check ch7ForwardBoundEF
#check problem7_1_componentwise_resolvent_bound
#check problem7_2_infNorm_residual_lower
#check problem7_8_frobenius_characterization_pos
#check stochasticMatrix_mul_ones

-- Higham Chapter 8 source-facing wrappers.
#check higham8_1_backSub
#check higham8_3_backSub_backward_error
#check higham8_10_forwardSub_forward_error_mu_bound
#check higham8_11_mmatrix_forwardSub_relative_error
#check higham8_14_infNorm_upperBound

-- Higham Chapter 9 source-facing wrappers and local Split 2 closures.
#check higham9_3_lu_backward_error_gamma
#check higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero
#check higham9_7_partialPivoting_growth_bound_and_attainment
#check higham9_8_exists_completePivoting_growth_factor_ge_theta_real
#check higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP

-- Higham Chapter 10 source-facing wrappers.
#check higham10_1_cholesky_existence
#check higham10_problem_10_1_maxEntryNorm_eq_largest_diag
#check higham10_problem_10_4_unpivoted_ge_positive_pivots_and_growth
#check higham10_problem_10_8_counterexample_not_psd

-- Higham Chapter 11 source-facing wrappers.
#check higham11_6_partialPivotExample_factorization
#check higham11_problem_11_2_twoByTwoPivot_scaledInverse_spec
#check higham11_problem_11_8_rookCompleteExample_factorization
#check higham11_problem_11_9_nonsymPosDef_of_symPartSPD

-- Higham Chapter 12 source-facing wrappers.
#check higham12_9_conventional_residual_error
#check higham12_3_exact_one_step_residual_bound
#check higham12_4_conditional_two_gamma_bound
#check higham12_problem_12_1_square
