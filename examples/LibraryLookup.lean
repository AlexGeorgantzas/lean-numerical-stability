import LeanFpAnalysis.FP
import LeanFpAnalysis.HDP

open LeanFpAnalysis.FP
open LeanFpAnalysis.HDP

/-!
This file is a small executable index for library exploration.
Run it with:

  lake env lean examples/LibraryLookup.lean

It intentionally contains no task-specific proof scripts.
-/

-- Floating-point model and gamma calculus
#check FPModel
#check gamma
#check gammaValid
#check gammaValid_mono
#check gamma_nonneg
#check gamma_mono
#check prod_error_bound
#check gamma_mul
#check gamma_inv
#check gamma_div
#check gamma_sum_le

-- General error and stability definitions
#check absError
#check relError
#check backwardErrorBounded
#check backwardErrorBoundedVec
#check relBackwardErrorBounded2
#check isRelComponentwiseBackwardStable
#check forward_from_backward

-- Summation and dot products
#check fl_sum_error
#check fl_sum_error_init
#check fl_sum_error_tight
#check fl_dotProduct
#check dotProduct_error_bound
#check dotProduct_backward_error
#check dotProduct_backward_stable_x
#check dotProduct_backward_stable_y
#check dotProduct_isRelBackwardStable

-- Matrix-vector and matrix-matrix products
#check fl_matVec
#check matVec_backward_error
#check matVec_error_bound
#check matVec_row_isRelBackwardStable
#check fl_matMul
#check matMul_error_bound
#check matMul_backward_error_col
#check outerProduct_error_bound
#check outerProduct_backward_error

-- Triangular solves
#check fl_forwardSub
#check forwardSub_backward_error
#check fl_backSub
#check backSub_backward_error
#check triangularSolve_backward_error
#check backSub_forward_error
#check forwardSub_forward_error

-- LU and Cholesky solve contracts
#check LUBackwardError
#check lu_backward_error_gamma
#check lu_solve_backward_error
#check lu_solve_backward_error_tight
#check CholeskyBackwardError
#check cholesky_backward_error_perturbation
#check cholesky_solve_backward_error_expanded
#check cholesky_solve_backward_error

-- Residuals, refinement, and stationary iteration
#check fl_residual
#check ResidualError
#check SolverSpec
#check conventional_residual_error
#check one_step_refinement_error_identity
#check one_step_residual_bound
#check lu_refinement_backward_stable
#check normwise_forward_bound
#check main_forward_bound
#check normwise_residual_bound

-- Exact matrix algebra and perturbation theory
#check matMul_id_right
#check matMul_id_left
#check matMul_assoc
#check matMul_vec_eq
#check matMulVec_matMul
#check forward_error_from_residual
#check componentwise_forward_error
#check forward_error_from_backward_error
#check normwise_forward_error_exact

-- HDP appetizer entry points
#check PairwiseNormBound
#check empiricalAverage
#check caratheodory_finiteDimensional
#check approximate_caratheodory_theorem_0_0_2
#check empiricalCenters_ncard_le
#check covering_polytopes_by_balls_param
#check covering_polytopes_by_balls
#check unorderedEmpiricalCenters_ncard_le_choose
#check improved_covering_polytopes_by_balls
#check exercise_0_0_5_binomial_chain
#check weighted_variance_identity
