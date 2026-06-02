# LeanFpAnalysis Library Lookup

This guide is a public map of the floating-point analysis library. It is meant
for Lean users, documentation tools, and automated agents that need to discover
which files and theorem names are relevant to a stability-analysis goal.

It is not a proof-script guide: it maps library concepts and theorem names
without giving task-specific scripts.

## How To Import

For exploratory work, start with:

```lean
import LeanFpAnalysis.FP
open LeanFpAnalysis.FP
```

For a smaller import, use the file listed in the tables below.

## Exact Algebra And Norm Policy

Mathlib is the source of truth for exact dot products, matrix algebra, and
norms.  Use Mathlib notation directly when the object already has a
Mathlib-native type, for example `x ⬝ᵥ y`, `‖WithLp.toLp 2 x‖`, or `‖A‖` for
`A : RMat m n` under the appropriate matrix norm scope.

Some existing algorithm APIs still use function-shaped matrices
`RMatFn m n := Fin m → Fin n → ℝ`.  For those legacy APIs, use compatibility
wrappers such as `frobNorm` and `infNorm`.  These wrappers are bridges to
Mathlib norms via `Matrix.of`; they are not independent norm definitions.

New exact matrix-facing APIs should prefer `RMat m n := Matrix (Fin m) (Fin n)
ℝ`, especially for rectangular algorithms such as QR and least squares.
Existing `fl_*` algorithms may continue using `RMatFn` while the implementation
layer is migrated gradually.

## Goal-To-Theorem Lookup

| Goal shape | Start with | Main definitions | Main theorem names | Notes |
|---|---|---|---|---|
| Floating-point model assumptions | `LeanFpAnalysis/FP/Model.lean` | `FPModel` | fields `model_add`, `model_sub`, `model_mul`, `model_div`, `model_sqrt` | Axiomatic Higham-style model; not IEEE-specific. Square root is modeled for nonnegative inputs. |
| Accumulated rounding errors | `LeanFpAnalysis/FP/Analysis/Rounding.lean` | `gamma`, `gammaValid` | `gammaValid_mono`, `gamma_nonneg`, `gamma_mono`, `prod_error_bound`, `gamma_mul`, `gamma_inv`, `gamma_div`, `gamma_sum_le` | Most algorithm bounds require a `gammaValid fp k` hypothesis. |
| Basic error and stability predicates | `LeanFpAnalysis/FP/Analysis/Error.lean`, `LeanFpAnalysis/FP/Analysis/Stability.lean` | `absError`, `relError`, `backwardErrorBounded`, `backwardErrorBoundedVec`, `relBackwardErrorBounded2`, `isRelComponentwiseBackwardStable` | `forward_from_backward` | General scalar/vector definitions used by low-level algorithm contracts. |
| Sequential summation | `LeanFpAnalysis/FP/Analysis/Summation.lean` | accumulated sums through `Fin.foldl` | `fl_sum_error`, `fl_sum_error_init`, `fl_sum_error_tight` | Core input to dot-product proofs. |
| Subtraction folds and inverse products | `LeanFpAnalysis/FP/Analysis/SubtractionFold.lean` | subtraction accumulation helpers | `fl_sub_sum_error_init`, `inv_prod_error_bound` | Used heavily by triangular substitution proofs. |
| Dot product forward error | `LeanFpAnalysis/FP/Algorithms/DotProduct.lean` | `fl_dotProduct` | `dotProduct_error_bound` | Tight `gamma fp n` bound for the sequential dot product. |
| Dot product backward error | `LeanFpAnalysis/FP/Algorithms/DotProduct.lean` | `fl_dotProduct` | `dotProduct_backward_error`, `dotProduct_backward_stable_x`, `dotProduct_backward_stable_y`, `dotProduct_isRelBackwardStable` | Componentwise relative perturbations of one input vector. |
| Floating 2-norm | `LeanFpAnalysis/FP/Algorithms/Norm2.lean` | `fl_norm2Sq`, `fl_norm2` | `norm_toLp_two_eq_sqrt_dotProduct`, `dotProduct_self_nonneg_real`, `dotProduct_self_eq_zero_iff_real`, `dotProduct_self_pos_iff_real`, `fl_norm2Sq_backward_error`, `fl_norm2Sq_nonneg_of_gammaValid_two_mul`, `fl_norm2_unroll`, `fl_norm2_unroll_of_gammaValid_two_mul` | Exact facts use Mathlib `dotProduct` and `‖WithLp.toLp 2 x‖` directly; FP facts compute `xᵀx` by `fl_dotProduct`, then apply rounded `FPModel.fl_sqrt`. |
| Matrix-vector product | `LeanFpAnalysis/FP/Algorithms/MatVec.lean` | `fl_matVec` | `matVec_backward_error`, `matVec_error_bound`, `matVec_row_isRelBackwardStable` | Built row-by-row from dot products. |
| Matrix multiplication | `LeanFpAnalysis/FP/Algorithms/MatMul.lean` | `fl_matMul` | `matMul_error_bound`, `matMul_backward_error_col` | Backward theorem is columnwise; each column may use a different perturbation. |
| Outer product | `LeanFpAnalysis/FP/Algorithms/OuterProduct.lean` | `fl_outerProduct` | `outerProduct_error_bound`, `outerProduct_backward_error` | Useful for rank-one update reasoning. |
| Recursive, pairwise, and tree summation | `LeanFpAnalysis/FP/Algorithms/RecursiveSum.lean`, `PairwiseSum.lean`, `SumTree.lean` | recursive/tree sum algorithms | `recursiveSum_backward_error`, `recursiveSum_forward_error_bound`, `pairwiseSum_backward_error`, `pairwiseSum_forward_error_bound`, `backward_error`, `forward_error` | `SumTree.backward_error` and `SumTree.forward_error` are in the same namespace and have generic names. |
| Forward substitution | `LeanFpAnalysis/FP/Algorithms/ForwardSub.lean` | `fl_forwardSub` | `forwardSub_backward_error`, `fl_forwardSub_satisfies_spec` | Lower-triangular solve. Requires nonzero diagonal and lower-triangular zero pattern. |
| Back substitution | `LeanFpAnalysis/FP/Algorithms/TriangularSolve.lean` | `fl_backSub` | `backSub_backward_error`, `backSub_backward_error_perturbed`, `backSub_backward_error_dual`, `fl_backSub_satisfies_spec` | Upper-triangular solve. Requires nonzero diagonal and upper-triangular zero pattern. |
| Combined triangular solve | `LeanFpAnalysis/FP/Algorithms/TriangularSolveCombined.lean` | `fl_forwardSub`, `fl_backSub` | `triangularSolve_backward_error` | Composes forward and back substitution. |
| Triangular forward-error bounds | `LeanFpAnalysis/FP/Analysis/ForwardError.lean`, `Algorithms/TriangularForwardBound.lean`, `Algorithms/TriangularForwardComparison.lean` | inverse and comparison quantities | `backSub_forward_error`, `forwardSub_forward_error`, `backSub_forward_error_diagDom`, `forwardSub_forward_error_comparison`, `forwardSub_forward_error_mu_bound` | These convert backward-error statements into forward-error bounds under matrix assumptions. |
| M-matrix forward substitution | `LeanFpAnalysis/FP/Algorithms/MMatrix.lean` | M-matrix predicates and comparison quantities | `forwardSub_nonneg`, `mmatrix_forwardSub_relative_error` | Proves the Corollary 8.10 relative-error statement in mu-form. |
| Inverse and triangular inverse bounds | `LeanFpAnalysis/FP/Algorithms/InverseBounds.lean` | inverse and norm bounds | `theorem_8_11_first_ineq`, `theorem_8_11_upper_bound` | Higham chapter 8 inverse-bound infrastructure. |
| LU factorization backward error | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean` | `LUBackwardError` | `lu_backward_error_perturbation`, `lu_backward_error_relative`, `lu_backward_error_gamma` | Specification of computed LU factors and perturbation bounds. |
| LU solve backward error | `LeanFpAnalysis/FP/Algorithms/LU/LUSolve.lean` | `fl_forwardSub`, `fl_backSub`, `LUBackwardError` | `lu_solve_backward_error`, `lu_solve_backward_error_tight`, `lu_solve_backward_error_mixed` | Composes LU factorization with triangular solves. |
| Structured LU bounds | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `SpecialMatrices.lean`, `Tridiagonal.lean`, `Doolittle.lean`, `BlockLU.lean` | growth-factor and special-matrix specs | `diagDom_lu_solve_backward_stable`, `spd_lu_backward_error`, `mmatrix_lu_backward_stable`, `banded_lu_backward_error`, `doolittle_solve_backward_error`, `block_lu_solve_backward_error` | Some structured results are specification-level interfaces; inspect hypotheses. |
| Cholesky factorization | `LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskySpec.lean` | `CholeskyBackwardError` | `cholesky_backward_error_perturbation`, `cholesky_backward_error_relative`, `cholesky_spd_backward_stable` | Factorization contract for SPD-style analyses. |
| Cholesky solve | `LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskySolve.lean` | `fl_forwardSub`, `fl_backSub`, `CholeskyBackwardError` | `cholesky_solve_backward_error_expanded`, `cholesky_solve_backward_error`, `cholesky_solve_spd_backward_stable` | Composes Cholesky factorization with two triangular solves. |
| QR factorization and QR solve | `LeanFpAnalysis/FP/Algorithms/QR/*.lean` | `householder`, `fl_householderApply`, `fl_householderQR_R`, `fl_householderQR_rhs`, `fl_householderQR_solve`, `givensRotation`, `givensC`, `givensS`, `fl_givensC`, `fl_givensS`, `fl_givensApply`, `GivensCoeffError`, `HouseholderQRBackwardError`, `HouseholderQRRhsPanelBackwardError`, `HouseholderQRPanelSolveBackwardError`, `GivensQRBackwardError`, `QRSolveBackwardError` | `fl_householderQR_R_structured_backward_error`, `fl_householderQRPanel_rhs_backward_error`, `fl_householderQR_rhs_backward_error`, `fl_householderQR_solve_components_backward_error`, `fl_householderQR_solve_backward_error`, `givensCoeff_norm_sq`, `givensCoeff_zero_second`, `givensRotation_constructed_orthogonal`, `fl_givensC_relative_error_conservative`, `fl_givensS_relative_error_conservative`, `fl_givensCoeffError_conservative`, `givensRotation_matMulVec_p`, `givensRotation_matMulVec_q`, `fl_givensApply_supplied_app_error`, `householder_qr_backward`, `givens_qr_backward`, `qr_solve_backward_error_from_components`, `qr_solve_perturbation_bound` | Householder QR now has implementation-backed recursive `R`, RHS-transform, shared-`Q` component, and full concrete solve bridges under explicit readiness/nonzero-diagonal/gamma assumptions. Givens has exact and rounded coefficient kernels, a conservative `gamma 6` coefficient contract bridge, and a supplied-parameter application bridge; the sharper Higham Lemma 18.6 `gamma 4` bridge and full Givens QR remain pending. |
| Residual computation | `LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean` | `fl_residual`, `ResidualError` | `conventional_residual_error` | Bound for the computed residual `fl(b - A*x_hat)`. |
| Iterative refinement | `LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean` | `SolverSpec`, `ResidualError` | `one_step_refinement_error_identity`, `one_step_residual_bound`, `one_step_backward_error_contraction`, `lu_refinement_backward_stable`, `refinement_forward_error_bound`, `thm_11_4_residual_bound` | Mixes exact algebra, solver specifications, and residual computation bounds. |
| Stationary iteration | `LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean` | iteration/residual helpers | `one_step_error`, `local_error_simplified`, `residual_eq_A_error`, `one_step_residual`, `normwise_forward_bound`, `main_forward_bound`, `normwise_one_step_residual_bound`, `normwise_residual_bound` | Useful for harder compositional stability analyses. |
| Matrix algebra infrastructure | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean` | `RVec`, `RMat`, `RSqMat`, `RMatFn`, `frobNorm`, `infNorm`, matrix products, identities, inverses | `matMul_id_right`, `matMul_id_left`, `matMul_assoc`, `matMul_vec_eq`, `matMulVec_matMul`, `frobNorm_matMul_le`, `abs_entry_le_frobNorm`, `abs_matMulVec_le_card_bound_infNormVec`, `IsOrthogonal.abs_matMulVec_le_card_infNormVec`, `row_sum_le_infNorm` | Exact matrix reasoning. `frobNorm` and `infNorm` are compatibility wrappers over Mathlib norms for legacy function-shaped matrices. |
| Perturbation theory | `LeanFpAnalysis/FP/Analysis/PerturbationTheory.lean` | residual and perturbation quantities | `forward_error_from_residual`, `componentwise_forward_error`, `forward_error_from_backward_error`, `componentwise_forward_error_exact`, `normwise_forward_error_exact` | Converts residual/backward-error hypotheses into forward-error conclusions. |

## Main Dependency Chains

The strongest internally derived results follow these chains:

```text
Model
  -> Rounding
  -> Summation
  -> DotProduct
  -> MatVec
  -> MatMul

Model
  -> Rounding and SubtractionFold
  -> ForwardSub / BackSub
  -> TriangularSolveCombined
  -> LU solve and Cholesky solve

Model
  -> DotProduct
  -> Norm2
  -> future Householder construction/application work

MatrixAlgebra + PerturbationTheory
  -> forward-error and residual-based analyses

MatVec + residual definitions
  -> IterativeRefinement
  -> StationaryIteration-style bounds
```

When a target statement looks like a new algorithm-level stability result,
first identify whether it is:

- a local kernel result, such as summation, dot product, matvec, matmul, or a
  triangular solve;
- a composition result, such as LU solve, Cholesky solve, residual computation,
  or iterative refinement;
- a perturbation conversion, where an existing backward/residual bound needs to
  be converted into a forward-error bound.

## Common Definitions

| Name | Kind | Location | Meaning |
|---|---|---|---|
| `FPModel` | structure | `FP/Model.lean` | Unit roundoff and rounded operations with standard relative-error axioms. |
| `gamma fp n` | definition | `Analysis/Rounding.lean` | Higham `gamma_n = n*u / (1 - n*u)`. |
| `gammaValid fp n` | definition | `Analysis/Rounding.lean` | Side condition `(n : Real) * fp.u < 1`. |
| `fl_dotProduct` | definition | `Algorithms/DotProduct.lean` | Sequential floating-point dot product. |
| `fl_norm2` | definition | `Algorithms/Norm2.lean` | Floating-point Euclidean norm: `fl_sqrt (fl_dotProduct x x)`. |
| `fl_matVec` | definition | `Algorithms/MatVec.lean` | Rowwise floating-point matrix-vector product. |
| `fl_matMul` | definition | `Algorithms/MatMul.lean` | Columnwise matrix-matrix product via `fl_matVec`. |
| `fl_forwardSub` | definition | `Algorithms/ForwardSub.lean` | Floating-point lower-triangular solve. |
| `fl_backSub` | definition | `Algorithms/TriangularSolve.lean` | Floating-point upper-triangular solve. |
| `fl_residual` | definition | `Algorithms/IterativeRefinement.lean` | Floating-point residual `fl(b - fl(A*x))`. |
| `LUBackwardError` | structure | `Algorithms/LU/GaussianElimination.lean` | Backward-error contract for computed LU factors. |
| `CholeskyBackwardError` | structure | `Algorithms/Cholesky/CholeskySpec.lean` | Backward-error contract for computed Cholesky factors. |
| `HouseholderAppError` | structure | `Algorithms/QR/HouseholderSpec.lean` | Backward-error contract for applying a Householder reflector. |
| `HouseholderQRRhsPanelBackwardError` | structure | `Algorithms/QR/QRSolve.lean` | Backward-error contract for the RHS transform in Householder QR solve. |
| `HouseholderQRPanelSolveBackwardError` | structure | `Algorithms/QR/QRSolve.lean` | Shared-orthogonal-factor contract for the QR `R` panel and RHS transform. |
| `QRSolveBackwardError` | structure | `Algorithms/QR/QRSolve.lean` | Backward-error contract for QR-based solve. |
| `SolverSpec` | structure | `Algorithms/IterativeRefinement.lean` | Abstract componentwise backward-stable solver. |
| `ResidualError` | structure | `Algorithms/IterativeRefinement.lean` | Componentwise residual-computation error contract. |

## Strong Results Versus Abstract Interfaces

Many core files derive their results from the floating-point model and earlier
library lemmas. Good examples are:

- `dotProduct_error_bound`
- `dotProduct_backward_error`
- `norm_toLp_two_eq_sqrt_dotProduct`
- `dotProduct_self_pos_iff_real`
- `fl_norm2Sq_backward_error`
- `fl_norm2Sq_nonneg_of_gammaValid_two_mul`
- `fl_norm2_unroll`
- `fl_norm2_unroll_of_gammaValid_two_mul`
- `matVec_backward_error`
- `matMul_error_bound`
- `forwardSub_backward_error`
- `backSub_backward_error`
- `triangularSolve_backward_error`
- `lu_solve_backward_error`
- `cholesky_solve_backward_error`
- `conventional_residual_error`

Some high-level chapter files intentionally expose abstract/specification
interfaces. They are useful when the missing local algorithm analysis is supplied
as a hypothesis, but they should not be read as fully derived from `FPModel`
alone. Inspect their hypotheses before using them as evidence of a completed
floating-point analysis.

Known abstract-interface areas include:

- `Algorithms/GaussJordan.lean`
- parts of `Algorithms/MatrixInversion.lean`
- `Algorithms/Cholesky/CholeskyDemmel.lean`
- `Algorithms/Cholesky/CholeskyIndefinite.lean`
- `Algorithms/Cholesky/CholeskyNonsym.lean`
- `Algorithms/Cholesky/CholeskyPSD.lean`
- `Algorithms/Cholesky/CholeskyPerturbation.lean`
- `Algorithms/QR/HouseholderQR.lean`
- `Algorithms/QR/GivensQR.lean`
- `Algorithms/QR/QRSolve.lean`
- `Algorithms/Sylvester/SylvesterPerturbation.lean`

The safest way to classify a theorem is to inspect the statement. If a
hypothesis already contains the algorithmic stability conclusion, the theorem is
a transfer or packaging result rather than a complete local analysis.

## Search Recipes

Inside the repository:

```bash
rg "theorem .*backward_error" LeanFpAnalysis/FP
rg "theorem .*error_bound" LeanFpAnalysis/FP
rg "def fl_" LeanFpAnalysis/FP
rg "structure .*Spec|structure .*Error" LeanFpAnalysis/FP
```

Inside Lean:

```lean
import LeanFpAnalysis.FP
open LeanFpAnalysis.FP

#check dotProduct_error_bound
#check matVec_backward_error
#check backSub_backward_error
#check lu_solve_backward_error
```

When a theorem almost matches a goal, compare:

- dimension order, such as `m n p` versus `n m`;
- whether the theorem is componentwise, normwise, or residual-based;
- whether the result is forward error or backward error;
- whether the bound is `gamma fp n`, `gamma fp (n + 1)`, or an absorbed form;
- whether the theorem perturbs one input, one row/column, or a whole matrix;
- whether the theorem requires triangular zero-pattern assumptions, nonzero
  diagonal assumptions, or an abstract factorization/solver specification.
