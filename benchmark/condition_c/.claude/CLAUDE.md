# Benchmark: Condition C — Full Library Access

You are solving floating-point stability analysis exercises in Lean 4. You have full access to the LeanFpAnalysis library, which formalizes Higham's "Accuracy and Stability of Numerical Algorithms."

## Your Task
Each exercise file in `ConditionC/` contains a theorem with `sorry`. Replace the `sorry` with a complete, compiling proof. Do NOT use `sorry` anywhere in your solution. Do NOT weaken the bound — it must match exactly.

## Library Location
The full library is at `../../LeanFpAnalysis/FP/`. You should read and explore these files to find useful lemmas, theorems, and definitions.

## Library Structure

### Core Foundations
- `Model.lean` — `FPModel` structure: axiomatic FP model with `fl_add/sub/mul/div` and `|δ| ≤ u`
- `Analysis/Error.lean` — `absError`, `relError`, `compRelErrorBounded`
- `Analysis/Rounding.lean` — `gamma`, `gammaValid`, `prod_error_bound`, `gamma_mul`, `gamma_mono`, `gamma_inv`
- `Analysis/Summation.lean` — `fl_sum_error`, `fl_sum_error_init`, `fl_sum_error_tight`
- `Analysis/SubtractionFold.lean` — `fl_sub_sum_error_init`, `inv_prod_error_bound`
- `Analysis/Stability.lean` — `backwardErrorBounded`, `isBackwardStable`, `condNumber`, `forward_from_backward`
- `Analysis/ForwardError.lean` — `forward_error_from_backward_componentwise`
- `Analysis/PerturbationTheory.lean` — Rigal-Gaches, Oettli-Prager, Thms 7.2/7.4, `condSkeel_le_kappaInf`
- `Analysis/MatrixAlgebra.lean` — `matMul`, `infNorm`, `frobNorm`, `IsOrthogonal`, Neumann series

### Algorithm Error Bounds
- `Algorithms/DotProduct.lean` — `fl_dotProduct`, `dotProduct_error_bound`, `dotProduct_backward_stable_x`
- `Algorithms/OuterProduct.lean` — `fl_outerProduct`, error bound
- `Algorithms/MatVec.lean` — `fl_matVec`, `matVec_backward_error`, `matVec_error_bound`
- `Algorithms/MatMul.lean` — `fl_matMul`, `matMul_error_bound`, `matMul_backward_error_col`
- `Algorithms/RecursiveSum.lean` — `fl_recursiveSum`, backward/forward error
- `Algorithms/PairwiseSum.lean` — `fl_pairwiseSum`, backward/forward error
- `Algorithms/ForwardSub.lean` — `fl_forwardSub`, `forwardSub_backward_error`
- `Algorithms/TriangularSolve.lean` — `fl_backSub`, `backSub_backward_error`
- `Algorithms/TriangularForwardBound.lean` — forward error bounds for triangular solves
- `Algorithms/LU/GaussianElimination.lean` — LU backward error
- `Algorithms/LU/LUSolve.lean` — `lu_solve_backward_error`
- `Algorithms/Cholesky/CholeskySpec.lean` — Cholesky backward error
- `Algorithms/Cholesky/CholeskySolve.lean` — Cholesky solve backward stability
- `Algorithms/QR/HouseholderQR.lean` — `householder_qr_backward`
- `Algorithms/QR/QRSolve.lean` — QR solve perturbation bound
- `Algorithms/IterativeRefinement.lean` — `linear_contraction`, refinement convergence
- `Algorithms/StationaryIteration.lean` — splitting, forward/backward error
- `Algorithms/CondEstimation.lean` — 1-norm power method
- `Algorithms/FastMatMul.lean` — Strassen/Winograd error

## Key Lean 4 Patterns
- `noncomputable` required on ALL defs over ℝ
- `open scoped BigOperators` required for `∑` notation
- `linarith` does NOT auto-find FPModel struct fields; pass as explicit hints
- `field_simp` needs explicit `≠ 0` hints
- Available: `abs_add_le` (NOT `abs_add`), `pow_le_pow_left₀` (NOT `pow_le_pow_left`)

## Strategy
1. Read the exercise statement carefully
2. Search the library for relevant theorems using Grep/Glob
3. Compose existing lemmas rather than reproving from scratch
4. Use `exact`, `apply`, `have`, `obtain` to chain library results