# Benchmark Task Derivation

Draft status: benchmark-source material.  Do not copy this file into generated
solver workspaces.

Important benchmark-design status: this document describes the current
prototype task set, not the final thesis task set.  The current set is too
Higham-centered.  Since much of LeanFpAnalysis formalizes Higham-style
material, a final benchmark must include tasks sourced from other numerical
analysis references and software specifications.  Otherwise Condition C may be
measuring access to a formalized book more than transfer to new stability
analyses.

See `benchmark/tasks/TASK_SOURCE_STRATEGY.md` for the source-diversification
rule that should govern the final task set.

This file records where each benchmark theorem comes from.  A task source is
not valid unless it identifies both:

- the numerical-analysis source for the algorithmic stability pattern; and
- the exact LeanFpAnalysis definition/theorem chain that justifies the formal
  bound used in the solver-facing task.

The tasks are sorted by intended composition depth, not by observed solver
runtime.  A late task can be fast in Condition C if the solver finds the right
library interface, and an early task can be slow if it tries to rederive
low-level rounding lemmas.

## Primary References

The main external reference is:

Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
SIAM, 2002.  The repository contains the local reference PDFs under
`References/`.

The benchmark uses these exact anchors:

| Source anchor | Local PDF | Use in tasks |
| --- | --- | --- |
| Higham equation (1.1) | `References/HighamBook.pdf` | Standard model for one rounded arithmetic operation. |
| Higham Lemma 3.1 | `References/Chapter03.pdf` | Product of elementary rounding factors and the `gamma` bound. |
| Higham equations (3.3)-(3.5) | `References/Chapter03.pdf` | Inner-product backward and forward error. |
| Higham Lemma 3.3 | `References/Chapter03.pdf` | Algebraic rules for combining `gamma` terms. |
| Higham equations (3.10)-(3.11) | `References/Chapter03.pdf` | Matrix-vector backward and forward error from row inner products. |
| Higham Algorithm 8.1 and Theorem 8.5 | `References/Chapter08.pdf` | Back substitution and triangular-solve backward error; forward substitution is the stated analogue. |
| Higham Corollary 8.6 | `References/Chapter08.pdf` | Combined triangular solve perturbation. |
| Higham Theorems 9.3 and 9.4 | `References/Chapter09.pdf` | LU factorization and solve backward error. |
| Higham Theorems 10.3 and 10.4 | `References/Chapter10.pdf` | Cholesky factorization and solve backward error. |
| Higham equations (11.5)-(11.7), Theorems 11.3-11.4 | `References/Chapter11.pdf` | Iterative-refinement solver/residual model and one-step stability. |
| Higham equations (16.1), (16.18), and (16.19) | `References/Chapter16.pdf` | Stationary iteration with local errors and normwise residual bound. |
| BLAS `DGEMV` operation | Netlib/LAPACK `dgemv` documentation: <https://www.netlib.org/lapack/explore-html/d7/dda/group__gemv_ga4ac1b675072d18f902db8a310784d802.html> | GEMV algorithm shape `y := alpha*A*x + beta*y`. |

For public web pointers to the book chapters, use SIAM's chapter landing pages.
The local PDFs above are the precise sources used for equation/theorem
numbering.

## Local Lean Source Anchors

The exact formal definitions and theorem names are the primary machine-checkable
sources for the benchmark bounds:

| Concept | Lean anchor |
| --- | --- |
| FP model | `LeanFpAnalysis/FP/Model.lean`, `FPModel`, especially `model_add`, `model_sub`, `model_mul`, `model_div` |
| `gamma` and validity guard | `LeanFpAnalysis/FP/Analysis/Rounding.lean`, `gamma`, `gammaValid` |
| Gamma algebra | `Rounding.lean`, `u_le_gamma`, `gamma_mono`, `gamma_mul`, `gamma_sum_le`, `gamma_add_u_le`, `three_gamma_plus_sq_le_gamma` |
| Dot product | `LeanFpAnalysis/FP/Algorithms/DotProduct.lean`, `fl_dotProduct`, `dotProduct_error_bound`, `dotProduct_backward_error`, `dotProduct_backward_stable_x` |
| Matrix-vector product | `LeanFpAnalysis/FP/Algorithms/MatVec.lean`, `fl_matVec`, `matVec_backward_error`, `matVec_error_bound` |
| Residual computation | `LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean`, `fl_residual`, `conventional_residual_error` |
| Forward substitution | `LeanFpAnalysis/FP/Algorithms/ForwardSub.lean`, `fl_forwardSub`, `forwardSub_backward_error` |
| Back substitution | `LeanFpAnalysis/FP/Algorithms/TriangularSolve.lean`, `fl_backSub`, `backSub_backward_error` |
| Combined triangular solve | `LeanFpAnalysis/FP/Algorithms/TriangularSolveCombined.lean`, `triangularSolve_backward_error` |
| LU factorization/solve | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`, `LUBackwardError`; `LeanFpAnalysis/FP/Algorithms/LU/LUSolve.lean`, `lu_solve_backward_error`; `LeanFpAnalysis/FP/Algorithms/LU/Tridiagonal.lean`, `banded_lu_solve_backward_stable` |
| Cholesky factorization/solve | `LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskySpec.lean`, `CholeskyBackwardError`; `LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskySolve.lean`, `cholesky_solve_backward_error` |
| Iterative refinement | `IterativeRefinement.lean`, `one_step_refinement_error_identity`, `one_step_residual_bound` |
| Stationary iteration | `LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean`, `ComputedIteration`, `one_step_residual`, `normwise_residual_bound` |

## Composition Ladder

| Task | Depth | Source status | Bound origin |
| --- | ---: | --- | --- |
| T01 Scaled dot | 1 | Derived from exact inner-product source plus one FP multiplication. | `dotProduct_backward_error` plus `FPModel.model_mul`, absorbed to `gamma (n + 1)` by gamma algebra. |
| T02 Shifted dot | 1 | Derived from exact inner-product source plus one FP addition. | `dotProduct_error_bound` plus `FPModel.model_add`, absorbed to `gamma (n + 1)`. |
| T03 Residual certificate | 2 | Derived certificate from conventional residual source. | `conventional_residual_error` plus triangle inequality and computed-residual hypothesis. |
| T04 Forward-sub residual | 2 | Direct consequence of triangular-solve backward error. | `forwardSub_backward_error` implies the residual bound for the original `L`. |
| T05 GEMV | 2 | BLAS algorithm shape plus derived matrix-vector composition. | `matVec_backward_error` plus two scalar multiplications and one addition, absorbed to `gamma (n + 2)`. |
| T06 Single perturbation for triangular pair | 3 | Direct composition of triangular-solve perturbations. | `triangularSolve_backward_error` packaged as one perturbation of `A = L*U`; coefficient `2*gamma n + gamma n^2`. |
| T07 LU growth-scaled solve | 3 | Higham LU solve bound with task-local growth conversion. | `lu_solve_backward_error` plus `|Lhat||Uhat| <= rho|A|`; coefficient `(3*gamma n + gamma n^2)*rho`. |
| T08 Cholesky growth-scaled solve | 3 | Higham Cholesky solve bound with task-local growth conversion. | `cholesky_solve_backward_error` plus `|Rhat^T||Rhat| <= rho|A|`; coefficient `gamma (3*n + 1)*rho`. |
| T09 One-step refinement | 4 | Derived one-step residual theorem specialized to conventional residual computation. | correction-solve backward error plus `conventional_residual_error`; bound has `mu|A||dhat| + gamma(n+1)(|b|+|A||x0|)`. |
| T10 Stationary forward-sub iteration | 4 | Bridge from concrete triangular local solve to abstract stationary-iteration residual theorem. | `forwardSub_backward_error` supplies local error; `normwise_residual_bound` supplies the final residual recurrence bound. |

The depth number is a design label: it counts how many stability-analysis
interfaces must be combined.  It is not a theorem about solver time.

## Per-Task Derivations

### T01 Scaled Dot Product

Solver-facing theorem:
`benchmark/tasks/T01_ScaledDot/Task.lean`, `scaledDot_backward_error`.

Algorithm:
`fl_scaledDot fp n alpha x y = fp.fl_mul alpha (fl_dotProduct fp n x y)`.

Exact sources:

- Higham equation (1.1), for the single rounded multiplication.
- Higham equations (3.3)-(3.5), for the inner-product error model.
- Higham Lemma 3.3, for combining the dot-product error with the scalar
  multiplication error.
- Lean: `dotProduct_backward_error`, `FPModel.model_mul`, `u_le_gamma`,
  `gamma_mul`, and `gamma_mono`.

Bound derivation:
`dotProduct_backward_error` gives perturbations of the dot-product terms
bounded by `gamma fp n`.  `FPModel.model_mul` gives one additional relative
error bounded by `u`, and `u <= gamma fp 1`.  The product of these two
relative-error factors is absorbed by `gamma_mul` into `gamma fp (n + 1)`.

Status:
derived, not a verbatim textbook theorem.

### T02 Shifted Dot Product

Solver-facing theorem:
`benchmark/tasks/T02_ShiftedDot/Task.lean`, `shiftedDot_forward_error`.

Algorithm:
`fl_shiftedDot fp n c x y = fp.fl_add c (fl_dotProduct fp n x y)`.

Exact sources:

- Higham equation (1.1), for the single rounded addition.
- Higham equation (3.5), for the forward inner-product bound.
- Higham Lemma 3.3, for absorbing the extra rounding step.
- Lean: `dotProduct_error_bound`, `FPModel.model_add`,
  `gamma_add_u_le`, `gamma_sum_le`, and `gamma_mono`.

Bound derivation:
`dotProduct_error_bound` controls
`fl_dotProduct - sum_i x_i*y_i` by `gamma fp n * sum_i |x_i||y_i|`.
The rounded addition contributes a term bounded by `u` times the magnitude of
the shifted exact quantity.  The task target charges this through
`|c| + sum_i |x_i||y_i|` and uses gamma absorption to state the result with
`gamma fp (n + 1)`.

Status:
derived, not a verbatim textbook theorem.

### T03 Residual Stopping Certificate

Solver-facing theorem:
`benchmark/tasks/T03_ResidualCertificate/Task.lean`,
`residual_stopping_certificate`.

Algorithm:
`fl_residual fp n A x b`, conventional residual computation.

Exact sources:

- Higham equations (11.6)-(11.7), conventional residual computation error in
  iterative refinement.
- Higham equations (3.10)-(3.11), matrix-vector error used inside the residual
  computation.
- Lean: `fl_residual`, `conventional_residual_error`,
  `matVec_backward_error`, and `FPModel.model_sub`.

Bound derivation:
`conventional_residual_error` bounds the distance between the computed
residual and the exact residual.  The task adds a certificate hypothesis
`|fl_residual ... i| <= tau i`.  The exact residual bound follows by the
triangle inequality:
`|r_i| <= |rhat_i| + |rhat_i - r_i|`.

Status:
derived certificate from a textbook residual-error source.

### T04 Forward-Substitution Residual Certificate

Solver-facing theorem:
`benchmark/tasks/T04_ForwardSubResidual/Task.lean`,
`forwardSub_residual_certificate`.

Algorithm:
`fl_forwardSub fp n L b`.

Exact sources:

- Higham Algorithm 8.1 for back substitution; the text explicitly states the
  analogous forward-substitution case.
- Higham Theorem 8.5, triangular substitution backward error.
- Lean: `fl_forwardSub` and `forwardSub_backward_error`.

Bound derivation:
`forwardSub_backward_error` provides a perturbation `DeltaL` such that
`(L + DeltaL)xhat = b` and
`|DeltaL_ij| <= gamma fp n * |L_ij|`.  Rearranging gives
`b - L*xhat = DeltaL*xhat`, and the componentwise residual bound follows by
triangle inequality.

Status:
direct consequence of a formalized Higham-style theorem.

### T05 BLAS GEMV Backward Stability

Solver-facing theorem:
`benchmark/tasks/T05_Gemv/Task.lean`, `gemv_backward_error`.

Algorithm:
`fl_gemv fp m n alpha beta A x y i =
fp.fl_add (fp.fl_mul alpha (fl_matVec fp m n A x i))
          (fp.fl_mul beta (y i))`.

Exact sources:

- Netlib/LAPACK `DGEMV`: generalized matrix-vector operation
  `y := alpha*A*x + beta*y`.
- Higham equations (3.10)-(3.11), rowwise matrix-vector error.
- Higham equation (1.1), for the scalar multiplications and final addition.
- Higham Lemma 3.3, for absorbing the extra rounded operations.
- Lean: `fl_matVec`, `matVec_backward_error`, `FPModel.model_mul`,
  `FPModel.model_add`, `gamma_mul`, `gamma_sum_le`, and `gamma_mono`.

Bound derivation:
`matVec_backward_error` gives a rowwise perturbation `DeltaA` bounded by
`gamma fp n * |A|`.  The multiplication by `alpha`, multiplication by `beta`,
and final addition each come from `FPModel`.  The task packages these scalar
rounding effects as perturbations of `A` and `y` and absorbs the total budget
into `gamma fp (n + 2)`.

Status:
derived BLAS-kernel task.  The algorithm shape is standard BLAS; the exact
formal bound is a benchmark-specific composition.

### T06 Combined Triangular Solve As One Backward Error

Solver-facing theorem:
`benchmark/tasks/T06_TriangularSolveSingle/Task.lean`,
`triangularSolve_single_backward_error`.

Algorithm:
forward substitution with `L`, then back substitution with `U`.

Exact sources:

- Higham Theorem 8.5, triangular solve backward error.
- Higham Corollary 8.6, combined triangular solve perturbation.
- Lean: `fl_forwardSub`, `fl_backSub`, `forwardSub_backward_error`,
  `backSub_backward_error`, and `triangularSolve_backward_error`.

Bound derivation:
The two triangular solves provide perturbations `DeltaL` and `DeltaU`.
Expanding `(L + DeltaL)(U + DeltaU)` gives one perturbation of `L*U`:
`L*DeltaU + DeltaL*U + DeltaL*DeltaU`.  The coefficient is therefore
`2*gamma fp n + gamma fp n^2`, exactly matching
`triangularSolve_backward_error`.

Status:
direct formal composition already present in the library, restated as a
benchmark theorem.

### T07 LU Solve With Growth-Scaled Backward Error

Solver-facing theorem:
`benchmark/tasks/T07_LUSolveGrowth/Task.lean`,
`lu_solve_growth_backward_error`.

Algorithm:
solve using computed factors `Lhat` and `Uhat`.

Exact sources:

- Higham Theorem 9.3, LU factorization backward error.
- Higham Theorem 9.4, LU solve backward error.
- Lean: `LUBackwardError`, `lu_solve_backward_error`,
  `banded_lu_solve_backward_stable`, `forwardSub_backward_error`, and
  `backSub_backward_error`.

Bound derivation:
`lu_solve_backward_error` gives a perturbation `DeltaA` satisfying
`(A + DeltaA)xhat = b` and
`|DeltaA| <= (3*gamma fp n + gamma fp n^2) * |Lhat||Uhat|`.
The task-local growth assumption
`|Lhat||Uhat| <= rho * |A|` converts this into the target relative bound
`((3*gamma fp n + gamma fp n^2) * rho) * |A|`.
The Condition C proof uses the library wrapper
`banded_lu_solve_backward_stable`, which is exactly this growth conversion.

Status:
textbook theorem plus task-local growth conversion.

### T08 Cholesky Solve With Growth-Scaled Backward Error

Solver-facing theorem:
`benchmark/tasks/T08_CholeskySolveGrowth/Task.lean`,
`cholesky_solve_growth_backward_error`.

Algorithm:
solve `Rhat^T y = b`, then `Rhat x = y`.

Exact sources:

- Higham Theorem 10.3, Cholesky factorization backward error.
- Higham Theorem 10.4, Cholesky solve backward error.
- Lean: `CholeskyBackwardError`,
  `cholesky_solve_backward_error_expanded`, and
  `cholesky_solve_backward_error`.

Bound derivation:
`cholesky_solve_backward_error` gives
`|DeltaA| <= gamma fp (3*n + 1) * |Rhat^T||Rhat|`.  The task-local growth
assumption
`sum_k |Rhat k i|*|Rhat k j| <= rho * |A i j|`
turns this into the target bound
`gamma fp (3*n + 1) * rho * |A i j|`.

Status:
textbook theorem plus task-local growth conversion.

### T09 One-Step Refinement With Conventional Residual

Solver-facing theorem:
`benchmark/tasks/T09_OneStepRefinement/Task.lean`,
`one_step_refinement_conventional_residual`.

Algorithm:
compute a conventional residual at `x0`, solve a correction equation
approximately, and update `x1 = x0 + dhat`.

Exact sources:

- Higham equations (11.5)-(11.7), solver and residual-error hypotheses for
  iterative refinement.
- Higham Theorems 11.3-11.4, one-step refinement stability.
- Lean: `fl_residual`, `conventional_residual_error`,
  `one_step_refinement_error_identity`, and `one_step_residual_bound`.

Bound derivation:
The task assumes a correction solve backward error
`(A + DeltaA)dhat = fl_residual fp n A x0 b` with
`|DeltaA| <= mu*|A|`.  `conventional_residual_error` bounds the difference
between the computed residual and the exact residual at `x0`.  The one-step
identity for `x1 = x0 + dhat` gives the target residual bound as the sum of
the correction-solve perturbation term and the residual-computation term.

Status:
derived specialization of the library's iterative-refinement framework.

### T10 Stationary Iteration With Inexact Triangular Local Solve

Solver-facing theorem:
`benchmark/tasks/T10_StationaryForwardSub/Task.lean`,
`stationary_forwardSub_residual_bound`.

Algorithm:
stationary iteration `M x_{k+1} = N x_k + b` where each local solve with
`M` is performed by floating-point forward substitution.

Exact sources:

- Higham equation (16.1), computed stationary iteration with local errors.
- Higham equation (16.18), residual recurrence.
- Higham equation (16.19), normwise residual bound.
- Higham Theorem 8.5, for the local triangular solve error.
- Lean: `ComputedIteration`, `forwardSub_backward_error`,
  `one_step_residual`, `normwise_one_step_residual_bound`, and
  `normwise_residual_bound`.

Bound derivation:
`forwardSub_backward_error` supplies a local residual/error vector for each
step.  The task hypothesis `hlocal` packages those local errors by an infinity
norm bound `mu`.  The abstract stationary-iteration theorem
`normwise_residual_bound` then gives the target
`q^(m+1)*||r0||_inf + mu*||I-H||_inf/(1-q)` residual estimate.

Status:
bridge task from a concrete floating-point triangular solve to an abstract
stationary-iteration residual theorem.

## Contamination Notes

These task statements should not be treated as copied textbook exercises.  The
book supplies the stability-analysis patterns and constants.  The exact Lean
targets are mostly library-composition tasks designed for this benchmark.

For thesis reporting, cite:

- the external theorem/equation number listed above;
- the local Lean theorem(s) used as formal source anchors; and
- this document's per-task derivation explaining the extra composition step.
