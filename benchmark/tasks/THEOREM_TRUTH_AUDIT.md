# External Task Theorem-Truth Audit

Draft status: benchmark-design material. Do not copy this file into generated
solver workspaces.

This file records a theorem-truth audit for the external-source pilot tasks
`E01`-`E10`.  The goal is to decide whether each task statement is actually
mathematically supported by the current library and source material before
running Codex as the evaluated solver.

This is not a reference-proof file.  It intentionally avoids storing completed
proof scripts for the solver-facing tasks.

## Status Labels

- **Supported**: the theorem appears true and has a plausible proof route from
  existing library results plus ordinary algebra/inequalities.
- **Supported, Bridge**: the theorem appears true and relies on an existing
  library theorem, but it also requires a task-local bridge or certificate
  unpacking step.
- **Certificate-Level**: the theorem appears true from explicitly assumed
  intermediate certificates, but it is not a full derivation from raw
  `FPModel` operations.
- **Needs Revision**: the statement is false, underspecified, or too close to
  assuming its own conclusion.

## Summary

| Task | Status | Main library support | Benchmark concern |
| --- | --- | --- | --- |
| E01 LAPACK `BERR` backward certificate | Supported | `conventional_residual_error`, Oettli-Prager sufficiency | Good candidate. |
| E02 Templates residual stopping | Supported | `conventional_residual_error`, `forward_error_from_residual`, norm bounds | Good candidate. |
| E03 LAPACK `FERR` forward certificate | Supported | `conventional_residual_error`, `forward_error_from_residual`, norm bounds | Good candidate. |
| E04 LAPACK Level 3 matmul | Supported | `matMul_error_bound`, row-sum norm inequalities | Good candidate, gamma-version of source's first-order bound. |
| E05 LAPACK triangular residual | Supported | `backSub_backward_error`, norm inequalities | Good candidate, gamma-version of source's first-order bound. |
| E06 Oettli-Prager forward conversion | Supported | `componentwise_forward_error_standard` | Good stability-conversion task. |
| E07 Templates stationary residual | Supported, Bridge | `normwise_residual_bound` | Builds `ComputedIteration` from a task-local local-error definition. |
| E08 LAPACK LS QR forward certificate | Supported, Bridge | `LSQRSolveBackwardError`, `ls_qr_forward_error` | Specification-transfer task; not full rectangular QR. |
| E09 LAPACK normal equations certificate | Supported | `ls_normal_equations_forward_error` plus perturbation bounds | Reasonable specification-transfer task. |
| E10 Ogita `SumK` certificate | Certificate-Level | certificate assumptions plus gamma/algebra inequalities | Not a full `SumK` algorithm proof. |

## E01: LAPACK/Oettli-Prager Backward Certificate

Statement:
`benchmark/tasks/E01_LapackBerrBackward/Task.lean`

Truth route:

- `conventional_residual_error` bounds the difference between
  `fl_residual fp n A x b i` and the exact residual `b_i - (A*x)_i`.
- The hypothesis bounds
  `|fl_residual_i| + gamma_{n+1} denominator_i` by `eta denominator_i`.
- By the triangle inequality, the exact residual satisfies the
  Oettli-Prager residual inequality with `E = |A|` and `f = |b|`.
- `oettli_prager_sufficient` supplies perturbations `DeltaA`, `Deltab`.

Source match:
LAPACK `BERR` and Oettli-Prager compatibility.

Verdict:
Supported.  This is a good benchmark candidate because it combines computed
residual error with a backward-stability certificate.

## E02: Netlib Templates Residual Stopping Criterion

Statement:
`benchmark/tasks/E02_TemplatesResidualStop/Task.lean`

Truth route:

- Use `conventional_residual_error` to convert the computed residual allowance
  into a bound on the exact residual.
- Use `forward_error_from_residual` with the left inverse `A_inv`.
- Bound `|A_inv| |r|` by `||A_inv||_inf * residualTol`.
- Apply the stopping hypothesis
  `||A_inv||_inf * residualTol <= stopTol * ||xhat||_inf`.

Source match:
Netlib Templates residual stopping criteria with an inverse-norm estimate.

Verdict:
Supported.  This is a good benchmark candidate.

## E03: LAPACK FERR-Style Forward Error Bound

Statement:
`benchmark/tasks/E03_LapackFerrForward/Task.lean`

Truth route:

- Use `conventional_residual_error` to prove each exact residual component is
  bounded by `lapackFerrDenom`.
- Use `forward_error_from_residual` to bound `|x - xhat|` by
  `|A_inv| lapackFerrDenom`.
- Take the infinity norm and divide by the positive
  `||xhat||_inf`.

Source match:
LAPACK `FERR` style: forward error estimated from inverse-magnitude
information and a residual plus residual-rounding allowance.

Verdict:
Supported.  This is a good benchmark candidate.

## E04: LAPACK Level 3 Matrix Multiplication Bound

Statement:
`benchmark/tasks/E04_LapackLevel3Matmul/Task.lean`

Truth route:

- `matMul_error_bound` gives the componentwise matrix-product error:
  `|Chat_ij - (A*B)_ij| <= gamma_n * sum_k |A_ik| |B_kj|`.
- Sum this bound over columns `j`.
- Swap finite sums to get
  `sum_k |A_ik| * sum_j |B_kj|`.
- Bound each row sum of `B` by `rectInfNorm n p B`, then each row sum of `A`
  by `rectInfNorm m n A`.

Source match:
LAPACK Level 3 BLAS infinity-norm forward-error requirement, translated to the
library's gamma model.

Verdict:
Supported.  This is a good benchmark candidate.

## E05: LAPACK Level 3 Triangular Solve Residual Bound

Statement:
`benchmark/tasks/E05_LapackTriangularResidual/Task.lean`

Truth route:

- `backSub_backward_error` gives `DeltaU` with
  `|DeltaU_ij| <= gamma_n |U_ij|` and `(U+DeltaU)xhat = b`.
- Rearranging gives `U*xhat - b = -DeltaU*xhat`.
- Triangle inequality gives the componentwise residual bound
  `|U*xhat - b|_i <= gamma_n * sum_j |U_ij| |xhat_j|`.
- Take `infNormVec` and use row-sum/vector norm bounds.

Source match:
LAPACK Level 3 BLAS triangular-solve residual requirement, translated to the
library's gamma model and one right-hand side.

Verdict:
Supported.  This is a good benchmark candidate.

## E06: Oettli-Prager Backward-To-Forward Error Conversion

Statement:
`benchmark/tasks/E06_OettliPragerForward/Task.lean`

Truth route:

- Unpack `opBackwardCompatible` to obtain `DeltaA`, `Deltab`.
- Apply `componentwise_forward_error_standard` with
  `y = xhat`, `epsilon = eta`, `E = |A|`, and `f = |b|`.

Source match:
Oettli-Prager compatibility plus LAPACK/standard componentwise forward-error
conditioning.

Verdict:
Supported.  This is a good stability-conversion candidate.

## E07: Netlib Templates Stationary-Iteration Residual Bound

Statement:
`benchmark/tasks/E07_TemplatesStationaryResidual/Task.lean`

Truth route:

- Define `xi k = stationaryLocalError n M N b xhat k`.
- Unfolding `stationaryLocalError` proves the abstract
  `ComputedIteration` step equation.
- Apply `normwise_residual_bound` using the hypothesis that the local error
  has norm at most `mu`.

Source match:
Stationary-iteration residual analysis in the style of Netlib Templates.

Verdict:
Supported, Bridge.  The revised statement is no longer a literal theorem
restatement, but it is still close to the stationary-iteration infrastructure.
It is acceptable as a mid-level composition task.

## E08: LAPACK Least-Squares QR Forward-Error Certificate

Statement:
`benchmark/tasks/E08_LapackLSQRForward/Task.lean`

Truth route:

- Unpack `LSQRSolveBackwardError` to obtain perturbations `DeltaG`, `Deltag`,
  the perturbed Gram-system equation, and the certificate bounds.
- Apply `ls_qr_forward_error` to those extracted perturbations.
- Return the perturbations and the explicit componentwise forward-error
  certificate.

Source match:
LAPACK/Björck least-squares perturbation and QR backward-error discussion.

Verdict:
Supported, Bridge.  It is an honest specification-transfer theorem and now
requires certificate unpacking, but it is still not a full rectangular QR
analysis from raw floating-point operations.

## E09: LAPACK Normal-Equations Forward-Error Certificate

Statement:
`benchmark/tasks/E09_LapackNormalEquations/Task.lean`

Truth route:

- `ls_normal_equations_forward_error` gives the componentwise bound involving
  `|DeltaG|` and `|Deltag|`.
- Use the hypotheses
  `|DeltaG_ij| <= epsG |ATA_ij|` and
  `|Deltag_i| <= epsg |ATb_i|`.
- Use nonnegativity of `epsG`, `epsg`, and absolute values to push those bounds
  through finite sums.

Source match:
LAPACK least-squares/normal-equations error-bound discussion, represented as a
perturbed Gram-system certificate.

Verdict:
Supported.  This is a reasonable specification-transfer task and less direct
than E08.

## E10: Ogita-Rump-Oishi SumK Certificate

Statement:
`benchmark/tasks/E10_OgitaSumKCertificate/Task.lean`

Truth route:

- Apply the certificate's final rounding bound:
  `|res - s| <= u |s| + gamma_{n-1}^2 sumAbs(stage(K-2))`.
- Use the certificate's distillation bound at stage `K-2`:
  `sumAbs(stage(K-2)) <= 3 |s| + gamma_{2n-2}^{K-2} sumAbs(p0)`.
- Use the assumptions
  `gamma_{n-1}^2 <= gamma_{2n-2}^2`,
  `0 <= gamma_{2n-2}`, and `0 <= sumAbs(p0)` to absorb
  `gamma_{n-1}^2 * gamma_{2n-2}^{K-2}` into `gamma_{2n-2}^K`.
- Use `3 <= K` for the natural-number stage inequalities.

Source match:
Ogita-Rump-Oishi `SumK` Proposition 4.10, but only after assuming the
intermediate distillation facts that would normally come from `TwoSum` and
`VecSum`.

Verdict:
Certificate-Level.  The theorem appears true, but it should not be advertised
as a full floating-point formalization of `SumK`.  It is a hard algebraic
paper-derived certificate task unless we later inline and analyze the full
error-free-transformation algorithms.

## Recommended Revisions Before Official Runs

1. Keep E01-E09 as serious candidates, with E08 clearly labelled as
   specification-transfer.
2. Keep E10 only if we want one certificate-level hard paper task; otherwise
   replace it with a task whose algorithm is fully modeled in the current
   library.
3. Do not run official Codex attempts until the final task set has no
   unintentional direct wrappers unless they are explicitly designated as
   calibration tasks.
