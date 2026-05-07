# External Stability Task Derivation

Draft status: benchmark-source material. Do not copy this file into generated
solver workspaces.

This file records the first external-source stability-only pilot tasks.  Each
task conclusion is a stability bound: backward compatibility, forward error, or
an error-bound certificate for a computed residual.  None of these tasks should
assume the same final error bound that it asks the solver to prove.

## E01: LAPACK/Oettli-Prager Backward Certificate

Solver-facing file:
`benchmark/tasks/E01_LapackBerrBackward/Task.lean`

Source anchors:

- LAPACK Users' Guide, "Further Details: Error Bounds for Linear Equation
  Solving": <https://www.netlib.org/lapack/lug/node81.html>.
- Oettli and Prager, "Compatibility of Approximate Solution of Linear
  Equations with Given Error Bounds for Coefficients and Right-Hand Sides",
  Numerische Mathematik 6, 405-409, 1964:
  <https://eudml.org/doc/131627>.

Source theorem pattern:

LAPACK describes the componentwise backward error of a computed solution
`xhat` as the smallest entrywise relative perturbation level for which
`(A + E)xhat = b + f`.  It gives the residual formula

```text
omega_c = max_i |r_i| / ((|A| |xhat| + |b|)_i)
```

with `r = b - A*xhat`, and states that `BERR` is this backward-error measure.

Lean task shape:

The task uses the computed residual `fl_residual fp n A x b`.  Because LAPACK's
formula is stated for the exact residual, the theorem charges the additional
floating-point residual-computation error using the existing library theorem
`conventional_residual_error`.  The conclusion is:

```text
exists DeltaA, Deltab,
  |DeltaA_ij| <= eta |A_ij|,
  |Deltab_i| <= eta |b_i|,
  (A + DeltaA)x = b + Deltab.
```

Why this is a stability proof:

It proves componentwise backward stability of an approximate solution
certificate.  The conclusion is not a restatement of the hypothesis; the
hypothesis is a computable residual certificate, while the conclusion is
existence of a nearby exact linear system.

## E02: Netlib Templates Residual Stopping Criterion

Solver-facing file:
`benchmark/tasks/E02_TemplatesResidualStop/Task.lean`

Source anchor:

- Netlib Templates, "Stopping Criteria":
  <https://netlib.org/linalg/old_html_templates/section2.8.2.html>.

Source theorem pattern:

The Templates stopping-criteria section explains that if an estimate involving
`A^{-1}` is available, a residual-based stopping test can guarantee that the
relative error in the computed solution is bounded by the user-supplied
`stop_tol`.

Lean task shape:

The task uses the computed residual and an explicit residual allowance

```text
|fl_residual_i| + gamma_{n+1} (|b_i| + sum_j |A_ij| |xhat_j|)
```

to cover both the observed residual and the error of computing that residual in
floating-point arithmetic.  The stopping hypothesis is

```text
||A^{-1}||_inf * residualTol <= stopTol * ||xhat||_inf.
```

The conclusion is

```text
||x - xhat||_inf <= stopTol * ||xhat||_inf.
```

Why this is a stability proof:

It proves a forward-error guarantee from a computed residual stopping
certificate.  The result is about the accuracy of an approximate solution of
`Ax=b`, not merely algebraic rewriting.

## E03: LAPACK FERR-Style Forward Error Bound

Solver-facing file:
`benchmark/tasks/E03_LapackFerrForward/Task.lean`

Source anchor:

- LAPACK Users' Guide, "Further Details: Error Bounds for Linear Equation
  Solving": <https://www.netlib.org/lapack/lug/node81.html>.

Source theorem pattern:

LAPACK describes `FERR` as a forward-error bound computed from a vector formed
by applying an estimate of `|A^{-1}|` to the computed residual plus a residual
rounding allowance.

Lean task shape:

The task defines a LAPACK-style numerator

```text
|A^{-1}| ( |fl_residual| + gamma_{n+1} (|b| + |A| |xhat|) )
```

and asks the solver to prove

```text
||x - xhat||_inf / ||xhat||_inf
  <= lapackFerrBound fp n A A_inv xhat b.
```

Why this is a stability proof:

It proves a forward-error bound for a computed approximate solution using the
same information LAPACK uses for `FERR`: a computed residual, a residual-error
allowance, and inverse-magnitude information.

## E04: LAPACK Level 3 Matrix Multiplication Bound

Solver-facing file:
`benchmark/tasks/E04_LapackLevel3Matmul/Task.lean`

Source anchor:

- LAPACK Users' Guide, "Error Bounds for Fast Level 3 BLAS":
  <https://www.netlib.org/lapack/lug/node108.html>.

Source theorem pattern:

LAPACK states that for a computed matrix product `Chat` approximating `A*B`,
a stable Level 3 BLAS implementation should satisfy an infinity-norm forward
error bound of the form

```text
||Chat - A*B||_inf <= c1(m,n,p) eps ||A||_inf ||B||_inf + O(eps^2).
```

Lean task shape:

The task specializes the source pattern to the conventional dot-product based
matrix product already modeled by `fl_matMul`.  The source's first-order
constant is represented by the library's `gamma fp n`, so the conclusion is a
gamma-version of the same normwise stability contract:

```text
||fl_matMul(A,B) - A*B||_inf
  <= gamma_n ||A||_inf ||B||_inf.
```

Why this is a stability proof:

It proves a forward-error bound for a concrete computed matrix multiplication
algorithm.  The task does not assume an entrywise or normwise matrix-product
error bound; it is expected to derive it from the row/column dot-product
analysis exposed by the library.

## E05: LAPACK Level 3 Triangular Solve Residual Bound

Solver-facing file:
`benchmark/tasks/E05_LapackTriangularResidual/Task.lean`

Source anchor:

- LAPACK Users' Guide, "Error Bounds for Fast Level 3 BLAS":
  <https://www.netlib.org/lapack/lug/node108.html>.

Source theorem pattern:

LAPACK states that a computed solution `Xhat` of triangular systems `T X = B`
should satisfy a residual bound of the form

```text
||T Xhat - B||_inf <= c2(m,p) eps ||T||_inf ||Xhat||_inf + O(eps^2).
```

Lean task shape:

The task specializes to one right-hand side and the library's modeled
back-substitution algorithm:

```text
||U*xhat - b||_inf <= gamma_n ||U||_inf ||xhat||_inf.
```

Why this is a stability proof:

It proves a residual-error guarantee for a computed triangular solve.  The
source statement is normwise; the Lean proof is expected to unpack the
componentwise triangular backward-error theorem and convert it to the normwise
residual bound.

## E06: Oettli-Prager Backward-To-Forward Error Conversion

Solver-facing file:
`benchmark/tasks/E06_OettliPragerForward/Task.lean`

Source anchors:

- Oettli and Prager, "Compatibility of Approximate Solution of Linear
  Equations with Given Error Bounds for Coefficients and Right-Hand Sides",
  Numerische Mathematik 6, 405-409, 1964:
  <https://eudml.org/doc/131627>.
- LAPACK Users' Guide, "Further Details: Error Bounds for Linear Equation
  Solving": <https://www.netlib.org/lapack/lug/node81.html>.

Source theorem pattern:

Oettli-Prager gives the compatibility interpretation of an approximate
solution under componentwise coefficient and right-hand-side perturbations.
LAPACK then describes the associated componentwise condition measure and a
forward-error bound obtained from the backward-error level.

Lean task shape:

The task starts from the existence of componentwise perturbations
`DeltaA, Deltab` for which `(A+DeltaA)xhat=b+Deltab`, and proves the explicit
componentwise forward-error consequence

```text
|x_i - xhat_i|
  <= eta * sum_j |A_inv_ij| (sum_k |A_jk| |xhat_k| + |b_j|).
```

Why this is a stability proof:

It is a stability-conversion theorem.  The hypothesis is a backward-error
certificate; the conclusion is a forward-error bound for the approximate
solution.

## E07: Netlib Templates Stationary-Iteration Residual Bound

Solver-facing file:
`benchmark/tasks/E07_TemplatesStationaryResidual/Task.lean`

Source anchors:

- Netlib Templates, "Stationary Iterative Methods":
  <https://www.netlib.org/templates/templates.html>.
- Netlib Templates, "Stopping Criteria":
  <https://netlib.org/linalg/old_html_templates/section2.8.2.html>.

Source theorem pattern:

Netlib Templates treats stationary iterations as successive approximations to
`Ax=b` and emphasizes residual-based convergence/stopping criteria.  For a
splitting `A = M - N`, the standard residual analysis uses the iteration matrix
and an inexact-step term to bound residual decay.

Lean task shape:

The task defines a concrete local error

```text
xi_k = M*xhat_{k+1} - (N*xhat_k + b)
```

and assumes this local computed-step error has norm at most `mu`.  The theorem
then proves the residual recurrence unrolled for `m+1` steps:

```text
||r_{m+1}||_inf
  <= q^(m+1) ||r_0||_inf
     + mu ||I-H||_inf / (1-q).
```

Why this is a stability proof:

It proves a residual-error bound for an inexact stationary iteration.  The
conclusion is not a pure convergence statement; the `xi` term models local
computed-step error, and the solver must bridge the task-local error
definition to the library's abstract `ComputedIteration` contract.

## E08: LAPACK Least-Squares QR Forward-Error Certificate

Solver-facing file:
`benchmark/tasks/E08_LapackLSQRForward/Task.lean`

Source anchors:

- LAPACK Users' Guide, "Error Bounds for Linear Least Squares Problems":
  <https://www.netlib.org/lapack/lug/node82.html>.
- LAPACK Users' Guide, "Further Details: Error Bounds for Linear Least Squares
  Problems": <https://www.netlib.org/lapack/lug/node83.html>.
- Björck, "The Calculation of Linear Least Squares Problems", Acta Numerica
  2004: <https://www.cambridge.org/core/journals/acta-numerica/article/calculation-of-linear-least-squares-problems/BA6F7F3457DA9172A313452C85E4702E>.

Source theorem pattern:

LAPACK states that QR-based least-squares drivers compute a solution with a
small normwise backward error.  Björck surveys perturbation and backward-error
bounds for least-squares problems.

Lean task shape:

The task uses the library's `LSQRSolveBackwardError` Gram-system perturbation
certificate for the QR-computed solution.  It asks the solver to extract the
perturbations and prove that those perturbations satisfy the componentwise
forward-error certificate

```text
|xhat_i - x_i|
  <= sum_j |ATA_inv_ij| (sum_k |DeltaG_jk| |xhat_k| + |Deltag_j|).
```

Why this is a stability proof:

It converts a QR least-squares backward-error certificate into an explicit
forward-error certificate for the computed solution.  The theorem is an
abstract/specification-transfer task because full rectangular QR is outside
the current square-matrix core.

## E09: LAPACK Normal-Equations Forward-Error Certificate

Solver-facing file:
`benchmark/tasks/E09_LapackNormalEquations/Task.lean`

Source anchors:

- LAPACK Users' Guide, "Further Details: Error Bounds for Linear Least Squares
  Problems": <https://www.netlib.org/lapack/lug/node83.html>.
- LAPACK Users' Guide, "Error Bounds for Linear Least Squares Problems":
  <https://www.netlib.org/lapack/lug/node82.html>.

Source theorem pattern:

LAPACK's least-squares discussion records the small-backward-error viewpoint
for computed least-squares solutions and highlights the condition-squared term
that appears in least-squares forward-error bounds.  The normal-equations
method exposes this sensitivity through the Gram system `A^T A x = A^T b`.

Lean task shape:

The task assumes explicit relative perturbation bounds for the Gram matrix and
right-hand side, then proves the componentwise forward-error consequence:

```text
|xhat_i - x_i|
  <= sum_j |ATA_inv_ij|
       (epsG * sum_k |ATA_jk| |xhat_k| + epsg * |ATb_j|).
```

Why this is a stability proof:

It is a stability-conversion theorem for the normal-equations algorithmic
path.  It does not assume the final forward-error bound; it derives it from the
perturbed normal equations and relative perturbation hypotheses.

## E10: Ogita-Rump-Oishi SumK Error Certificate

Solver-facing file:
`benchmark/tasks/E10_OgitaSumKCertificate/Task.lean`

Source anchor:

- Ogita, Rump, and Oishi, "Accurate Sum and Dot Product", SIAM J. Sci.
  Comput. 26(6), 1955-1988, 2005, Algorithm 4.8, Lemma 4.9, and Proposition
  4.10, DOI 10.1137/030601818:
  <https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf>.

Source theorem pattern:

The paper's `SumK` algorithm applies repeated error-free vector
transformations and proves an absolute error bound of the form

```text
|res - s| <= (eps + 3 gamma_{n-1}^2) |s| + gamma_{2n-2}^K sum_i |p_i|.
```

Lean task shape:

The task does not formalize IEEE error-free transformations in the public
library.  Instead, it inlines a `SumKDistillationCertificate` containing the
paper's intermediate distillation facts: preservation of the exact sum,
control of the absolute sum after distillation, and the final ordinary
rounding bound.  From those intermediate facts, the theorem asks the solver to
derive the Proposition 4.10-style absolute error bound.

Why this is a stability proof:

It proves an absolute forward-error bound for a compensated summation
certificate.  It is intentionally harder and more paper-specific than the
LAPACK/Netlib tasks.  It should be documented as a certificate-level
formalization, not as a full formalization of `TwoSum`, `VecSum`, and `SumK`
from raw `FPModel`.
