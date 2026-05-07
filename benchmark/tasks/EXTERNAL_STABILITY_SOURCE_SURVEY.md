# External Stability Source Survey

Draft status: benchmark-design material. Do not copy this file into generated
solver workspaces.

This survey records external source material for benchmark tasks whose target
statements should be traceable to published stability-analysis results rather
than invented for the benchmark.  The goal is to choose tasks whose theorem
statements are as close as possible to a named theorem, equation, or documented
software accuracy contract.

## BLAS DGEMV

BLAS is the Basic Linear Algebra Subprograms interface.  `DGEMV` is the
double-precision general matrix-vector multiply routine.  The name decomposes
as:

- `D`: double precision real arithmetic;
- `GE`: general dense matrix;
- `MV`: matrix-vector operation.

The Netlib BLAS/LAPACK documentation specifies the operation
`y := alpha*A*x + beta*y` and the transpose variant.  This is an algorithm/API
source, not a stability theorem.  A benchmark task using DGEMV therefore still
needs a separate stability-bound source.  Otherwise the task should be labelled
"externally specified algorithm, library-derived bound."

Source:
<https://www.netlib.org/lapack/explore-html/d7/dda/group__gemv.html>

## Source Acceptance Rule

For final benchmark tasks, prefer sources satisfying all of the following:

- the source states an algorithm or computed quantity;
- the source states a stability, residual, backward-error, or forward-error
  bound;
- the Lean theorem can follow the source statement closely, modulo notation
  translation from `epsilon`/`u` to the library's `FPModel` and `gamma`;
- the theorem is not merely a wrapper around an existing Lean theorem with no
  task-local reasoning.

If a source gives only a qualitative statement such as "the algorithm is
stable", it is not enough for a final task unless the benchmark theorem keeps
the source's unspecified constants explicit.

## Strong Candidates Within Current Library Scope

| Candidate | External source anchor | Source theorem/bound shape | Current Lean support | Benchmark suitability |
| --- | --- | --- | --- | --- |
| LAPACK componentwise backward error for linear solves | LAPACK Users' Guide, "Further Details: Error Bounds for Linear Equation Solving": <https://www.netlib.org/lapack/lug/node81.html> | Componentwise backward error `omega_c = max_i |r_i| / ((|A||xhat| + |b|)_i)` and perturbed-system interpretation `(A+E)xhat=b+f`. | `IterativeRefinement.lean`, `PerturbationTheory.lean`, matrix/vector absolute-value infrastructure. | Very strong. This is a real stability-analysis result and can become a residual-to-perturbation task. |
| LAPACK normwise backward/forward error for linear solves | LAPACK Users' Guide, same section plus overview: <https://www.netlib.org/lapack/lug/node80.html> | Normwise backward error from residual, then forward error bounded by backward error times condition number. | `PerturbationTheory.lean`, `IterativeRefinement.lean`, norm infrastructure. | Strong. Good early/mid task if theorem uses explicit condition-number hypotheses. |
| Netlib Templates residual stopping criterion | Netlib Templates stopping criteria: <https://netlib.org/templates/templates.html> and <https://netlib.org/linalg/old_html_templates/section2.8.2.html> | Residual stopping tests of the form `||r|| <= stop_tol * (...)`; with an `A^{-1}` estimate, relative error is bounded by `stop_tol`. | `StationaryIteration.lean`, residual and perturbation theory. | Strong. This is not Higham, is algorithmic, and maps to current residual machinery. |
| LAPACK fast Level 3 BLAS error bounds | LAPACK Users' Guide, "Error Bounds for Fast Level 3 BLAS": <https://www.netlib.org/lapack/lug/node108.html> | Matrix multiplication normwise error `||Chat - AB||_inf <= c1 eps ||A||_inf ||B||_inf + O(eps^2)`; triangular solve residual `||T Xhat - B||_inf <= c2 eps ||T||_inf ||Xhat||_inf + O(eps^2)`. | `MatMul.lean`, `TriangularSolve.lean`, norm lemmas. | Strong if we handle the first-order/O(eps^2) issue honestly, for example by using a stated `c*u` hypothesis or a gamma version justified by the library. |
| Oettli-Prager compatibility theorem | Oettli and Prager, Numerische Mathematik 6, 405-409 (1964): <https://eudml.org/doc/131627> | Approximate solution is compatible with coefficient/RHS error bounds iff a componentwise residual inequality holds. | `PerturbationTheory.lean`, componentwise residual infrastructure. | Very strong conceptually. Need exact source extraction before finalizing theorem text. |
| Björck least-squares perturbation/backward error | Björck, "The Calculation of Linear Least Squares Problems", Acta Numerica 2004; Cambridge excerpt: <https://assets.cambridge.org/97805211/74329/excerpt/9780521174329_excerpt.pdf> | Survey includes optimal LS backward-error formulae and QR residual orthogonality bound `(A+E)^T r=0`, `||E||_2 <= c*u*||A||_2`. | `LeastSquares/LSQRSolve.lean`, `LeastSquares/LSPerturbation.lean`, QR modules. | Good mid/hard candidate. Exact theorem statement should be chosen only after pinning the formula cleanly. |
| Demmel-Dumitriu-Holtz-Kleinberg fast matrix multiplication | "Fast Matrix Multiplication is Stable", Numerische Mathematik 106 (2007): <https://arxiv.org/abs/math/0603207> | Theorem 3.1 gives a maximum-entry norm forward-error bound for bilinear recursive matrix multiplication algorithms. | `FastMatMul.lean`, `MatMul.lean`. | Excellent late task. Hard enough to test navigation and abstraction, while source theorem is explicit. |

Initial external-source pilot tasks:

- `benchmark/tasks/E01_LapackBerrBackward/Task.lean`
- `benchmark/tasks/E02_TemplatesResidualStop/Task.lean`
- `benchmark/tasks/E03_LapackFerrForward/Task.lean`
- `benchmark/tasks/E04_LapackLevel3Matmul/Task.lean`
- `benchmark/tasks/E05_LapackTriangularResidual/Task.lean`
- `benchmark/tasks/E06_OettliPragerForward/Task.lean`
- `benchmark/tasks/E07_TemplatesStationaryResidual/Task.lean`
- `benchmark/tasks/E08_LapackLSQRForward/Task.lean`
- `benchmark/tasks/E09_LapackNormalEquations/Task.lean`
- `benchmark/tasks/E10_OgitaSumKCertificate/Task.lean`

These are documented in `benchmark/tasks/EXTERNAL_TASK_DERIVATION.md`.
They are a source-backed pilot set, not yet a frozen thesis benchmark.  In
particular, E08-E10 include specification-transfer or certificate-level
statements because the public library does not yet formalize full rectangular
QR, IEEE error-free transformations, or paper-specific compensated algorithms.

## Candidates That Need More Library Work

| Candidate | External source anchor | Source theorem/bound shape | Current gap | Benchmark suitability |
| --- | --- | --- | --- | --- |
| Accurate compensated summation/dot product | Ogita, Rump, Oishi, "Accurate Sum and Dot Product", SIAM J. Sci. Comput. 26(6), DOI 10.1137/030601818; public PDF: <https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf> | Error-free transformations, `Sum2`, `SumK`, and dot-product algorithms with K-fold/twice-working-precision quality bounds. | Current library has ordinary sum/dot-product analysis, but not the error-free transformation algorithms. | Good hard/out-of-scope task if we define EFT algorithms locally or extend the library first. |
| Rump computable backward error bounds | Rump, "Computable backward error bounds for basic algorithms in linear algebra", NOLTA 6(3), 360-363 (2015), DOI 10.1587/nolta.6.360; PDF pointer: <https://www.tuhh.de/ti3/paper/rump/Ru14c.pdf> | Replaces standard `gamma_k |R||S|`-style bounds by `k*u |R||S|` for several basic linear algebra algorithms under sharper assumptions. | Current library is gamma-based and intentionally general, not IEEE-specific. | Good thesis discussion or future task, but probably not ideal for the first final benchmark unless we add sharper model assumptions. |
| Sparse backward error for sparse linear systems | Arioli, Demmel, Duff, "Solving Sparse Linear Systems with Sparse Backward Error", SIAM J. Matrix Anal. Appl. 10(2), DOI 10.1137/0610013. | Sparse/componentwise backward-error and iterative-refinement estimates. | Current library does not have sparse matrix patterns or sparse perturbation masks as first-class interfaces. | Strong external task concept, but out of current library scope. |
| Communication-avoiding QR/LU stability | Demmel, Grigori, Hoemmen, Langou, "Communication-optimal parallel and sequential QR and LU factorizations": <https://arxiv.org/abs/0808.2664> | Stability claims for communication-avoiding QR/LU relative to Householder QR or partial-pivoted LU. | Current library has QR/LU abstractions but not CAQR/CALU algorithms. | Good future benchmark family after adding algorithm specs. |
| Goldberg quadratic formula cancellation | Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic": <https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html> | Stable rearrangement of quadratic-root formula to avoid catastrophic cancellation. | Current `FPModel` has no square-root operation and no polynomial-root API. | Useful pedagogical source, but outside current linear-algebra-focused library. |

## Candidate Final Task Direction

The final ten tasks should not be chosen until each theorem statement has an
exact source anchor.  A plausible mixed-source ladder is:

1. LAPACK/Oettli-Prager componentwise residual implies backward perturbation.
2. LAPACK normwise residual implies forward-error bound under a condition
   number hypothesis.
3. Netlib Templates stopping criterion implies a relative forward-error target.
4. LAPACK Level 3 BLAS matrix multiplication normwise error certificate.
5. LAPACK Level 3 BLAS triangular-solve residual certificate.
6. Björck least-squares QR residual orthogonality/backward-error certificate.
7. LAPACK least-squares `ERRBD`-style forward-error theorem.
8. Demmel-Dumitriu-Holtz-Kleinberg fast matrix multiplication stability task.
9. Ogita-Rump-Oishi compensated summation or dot-product task, initially at
   certificate level and later with task-local `TwoSum`/`VecSum` definitions
   if we want a full algorithm proof.
10. Sparse backward-error or communication-avoiding QR/LU task, if we accept
    an out-of-scope hard task or add the required interfaces.

This list deliberately mixes software accuracy documentation, classical
backward-error theory, least-squares analysis, and modern fast-algorithm
stability.  It avoids treating Higham's book as the primary source for most
tasks, although LeanFpAnalysis may still use Higham-style formal infrastructure
to prove the resulting Lean statements.

## Inline Formalization Policy

Paper-specific algorithm definitions should be introduced inside the
solver-facing task file, not in the public library, unless they are intended as
permanent reusable library features.

Reason:

- the task file is copied byte-identically into Condition A and Condition C;
- inline definitions guarantee both conditions prove the same theorem about the
  same algorithm;
- Condition C should benefit from general library infrastructure, not from
  benchmark-specific helpers added immediately before evaluation.

The source survey and task derivation notes may still describe the paper
theorem and its notation, but final tasks should prove stability bounds rather
than assume the paper's final bound as a hypothesis.
