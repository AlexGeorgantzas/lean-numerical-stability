# Condition A Stub Audit

This file records the current audit of
`benchmark/stubs/common/LeanFpAnalysis/FP.lean`.

Condition A is allowed to expose bare definitions and theorem-statement data
types.  It must not expose proved stability theorems, gamma arithmetic lemmas,
lookup documentation, or solver hints.  When a definition appears in
a benchmark theorem target, the stub should preserve the public library meaning
rather than replacing it with a degenerate placeholder.

## Audited Definitions

| Stub item | Public-library source | Status |
| --- | --- | --- |
| `FPModel` | `LeanFpAnalysis/FP/Model.lean` | Bare model fields copied for task statements. |
| `gamma`, `gammaValid` | `LeanFpAnalysis/FP/Analysis/Rounding.lean` | Bare definitions only; no gamma lemmas exposed. |
| `fl_dotProduct` | `LeanFpAnalysis/FP/Algorithms/DotProduct.lean` | Algorithm definition exposed; dot-product theorems omitted. |
| `fl_matVec` | `LeanFpAnalysis/FP/Algorithms/MatVec.lean` | Algorithm definition exposed; matvec theorems omitted. |
| `fl_matMul` | `LeanFpAnalysis/FP/Algorithms/MatMul.lean` | Algorithm definition exposed; matrix-product theorems omitted. |
| `fl_residual` | `LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean` | Algorithm definition exposed; residual theorems omitted. |
| `fl_forwardSub`, `fl_forwardSub_steps` | `LeanFpAnalysis/FP/Algorithms/ForwardSub.lean` | Fold-based algorithm definitions copied. |
| `fl_backSub`, `fl_backSub_steps` | `LeanFpAnalysis/FP/Algorithms/TriangularSolve.lean` | Fold-based algorithm definitions copied. |
| `matMul`, `matMulVec`, `idMatrix`, `matSub_id` | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean` | Bare algebraic definitions exposed; algebra lemmas omitted. |
| `frobNormSq`, `frobNorm` | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean` | Bare norm definitions exposed for least-squares certificates; norm lemmas omitted. |
| `infNormVec`, `infNorm` | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean` | Finite-supremum definitions copied. |
| `IsLeftInverse`, `IsRightInverse`, `IsInverse` | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean` | Predicate definitions copied. |
| `LUBackwardError` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean` | Specification structure exposed; LU theorems omitted. |
| `CholeskyBackwardError` | `LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskySpec.lean` | Specification structure exposed; Cholesky theorems omitted. |
| `SplittingSpec`, `dualIterMatrix`, `ComputedIteration` | `LeanFpAnalysis/FP/Algorithms/StationaryIteration.lean` | Statement-level definitions copied; stationary-iteration theorems omitted. |
| `LSQRSolveBackwardError` | `LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean` | Specification structure exposed; QR least-squares theorems omitted. |

## Fixed Issues

- `infNormVec` and `infNorm` were initially defined as `0`, which made T10
  trivial in Condition A.  They now match the public library definitions.
- `fl_forwardSub` and `fl_backSub` were initially zero-valued placeholders,
  while T04, T06, T07, T08, and T10 mention those algorithms.  They now match
  the public library fold-based definitions.
- The validator now rejects `sorryAx` as a forbidden placeholder, because a T07
  Condition A attempt used `exact sorryAx _ true`.

## Remaining Caveat

This audit checks the shared names used by the prototype `T01`-`T10` tasks and
the external-source pilot `E01`-`E10` tasks as of May 7, 2026.  If new tasks
add more public-library names to Condition A theorem targets, this file and
the common stub must be audited again before the run is treated as an official
benchmark datapoint.
