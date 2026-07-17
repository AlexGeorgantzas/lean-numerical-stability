# Higham Chapter 23 Formalization Report

## Outcome

The selected-scope gate is **FAIL** after re-auditing the recursively rounded
claims against pp. 440 and 442--443.  The actual one-level algorithms and
several rounded nonrecursive analyses are proved; Miller's result and
Theorems 23.2--23.4 are not.

## Proved source-facing work

| Source | Lean surface | Result |
|---|---|---|
| (23.2) | paired Winograd finite-sum identity | exact algebra proved |
| (23.3)--(23.4) | `Higham23Block2`, `higham23Strassen2` | exact seven-product correctness proved |
| (23.5) | executable Strassen cost recurrence | printed multiplication/addition counts proved |
| (23.6) | `higham23WinogradStrassen2` | exact 15-addition correctness proved |
| (23.7a)--(23.7b) | exact bilinear product/evaluator | source equations and one-level correctness predicate proved |
| (23.8)--(23.9) | `higham23ThreeM` | exact three-real-product identity proved |
| (23.10), (23.17) | actual rounded conventional matrix multiplication | componentwise/max-entry bounds with quadratic remainder proved |
| Theorem 23.1 / (23.12) | actual rounded Winograd inner product | printed error bound and balancing theorem proved |
| (23.16), recurrence after (23.18) | canonical scalar coefficient recurrences | 12/46 and 18/89 arithmetic and closed upper coefficients proved |
| (23.20)--(23.24) | actual rounded conventional and 3M complex paths | componentwise, scaling, and induced-infinity bounds proved |

## Open selected work

| Source | Bottleneck |
|---|---|
| (23.11) | Miller's cited polynomial-algorithm theorem and `f_n` |
| Theorem 23.2 / (23.14)--(23.15) | recursively rounded Strassen evaluator and operation-level induction |
| Theorem 23.3 / (23.18) | recursively rounded Winograd--Strassen evaluator and induction |
| Theorem 23.4 / (23.19) | cited Bini--Lotti constants/theorem and rounded recursive bilinear evaluator |
| 23.B3 / Problem 23.6 | combined rounded 3M--Strassen path |

## Audit correction

The previous report called these rows `PASS (EXPLICIT-DOMAIN)`.  The shared
first-order structure already required the missing expansion and its
nonemptiness witnesses used synthetic exact/zero-error computations rather
than recursive Strassen, Winograd--Strassen, or bilinear evaluation.
Likewise, support-count-plus-one values were not the external Bini--Lotti
constants.  Those structures, producers, theorem-shaped consequences, and
witnesses were removed.

The retained `higham23BiniLottiCoefficient` now takes `alpha` and `beta`
as parameters and represents only the algebraic coefficient shape.
`higham23ThreeMStrassenCoefficient` is likewise documented as a scalar
identity, not a combined error theorem.

## Verification

- `lake env lean LeanFpAnalysis/FP/Algorithms/FastMatMul/Higham23.lean`:
  PASS after the audit correction.
- The module contains no `sorry`, `admit`, `axiom`, `unsafe`,
  `opaque`, `Higham23FirstOrderExpansion`, synthetic nonempty producer,
  or `*_explicitDomain` theorem.
- Source formulas were checked against rendered pp. 438, 440, 442, and 443.

See the inventory and not-proved ledger for row-level status.
