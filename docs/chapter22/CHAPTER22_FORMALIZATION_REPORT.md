# Higham Chapter 22 Formalization Report

## Outcome

The selected-scope gate is **FAIL** after a source-faithfulness re-audit.
Substantial exact and executable coverage remains, but the cited condition
estimates, the finite triangular factorization, the final solves, and the
rounded forward/residual analyses are not proved.

## Proved source-facing work

| Source | Lean surface | Result |
|---|---|---|
| Vandermonde definition, nonsingularity, (22.1)--(22.3) | Vandermonde adapters, Lagrange/Vieta rows, `higham22_eq22_3` | exact algebra proved |
| Algorithm 22.1 | actual master-product and synthetic-division path | printed coefficient matrix proved equal to `V⁻¹` |
| Confluent example and general prose | displayed matrix plus arbitrary multiplicity model | determinant/injectivity proved |
| Table 22.1 V7 and Table 22.2 | root-unity inverse; five recurrence families | exact rows proved |
| (22.6)--(22.14) | polynomial recurrence, Newton form, sparse coefficient update | exact identities and Stage-II synthesis proved |
| Algorithm 22.2 local path | actual Stage-I recurrence, printed Stage-II recurrence, Newton invariant | genuine partial implementation; no solve claim |
| Algorithm 22.3 local path | literal primal two-stage loop and branch/state equations | genuine partial implementation; no solve claim |
| Algorithm 22.8 / Problem 22.10 | normalized derivative-state loop | end-to-end derivative correctness proved |
| Refinement scalar foundation | `higham22RefinementError` | closed form and convergence proved |

## Open selected work

| Source | Bottleneck |
|---|---|
| Table 22.1 V1--V6 | cited family-specific condition-number estimates |
| Algorithms 22.2--22.3; (22.15)--(22.17) | Stage-I interpolation invariant and finite loop-derived triangular factors with product `P⁻ᵀ` |
| Theorem 22.4; (22.18)--(22.21) | recursively rounded operation path and factor perturbation proof |
| Corollary 22.5; (22.22) | actual checkerboard/no-cancellation specialization |
| Theorem 22.6; (22.23)--(22.25) | actual inverse perturbed factors and conditional residual assembly |
| Corollary 22.7; Problem 22.8 | upper-bidiagonal inverse perturbation proof |
| 22.B2 | solver-specific instantiation of the scalar contraction theorem |

## Audit correction

The previous report counted theorem-shaped domains as terminal
`PASS (EXPLICIT-DOMAIN)`.  Re-reading pp. 422 and 424--426 showed that those
domains contained the missing inverse factorization or first-order expansion,
while their nonempty witnesses used identity or zero computations unrelated
to Algorithms 22.2--22.3.  Those declarations and witnesses were removed.
The public lookup now checks the genuine recurrences and Stage-II synthesis
instead of the deleted transpose-factorization adapter.

All owned Appendix rows 22.1, 22.4, 22.5, 22.7, 22.8, 22.9, and 22.11 are
inventoried. Appendix 22.9's short ordering obstruction is an unselected
optional problem result, so it is accounted for without becoming a core gate.

## Verification

- `lake env lean LeanFpAnalysis/FP/Algorithms/Vandermonde/Higham22.lean`:
  PASS after the audit correction.
- The module contains no `sorry`, `admit`, `axiom`, `unsafe`,
  `opaque`, or synthetic `*_explicitDomain`/nonempty closure endpoint.
- Source formulas were checked against rendered pp. 422, 424, 425, and 426.

See the inventory and not-proved ledger for row-level status.
