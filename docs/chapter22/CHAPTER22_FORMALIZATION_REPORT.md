# Higham Chapter 22 Formalization Report

## Outcome

The fresh strict selected-scope gate is **PASS**.  The exact factorization,
rounded forward analysis, checkerboard specializations, general residual
theorem conditional on source assumption (22.24), and the monomial producer
required by Corollary 22.7 are all present.  Table 22.1 is handled under the
core-mode figure/table rule, and the unquantified refinement sentence is
deferred rather than strengthened into an invented endpoint.

## Principal endpoints

| Source | Lean evidence |
|---|---|
| Algorithm 22.1, (22.1)--(22.4) | exact synthetic-division inverse path and confluent determinant theorems |
| Algorithm 22.2, (22.5)--(22.17) | `higham22Hermite_algorithm22_2Printed_solve`, `higham22Hermite_eq22_17_inverse` |
| Algorithm 22.3 | `higham22_algorithm22_3_eq_factorized` proves the separate natural-indexed executor equals the transposed factor product; `higham22Hermite_algorithm22_3_solve` is the literal primal solve |
| (22.19)--(22.21) | `higham22_eq22_19_actual_stageI`, `_eq22_20_actual_stageII`, `_eq22_21_actual_rounded_factor_product` |
| Theorem 22.4 / (22.18) | `higham22_theorem22_4_actual_factor_product_bound`, `higham22_eq22_18_actual_forward_error` |
| Corollary 22.5 / (22.22) | full factor-sequence checkerboard proof and `higham22_corollary22_5_named_bases` |
| (22.23)--(22.25), Theorem 22.6 | exact/rounded reverse inverse factors, `Higham22Eq22_24`, `higham22_theorem22_6_actual_inverse_matrix_bound`, `higham22_eq22_25_actual_residual_bound` |
| Problem 22.8 / Corollary 22.7 | complex structured-bidiagonal inverse producer, actual state-dependent factor identification, `higham22Closure_eq22_24_monomial`, `higham22_corollary22_7_monomial_residual_closed`, and `higham22_corollary22_7_first_order` — PROVED |
| Algorithm 22.8 | `higham22_algorithm22_8_correct` |
| Refinement prose 22.B2 | DEFER-MISSING-PRECISE-STATEMENT; Chapter 5 residual-formation producers and the Chapter 12 one-step envelope remain useful extra bridges |

## Assumption discipline

`Higham22Eq22_24` is the source's explicit simplifying assumption about each
rounded upper-factor inverse in general Theorem 22.6.  It includes
nonsingularity, which is implicit in the book's ordinary inverse notation,
and its componentwise relative bound.  For Corollary 22.7,
`higham22Closure_eq22_24_monomial` now produces it from the actual rounded
factor sequence, so the public closed corollary has no target-bearing premise.

## Verification

- Fresh focused build of
  `LeanFpAnalysis.FP.Algorithms.Vandermonde.Higham22MonomialClosure`:
  PASS (3078 jobs).
- Axiom audit of the (22.24) producer and closed Corollary 22.7: only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean examples/LibraryLookup.lean`: chapter endpoints checked.
- The Chapter 22 module contains no `sorry`, `admit`, `axiom`, `unsafe`, or
  target-bearing explicit-domain closure object.
- Source checked from scratch against `References/1.9780898718027.ch22.pdf`
  and the owned Appendix A solution to Problem 22.8.
