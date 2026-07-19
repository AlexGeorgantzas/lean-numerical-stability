# Higham Chapter 22 Formalization Report

## Outcome

The strict selected-scope gate is **FAIL**.  The exact factorization, rounded
forward analysis, checkerboard specializations, and general residual theorem
conditional on source assumption (22.24) are present.  Three source-strength
gaps remain: Table 22.1 V1--V6, the actual monomial Stage-II producer required
by Corollary 22.7, and the whole-contraction/final-stability part of the
refinement prose.

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
| Problem 22.8 / Corollary 22.7 | abstract structured bidiagonal inverse-entry producer and `higham22_corollary22_7_first_order`; actual factor-sequence bridge OPEN |
| Algorithm 22.8 | `higham22_algorithm22_8_correct` |
| Refinement prose 22.B2 | Chapter 5 residual-formation producers plus Chapter 12 one-step envelope; whole contraction/final backward-stability endpoint OPEN |

## Assumption discipline

`Higham22Eq22_24` is the source's explicit simplifying assumption about each
rounded upper-factor inverse in general Theorem 22.6.  It includes
nonsingularity, which is implicit in the book's ordinary inverse notation,
and its componentwise relative bound.  Corollary 22.7 is different: Appendix
A Problem 22.8 is supposed to discharge this assumption for monomials.  The
current corollary still accepts it as a premise, so it is not a closed source
endpoint.

## Verification

- Fresh focused build through
  `LeanFpAnalysis.FP.Algorithms.Vandermonde.Higham22Ch12RefinementBridge`:
  PASS (3402 jobs), including `Higham22`, `Horner`, and `HighamChapter12`.
- `lake env lean examples/LibraryLookup.lean`: chapter endpoints checked.
- The Chapter 22 module contains no `sorry`, `admit`, `axiom`, `unsafe`, or
  target-bearing explicit-domain closure object.
- Source checked from scratch against `References/1.9780898718027.ch22.pdf`
  and the owned Appendix A solution to Problem 22.8.  That re-check is what
  exposed the open actual-factor bridge and the precise Table 22.1 rows.
