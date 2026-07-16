# Higham Chapter 27 Source Coverage Ledger

Source: Higham, 2nd ed., Chapter 27, printed pp. 489-509. Mode: core.

| Source group | Status | Lean evidence |
|---|---|---|
| IEEE sticky flags | VERIFIED | `FPException`, `raiseException_mono`, `clearException` |
| Arithmetic parameters/model vocabulary | PRESENT | `ArithmeticParameters`, `PortableArithmeticModel` |
| Printed two-pass scaled norm | VERIFIED exact and rounded range trace | `twoPassScaledNorm_sq`, `twoPassRoundedScaledSum_bounds_and_safe` |
| One-pass scaled norm / Appendix (A.16) | VERIFIED in exact arithmetic | `scaledSumSqStep_invariant`, `scaledSumSqFold_invariant`, `higham27_problem27_5_scaled_norm_correct_sq` |
| True complex one-norm vs BLAS `xCASUM` | VERIFIED / REUSED | repository `complexVecOneNorm`, `higham27BlasComplexPseudoOneNorm`, and `higham27_complexVecOneNorm_le_blasComplexPseudoOneNorm` |
| Equation (27.1) | VERIFIED | `higham27_eq27_1_smith_complex_division` |
| Conventional quotient and analogous Smith branch | VERIFIED / REUSED | Mathlib quotient-component lemmas and `higham27_smith_complex_division_symmetric` |
| Smith overflow avoidance (underflow still possible) | VERIFIED WITH SCOPED CONTRACT / UNCONDITIONAL READING REFUTED | both rounded pre-division branch traces compile; max-finite denominator counterexample compiles |
| Two-pass overflow safety | VERIFIED WITH EXPLICIT FORMAT/INPUT CONTRACT | concrete quotient/square/accumulation/final-product trace |
| Blue three-accumulator safety and accuracy | DEFERRED | chapter supplies no executor, thresholds, rounding order, combination logic, or accuracy inequality |
| Historical/software/empirical sections | EXCLUDED | reason-coded in the inventory |
| Optional Problems 27.1-27.8 | EXCLUDED except selected 27.5 | Appendix rows are inventoried individually |

Aggregate selected-scope status: **PASS**.  Precise printed algorithms and the
selected implementation-facing traces are verified under explicit contracts;
the source's overbroad Smith reading is refuted rather than promoted.  Blue's
citation-only idea summary is deferred for lack of a precise local statement.

Verification: target and Algorithms-umbrella builds PASS; forbidden-token
hygiene PASS. Representative axiom audits, including `twoPassScaledNorm_sq`,
`twoPassRoundedScaledSum_bounds_and_safe`, both Smith branch traces, and the
max-finite counterexample contain only standard Mathlib axioms.
