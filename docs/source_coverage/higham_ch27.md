# Higham Chapter 27 Source Coverage Ledger

Source: Higham, 2nd ed., Chapter 27, printed pp. 489-509. Mode: core.

Canonical source entry point: `NumStability/Source/Higham/Chapter27.lean`.
`SoftwareEnvironment.lean` owns the software-model, norm, and Smith-division
surface; `Problem06.lean` owns the exact real-arithmetic `pythag` development.
The two former `Algorithms/SoftwareIssues/Higham27*.lean` paths are
compatibility imports only.

| Source group | Status | Lean evidence |
|---|---|---|
| IEEE sticky flags | VERIFIED | `FPException`, `raiseException_mono`, `clearException` |
| Arithmetic parameters/model vocabulary | PRESENT | `ArithmeticParameters`, `PortableArithmeticModel` |
| Printed two-pass scaled norm | VERIFIED exact and literal rounded returned-norm trace | `twoPassScaledNorm_sq`, `twoPassRoundedScaledNorm`, `higham27_twoPassRoundedScaledNorm_trace_safe` |
| One-pass scaled norm / Appendix (A.16) | VERIFIED in exact arithmetic | `scaledSumSqStep_invariant`, `scaledSumSqFold_invariant`, `higham27_problem27_5_scaled_norm_correct_sq` |
| True complex one-norm vs BLAS `xCASUM` | VERIFIED / REUSED | repository `complexVecOneNorm`, `higham27BlasComplexPseudoOneNorm`, and `higham27_complexVecOneNorm_le_blasComplexPseudoOneNorm` |
| Equation (27.1) | VERIFIED | `higham27_eq27_1_smith_complex_division` |
| Conventional quotient and analogous Smith branch | VERIFIED / REUSED | Mathlib quotient-component lemmas and `higham27_smith_complex_division_symmetric` |
| Smith overflow avoidance (underflow still possible) | VERIFIED WITH SCOPED CONTRACT / UNCONDITIONAL READING REFUTED | both rounded pre-division branch traces compile; max-finite denominator counterexample compiles |
| Two-pass overflow safety | VERIFIED WITH EXPLICIT FORMAT/INPUT CONTRACT | explicit zero-scale branch; rounded quotient/square/accumulation/square-root/final-multiply trace |
| Problem 27.6 exact `pythag` algebra | VERIFIED | `higham27_problem27_6_halley_specialization`, `higham27_problem27_6_pair_step_invariant`, `higham27_problem27_6_matlab_scaled_step`, `higham27_problem27_6_monotone_enclosure`, and `higham27_problem27_6_cubic_error_identity`/`_bound` |
| Blue three-accumulator safety and accuracy | DEFERRED | chapter supplies no executor, thresholds, rounding order, combination logic, or accuracy inequality |
| Historical/software/empirical sections | EXCLUDED | reason-coded in the inventory |
| Optional Problems 27.1-27.8 | EXCLUDED except selected 27.5 and the exact real-arithmetic content of 27.6 | Appendix rows are inventoried individually; only Problem 27.6's machine-specific `<= 3` stopping claim remains deferred |

Aggregate selected-scope status: **PASS**.  Precise printed algorithms and the
selected implementation-facing traces are verified under explicit contracts;
the source's overbroad Smith reading is refuted rather than promoted.  Blue's
citation-only idea summary is deferred for lack of a precise local statement.

For the two-pass norm, the source-facing safety theorem assumes finite input
data, representable integer accumulation bounds, a representable envelope for
`sqrt n`, and capacity for rescaling that envelope.  It proves the nonzero
division domain, nonnegative square-root domain, and no-overflow property for
every exact pre-round value.  The executor returns zero before forming any
quotient when the scale is zero.  Underflow and inexact rounding remain
possible and are not mislabeled as absent.

Problem 27.6's exact Halley specialization, scaled recurrence, Pythagorean
invariant, monotone enclosure, and cubic error identity and bound are proved in
the canonical `Problem06` leaf. Only the statement that MATLAB's
`r + 4 == 4` test stops in at most three iterations remains deferred because
it depends on a concrete machine format and evaluation semantics.

Verification: target and Algorithms-umbrella builds PASS; forbidden-token
hygiene PASS. Representative axiom audits, including `twoPassScaledNorm_sq`,
`higham27_twoPassRoundedScaledNorm_trace_safe`, both Smith branch traces, and
the max-finite counterexample contain only standard Mathlib axioms.
