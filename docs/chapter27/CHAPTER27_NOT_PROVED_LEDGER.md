# Chapter 27 Not-Proved Ledger

The Chapter 27 selected-scope gate is **PASS**.  No selected precise body claim
remains open.

## Closed exact and range-safety rows

| Source location | Claim | Lean disposition |
|---|---|---|
| Sec. 27.8, p. 499 | The printed two-pass scaled norm avoids overflow | `twoPassRoundedScaledNorm` is the literal executor and `higham27_twoPassRoundedScaledNorm_trace_safe` verifies its explicit zero branch and its rounded quotient, square, accumulation, square-root, and final-multiplication path under finite-input, representability, and final-capacity conditions.  The theorem rules out divide-by-zero, invalid square root, and intermediate overflow; it does not rule out underflow or inexact rounding. |
| Sec. 27.8, p. 500 | Smith's branched scaled division avoids overflow before the final quotient divisions | `smith_first_branch_preDivision_safe` and `smith_symmetric_branch_preDivision_safe` verify both rounded branches under explicit input/capacity conditions. |
| Sec. 27.8, p. 500 | Unrestricted Smith wording | An unconditional theorem would be false: `smith_scaledDenominator_overflows_at_maxFiniteMagnitude` proves that `c=d=maxFiniteMagnitude` makes the printed scaled denominator overflow.  The ledger therefore records the scoped theorem and the counterexample, not a stronger invented claim. |
| Problem 27.6, pp. 507--509 | Exact Moler--Morrison/Halley `pythag` algebra | `higham27_problem27_6_halley_specialization`, `_pair_step_eq_halley`, `_pair_step_invariant`, `_matlab_scaled_step`, `_cubic_error_identity`, `_monotone_enclosure`, and `_cubic_error_bound` prove the exact real-arithmetic specialization, recurrence, invariant, enclosure, and cubic convergence algebra. |

## Deferred and excluded rows

Blue's three-accumulator method is **DEFER-MISSING-PRECISE-STATEMENT**, not a
gate blocker.  The chapter gives only an idea-level summary and a citation: it
does not specify the three thresholds, executor, rounding order, combination
logic, or the claimed error-bound formula.  The separately printed concise
Hammarling/LAPACK update in Problem 27.5 has an exact invariant and correctness
theorem in Lean, but it is not mislabeled as Blue's algorithm.

Problem 27.6's remaining statement that MATLAB's `r + 4 == 4` stopping test
fires in at most three iterations is **DEFER-MACHINE-SPECIFIC**. Proving it
requires a concrete floating-point format and evaluation semantics; it is not
part of the exact real-arithmetic recurrence already closed above.

Problems 27.1--27.4 and 27.7--27.8 remain optional or machine-specific and are
excluded by the core-selection policy. Historical hardware, compiler, timing,
software-catalogue, and Patriot-incident rows are likewise nonblocking skips.
