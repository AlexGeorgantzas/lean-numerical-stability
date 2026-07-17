# Chapter 27 Proof-Source Ledger

| Selected claim | Source proof and location | External source | Route/status | Local Lean closure |
|---|---|---|---|---|
| Printed two-pass norm | direct algebra from p. 499 algorithm | none | formalized | `twoPassScaledNorm_sq` |
| Scaled norm invariant | Appendix A solution 27.5, p. 571, equation (A.16) | none | formalized | `scaledSumSqStep_invariant`, `scaledSumSqFold_invariant`, `higham27_problem27_5_scaled_norm_correct_sq` |
| True complex one-norm and `xCASUM` pseudo-one-norm | definitions on p. 500 | BLAS documentation cited for naming only | true norm reused from `Analysis.Norms`; pseudo-norm and comparison formalized directly | `complexVecOneNorm`, `higham27BlasComplexPseudoOneNorm`, `higham27_complexVecOneNorm_le_blasComplexPseudoOneNorm` |
| Two-pass overflow immunity | explanatory prose for the printed p. 499 algorithm | none | concrete finite round-to-even trace formalized under explicit format/input capacity conditions | `twoPassRoundedScaledSum_bounds_and_safe` |
| Blue three-accumulator immunity and accuracy | idea-level prose summary only | Blue [143, 1978] | deferred: chapter omits the executor, thresholds, rounding order, combination logic, and error inequality | none; no theorem invented from the citation summary |
| Smith division (27.1) | direct algebra in Sec. 27.8 | Smith [1052, 1962] cited for algorithm, not needed for proof | formalized directly | `higham27_eq27_1_smith_complex_division` |
| Analogous `|d| >= |c|` Smith branch | stated by symmetry after (27.1) | Smith [1052, 1962] | formalized directly | `higham27_smith_complex_division_symmetric` |
| Smith overflow avoidance (with possible underflow) | implementation explanation surrounding (27.1) | Smith [1052, 1962] | both scoped rounded pre-division traces formalized; unconditional reading refuted | `smith_first_branch_preDivision_safe`, `smith_symmetric_branch_preDivision_safe`, `smith_scaledDenominator_overflows_at_maxFiniteMagnitude` |

No unproved external theorem is used by a completed Chapter 27 surface.  No
selected precise body row remains open.
