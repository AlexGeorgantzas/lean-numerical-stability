# Chapter 22 Not-Proved Ledger

The strict from-scratch re-audit found selected core rows that are not closed.

| Source row | Disposition | Reason |
|---|---|---|
| Table 22.1 V1 | OPEN | Precise harmonic-node inequality `κ∞(V_n) > n^(n+1)`.  The surrounding source says it follows from (22.3), but no specialization/product proof exists. |
| Table 22.1 V2 | OPEN | Precise all-real-node `κ₂` lower bound; external citation is a proof-source issue, not a license to skip the claim. |
| Table 22.1 V3 | OPEN | Precise nonnegative-node `κ₂` lower bound; no producer exists. |
| Table 22.1 V4 | OPEN | Precise equispaced-`[0,1]` `κ∞` asymptotic; the source relates it to (22.3), but the asymptotic specialization is absent. |
| Table 22.1 V5 | OPEN | Precise equispaced-`[-1,1]` `κ∞` asymptotic; no producer exists. |
| Table 22.1 V6 | OPEN | Precise Chebyshev-node `κ∞` asymptotic; no producer exists. |
| Corollary 22.7 / Problem 22.8 bridge | OPEN | `higham22_problem22_8_source_coefficient` is only an abstract real upper-bidiagonal entry theorem.  No theorem identifies the actual complex, state-dependent rounded Stage-II sequence with its structured perturbation, and the corollary still accepts `Higham22Eq22_24` as an input. |
| Refinement prose 22.B2 | OPEN/PARTIAL | The new bridge derives residual-formation accuracy from (5.3)/(5.7).  It still assumes the full Chapter 12 envelope contracts, and no endpoint states the printed asymptotic componentwise backward stability. |
| Empirical rows 22.E1 and Table 22.3 | SKIP-EMPIRICAL | Historical machine outputs are underspecified. |
| 22.B3 | SKIP-QUALITATIVE | Editorial method-selection heuristics. |
| 22.N | SKIP-LITERATURE-REVIEW | Notes and bibliography. |
| Unselected Problems | OPTIONAL-PROBLEM-NOT-SELECTED / BENCHMARK_CANDIDATE | Exhaustively inventoried in the source inventory. |

The source's equation (22.24) remains a legitimate explicit assumption for
the *general* Theorem 22.6, and Theorem 22.6/(22.25) are proved from it.  It is
not a legitimate unresolved premise in the monomial Corollary 22.7, because
the source explicitly invokes Problem 22.8 to produce that specialization.

The current rounded operation graph also charges division by `1`, subtraction
`0-α`, and additions of exact zero through the unrestricted relative-error
interface.  Consequently its monomial rows can accumulate more independent
local factors than the one row scale plus one superdiagonal perturbation used
in Appendix A.  Closing the bridge requires either (a) a source-faithful
neutral-operation/negation exactness contract and a proof for the actual
factor sequence, or (b) a revised coefficient proved for the more permissive
graph; the existing real Problem 22.8 theorem alone cannot establish it.
