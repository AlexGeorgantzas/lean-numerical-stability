# Chapter 14 Not-Proved Ledger

## Selected-Scope Gate

**Current status: OPEN (strict gate FAIL).**

The 78-row source inventory remains the authoritative accounting document.
Theorem 14.5 and Corollaries 14.6-14.7 are open because their exact-constant
theorems consume source-family structures that no rounded Algorithm 14.4
execution constructs.

| Source location | Exact selected claim | Current Lean status | Why the current result does not close it | Smallest missing producer | Blocking final gate? |
|---|---|---|---|---|---|
| Theorem 14.5, (14.31)-(14.33) | Printed residual and forward bounds for a successful computed GJE solution | Conditional family endpoint | `ch14ext_gjeSourceTrace_theorem14_5_printed_vanishing_family_endpoint` assumes `Ch14GJETheorem145SourceFamily`; in particular, its rounded trace is assumed to finish at `I` and its stage/inverse families are assumed `O(1)` | A rounded executor with structural zeroing and final diagonal scaling, plus a constructor proving the family fields for that same trace | YES |
| Corollary 14.6 | SPD residual and relative-forward constants | Conditional family endpoint | `Ch14Cor146SourceRunFamily` is unconstructed and additionally contains scaled-inverse and uniform-inverse regularity fields | Construct it from the corrected rounded executor and SPD/positive-pivot hypotheses | YES |
| Corollary 14.7 | Row-diagonally-dominant residual and relative-forward constants | Conditional family endpoint | `Ch14Cor147SourceFamily` is unconstructed and contains finalization and uniform stage/inverse regularity fields | Construct it from the corrected rounded executor and row-dominance hypotheses | YES |

`Ch14GJEOperationalBridge.lean` discharges the tractable witness fields:
`ch14ext_gjeSourceComputedOutput` is definitionally the trace output, while
`ch14ext_gjeCanonicalUpperInverse_isInverse` and
`ch14ext_gjeCanonicalUpperSolve_exact` construct the exact analysis-only
inverse and solve from nonsingularity. The family solve is `O(1)` once the
canonical inverse and RHS are `O(1)`.

The same module also rules out the missing bridge for the current executor.
`ch14ext_finalizationCounter_all_local_guards_but_not_identity` proves both
gamma-validity guards and operational pivot success for a normalized 2-by-2
trace, while the same legal `FPModel` leaves the eliminated entry equal to
`-u`. Thus all current local guards still cannot prove
the old `final_matrix = I` field; a structural-zero/final-scaling executor is
required.

## Intentional Exclusions

The following are not proof gaps and do not fail the selected gate:

| Category | Rows | Reason |
|---|---|---|
| Empirical figures/tables | Table 14.1, Figure 14.1, Table 14.2, Tables 14.3-14.5, Table 14.6 | Historical machine output or plots without a uniquely specified execution |
| Exposition/literature | Parallel inversion methods; Section 14.7 notes | Literature review, qualitative observations, and benchmark material |
| Optional Problems | Problems 14.1, 14.6, 14.9 | Not selected in this core pass; Problem 14.1 is not a precise theorem |

## Honest Model Boundaries

- `fl_matMul` and the repository `FPModel` formalize the abstract rounded-operation semantics used by the book; they are not a hardware emulator.
- Problem 14.2 proves consequences of family-level forms of assumptions (13.4) and (13.5). It does not claim that an unspecified fast multiplication implementation satisfies those contracts.
- Successful-run pivot/nonzero conditions are operational domain assumptions, not assumed error conclusions.
