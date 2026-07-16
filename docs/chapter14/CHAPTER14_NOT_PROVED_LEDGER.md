# Chapter 14 Not-Proved Ledger

## Selected-Scope Gate

**Current status: CLOSED.**

The 78-row source inventory is the authoritative accounting document. All 68 selected rows are discharged: 66 are `PASS` and two are `SOURCE-ERROR/CORRECTED`. There are no selected proof obligations remaining.

The final source-active endpoints are:

| Source group | Final closure |
|---|---|
| Algorithm 14.4 through Theorem 14.5 | `Ch14GJETheorem145SourceClosure.lean`: `ch14ext_gjeSourceTrace_theorem14_5_printed_vanishing_family_endpoint` |
| Corollary 14.6 | `Ch14Corollary146SourceClosure.lean`: `ch14ext_cor146Source_vanishing_family_endpoint` |
| Corollary 14.7 | `Ch14Corollary147SourceClosure.lean`: `ch14ext_cor147Source_vanishing_family_endpoint` |

`Ch14GJEPrintedEnvelopeClosure.lean` is a generic algebraic helper. Its older unmasked-family endpoint is not used as the final Chapter 14 closure; the source-active masked trace and derived boundedness live in `Ch14GJETheorem145SourceClosure.lean`.

Likewise, `Ch14Corollary146Closure.lean` retains the older unmasked fixed-run helper route, but the accepted Corollary 14.6 endpoint is the masked source-trace theorem in `Ch14Corollary146SourceClosure.lean`.

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
