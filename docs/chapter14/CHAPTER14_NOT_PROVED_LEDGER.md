# Chapter 14 Not-Proved Ledger

## Selected-Scope Gate

**Current status: CLOSED / PASS.**

The 82-row source inventory is the authoritative accounting document. Of 71
selected rows, 69 are `PASS` and two are `SOURCE-ERROR/CORRECTED`.  No selected
row remains open, so Chapter 14 is complete in default core mode.

## Closed Final Selected Obligation

| Source claim | Final closure | Remaining completion obligation |
|---|---|---|
| p. 278 Schulz convergence from `X_0=alpha A^T` and `0<alpha<2/‖A‖₂^2` (inverse, or pseudoinverse for rectangular `A`) | `Ch14SchulzIteration.lean` supplies the exact step, residual powers, and Moore--Penrose support/error identities. `Ch14SchulzSpectralConvergence.lean` defines the exact rectangular operator norm, proves right-Gram spectral contraction, constructs a canonical arbitrary-rank compact-SVD Moore--Penrose inverse, and proves `ch14ext_rectSchulzIter_tendsto_canonicalMoorePenrose_of_lt_two_div_norm_sq`; `ch14ext_schulzIter_tendsto_inverse_of_lt_two_div_norm_sq` closes the square inverse clause. | None. |

`Ch14GJEPrintedEnvelopeClosure.lean` is a generic algebraic helper. Its older unmasked-family endpoint is not used as the final Chapter 14 closure; the source-active masked trace and derived boundedness live in `Ch14GJETheorem145SourceClosure.lean`.

Likewise, `Ch14Corollary146Closure.lean` retains the older unmasked fixed-run helper route, but the accepted Corollary 14.6 endpoint is the masked source-trace theorem in `Ch14Corollary146SourceClosure.lean`.

## Closed Primary Contracts

The following primary contracts remain closed and were checked against the
rendered source during this re-audit:

| Source group | Final closure |
|---|---|
| Lemmas 14.1--14.3 | `Ch14Method2Loop.lean`, `Ch14Method1BWhole.lean`, `Ch14Method2CWhole.lean` |
| Algorithm 14.4 through Theorem 14.5 | `Ch14GJETheorem145SourceClosure.lean`: `ch14ext_gjeSourceTrace_theorem14_5_printed_vanishing_family_endpoint` |
| Corollary 14.6 | `Ch14Corollary146SourceClosure.lean`: `ch14ext_cor146Source_vanishing_family_endpoint` |
| Corollary 14.7 | `Ch14Corollary147SourceClosure.lean`: `ch14ext_cor147Source_vanishing_family_endpoint` |

## Intentional Exclusions

The following are not proof gaps and do not fail the selected gate:

| Category | Rows | Reason |
|---|---|---|
| Empirical figures/tables | Table 14.1, Figure 14.1, Table 14.2, Tables 14.3-14.5, Table 14.6 | Historical machine output or plots without a uniquely specified execution |
| Exposition/literature | p. 278 slow-start estimate and Csanky/stability discussion; Section 14.7 notes | Qualitative thresholds, literature review, and benchmark material; the precise Schulz claims are selected separately |
| Optional Problems | Problems 14.1, 14.6, 14.9 | Not selected in this core pass; Problem 14.1 is not a precise theorem |

## Honest Model Boundaries

- `fl_matMul` and the repository `FPModel` formalize the abstract rounded-operation semantics used by the book; they are not a hardware emulator.
- Problem 14.2 proves consequences of family-level forms of assumptions (13.4) and (13.5). It does not claim that an unspecified fast multiplication implementation satisfies those contracts.
- Successful-run pivot/nonzero conditions are operational domain assumptions, not assumed error conclusions.
