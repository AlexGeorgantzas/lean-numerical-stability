# Chapter 14 Not-Proved Ledger

## Selected-Scope Gate

**Current status: CLOSED (strict gate PASS).**

The **79-row** source inventory is the authoritative accounting document.
There are no remaining precise selected-source proof obligations. The rows
formerly blocked by the pre-division trace are closed by structural
finalization and the literal componentwise final-division analysis.

| Source location | Selected claim | Current Lean status | Terminal accounting | Blocking final gate? |
|---|---|---|---|---|
| (14.27), (14.29)-(14.30) | Accumulated matrix/RHS identities and componentwise forward/backward errors | CLOSED | The finalized source trace writes eliminated dead-storage entries as structural zeros, produces the actual final diagonal, and feeds the accumulation endpoints; `Ch14GJEFinalDivisionClosure.lean` carries them through the printed divisions | NO |
| Theorem 14.5, (14.31)-(14.33) | Printed residual and forward bounds for the actual computed GJE solution | CLOSED at determinate source strength | Exact all-orders envelopes and literal first-order constants are proved for `ch14ext_gjeFinalizedDivOutput`; the PDF's bare `O(u^2)` wording is terminally deferred because it specifies no family or uniformity hypotheses | NO |
| Corollary 14.6 | SPD residual and relative-forward constants | CLOSED at determinate source strength | `Ch14Cor146UniformInverseBridge.lean` constructs the scaled inverse and its regularity under the visible symmetry-exploiting SPD policy; the unparameterized `O(u^2)` wording is terminally deferred | NO |
| Corollary 14.7 | Row-diagonally-dominant residual and relative-forward constants | CLOSED at determinate source strength | `Ch14Cor147FinalDivisionFamilyClosure.lean` proves the actual-output constants and `Ch14Cor147SourceDomainConstructor.lean` constructs the exact domain witnesses; the unparameterized `O(u^2)` wording is terminally deferred | NO |
| Fixed-matrix addendum to (14.30) | General final diagonal scaling has a "negligible effect" | `DEFER-MISSING-PRECISE-STATEMENT` | The PDF provides neither a rounded scaling operation nor a quantitative transfer bound, so inventing one would strengthen the source | NO |

`Ch14GJEOperationalBridge.lean` remains part of the audit trail. Its checked
2-by-2 counterexample shows why the old literal-storage trace could not imply
`final_matrix = I`: a legal `FPModel` can leave an eliminated dead entry equal
to `-u`. The canonical structural-finalization producer repairs exactly this
modeling defect, ends at the actual diagonal `D` (and at `I` for the
source-normalized unit-diagonal case), and the final-division closure analyzes
the literal Algorithm 14.4 output. Thus the counterexample is a superseded
blocker diagnosis, not a current open obligation.

## Intentional Exclusions

The following are not proof gaps and do not fail the selected gate:

| Category | Rows | Reason |
|---|---|---|
| Empirical figures/tables | Table 14.1, Figure 14.1, Table 14.2, Tables 14.3-14.5, Table 14.6 | Historical machine output or plots without a uniquely specified execution |
| Exposition/literature | Remaining parallel inversion prose; Section 14.7 notes | Csanky/processor/complexity discussion, acceleration and qualitative stability observations, bibliographic material, and benchmarks. The precise Schulz recurrence and convergence claims are proved in `Ch14SchulzIteration.lean`. |
| Optional Problems | Problems 14.1, 14.6, 14.9 | Not selected in this core pass; Problem 14.1 is not a precise theorem |

## Honest Model Boundaries

- `fl_matMul` and the repository `FPModel` formalize the abstract rounded-operation semantics used by the book; they are not a hardware emulator.
- Problem 14.2 proves consequences of family-level forms of assumptions (13.4) and (13.5). It does not claim that an unspecified fast multiplication implementation satisfies those contracts.
- Successful-run pivot/nonzero conditions are operational domain assumptions, not assumed error conclusions.
