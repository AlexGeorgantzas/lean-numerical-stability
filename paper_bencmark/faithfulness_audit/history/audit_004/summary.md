# Faithfulness audit 004

## Snapshot

- Status: `in-progress`
- Baseline: completed `audit_003` at history commit
  `a06728e225be6348dcd72754114d0c9af1b5d4eb`
- Corpus: 20 papers and 60 tasks
- Ordinary audit scope: 53 tasks after seven owner-approved exclusions
- Currently accepted in ordinary scope: 50 tasks
- Pending fresh audit: `P09-T2`
- Audited but still not accepted: `P15-T3`, `P16-T3`
- Current-target fourth-pass audits completed so far: 7; 5 accepted and 2 not accepted
- Latest completed fourth-pass audit reference: branch
  `benchmark_faithfulness_audit`, commit
  `d2ca3ee27f187dd5e5360c04f5dc4818c73d47aa`
- Recorded as an in-progress history entry: `2026-08-23`

Task-local `faithfulness/` bundles remain the detailed evidence. The final
`results.json` and `manifest.json` will be generated only after the pass is
settled, so they can pin the final controlled inputs and task-audit commits.

## Progress from Audit 3

| View | Eligible | Accepted | Not accepted | Pending |
|---|---:|---:|---:|---:|
| Audit 4 current state | 53 | 50 | 2 | 1 |
| Audit 3 completed baseline | 57 | 45 | 12 | 0 |

Five rebuilt tasks have moved from an unaccepted Audit 3 classification into
an accepted category: `P04-T2`, `P06-T1`, `P08-T3`, `P11-T1`, and `P12-T3`. Four
additional tasks have been excluded by owner decision: `P18-T3`, `P19-T2`,
`P19-T3`, and `P20-T3`. These exclusions reduce the ordinary denominator from
57 to 53 but do not convert their existing negative audit tags into accepted
results.

## Fourth-pass outcomes

| Task | Audit 3 | Current disposition |
|---|---|---|
| `P04-T2` | `not-faithful-weaker` | `faithful-stronger` |
| `P08-T3` | `not-faithful-weaker` | `faithful-stronger` |
| `P11-T1` | `not-faithful-weaker` | `faithful-stronger` |
| `P12-T3` | `not-faithful-weaker` | `faithful-equivalent` |
| `P15-T3` | `not-faithful-different` | `undetermined`; further repair remains open |
| `P16-T3` | `not-faithful-different` | `not-faithful-different`; further repair remains open |
| `P06-T1` | `not-faithful-weaker` | `faithful-stronger` |
| `P09-T2` | `not-faithful-weaker` | rebuilt again in `ee0e78c3c`; fresh audit pending |

The negative P09-T2 audit at `080e0b55e` was superseded by the committed
rebuild at `ee0e78c3c` and is not a verdict on the current target. `P15-T3` now
preserves the final algebra and detailed UFC/UCF and triangular-solve traces,
but its run still assumes aggregate predecessor analyses that the paper
derives; the paper's `A`/`Atilde` and Big-O ambiguity also prevents the reverse
implication from being decided. `P16-T3` remains different because
correction-level contraction estimates and high-precision bounds containing
the paper's central work are still supplied as proof-carrying inputs, while
the target omits parts of the paper's final attainable-level conclusion.

## Exclusion categories

Exclusion means that a task is retained in the benchmark corpus but omitted
from the ordinary paper-faithfulness denominator. Its existing audit tag is
kept as provenance and is not treated as an acceptance result.

### Corrected defective source claims

These tasks formalize a project-corrected version of a published result whose
written hypotheses do not imply its conclusion. The added assumptions make
the mathematics sound but restrict applicability, so an ordinary audit can
legitimately classify the corrected Lean statement as weaker than the printed
claim.

- `P07-T2`: Theorem 3.5 needs the perturbed matrix to retain full column rank
  and the perturbed right-hand side to lie in its range. The corrected task
  adds both conditions. See the
  [source-validity record](../../source_validity/P07-T2.md).
- `P16-T2`: the proof of Lemma 4.2 uses an unstated comparison between the
  current and next iterate norms. A one-dimensional counterexample violates
  the printed recurrence without it, so the corrected task states the
  comparison explicitly. See the
  [source-validity record](../../source_validity/P16-T2.md).
- `P17-T1`: Theorem 3.6 bounds an expected product while its proof multiplies
  inequalities by a preceding partial product without ensuring that product
  is nonnegative; it also needs the lower factor `1 - B` to be nonnegative.
  A two-outcome counterexample satisfies the printed expectation and bias
  assumptions but gives expected product `6`, above the claimed upper bound
  `9/4`. The project-corrected task adds nonnegative-factor and `B <= 1`
  conditions. See the
  [source-validity record](../../source_validity/P17-T1.md).

### Insufficient exact source data

- `P18-T3` (`not-faithful-different`): Method 4s3pC is published only through
  coefficients rounded to 15 decimal places, but the selected exact
  convergence-order result requires exact coefficient identities. The printed
  decimals fail at least one such identity, and no exact tableau is available
  in the checked source material. The task is excluded as source-ambiguous
  unless exact coefficients are obtained or a different result is selected.

### Deferred full-analysis reconstruction

These exclusions do not assert that the papers' selected claims are false.
They preserve negative tags for current targets that assume substantial parts
of the analysis they are meant to formalize. A faithful replacement would
require a broader proof reconstruction or an approved source reselection.

- `P19-T2` (`not-faithful-different`) and `P19-T3`
  (`not-faithful-different`): the tasks preload the main MGS and appendix
  analyses as certificates and omit necessary links among nonsingularity,
  precision, constants, and first-order semantics. Repairing them faithfully
  requires a coordinated reconstruction of Theorem 3.1 and Appendices A, C,
  and D, or coordinated reselection.
- `P20-T3` (`not-faithful-weaker`): the task assumes the substantive Section 4
  derivation, gives second-order notation insufficient mathematical content,
  and treats equation (4.33) as a second bound for an execution to which it
  does not apply. Retaining Theorem 4.1 would require formalizing equations
  (4.8)--(4.32) while importing only the legitimate external estimate.

## Provisional paper matrix

Legend: `E` equivalent, `S` stronger, `D` different, `U` undetermined, `P`
pending, and `X` excluded. Only `E` and `S` are accepted.

| Paper | T1 | T2 | T3 | Accepted/eligible |
|---|---:|---:|---:|---:|
| P01 | E | E | E | 3/3 |
| P02 | S | S | S | 3/3 |
| P03 | S | E | S | 3/3 |
| P04 | S | S | S | 3/3 |
| P05 | S | S | S | 3/3 |
| P06 | S | E | E | 3/3 |
| P07 | S | X | S | 2/2 |
| P08 | S | S | S | 3/3 |
| P09 | S | P | E | 2/3 |
| P10 | E | E | E | 3/3 |
| P11 | S | S | S | 3/3 |
| P12 | S | E | E | 3/3 |
| P13 | E | E | S | 3/3 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | U | 2/3 |
| P16 | E | X | D | 1/2 |
| P17 | X | S | S | 2/2 |
| P18 | S | E | X | 2/2 |
| P19 | S | X | X | 1/1 |
| P20 | S | S | X | 2/2 |
| **Current total** |  |  |  | **50/53** |

## Completion condition

The current committed `P09-T2` rebuild still requires a fresh task-local audit.
Even if it is accepted, the aggregate would be `51/53` because `P15-T3` and
`P16-T3` remain eligible and not accepted. Reaching 100% requires all three
tasks to be accepted, or a separate explicit owner decision changing their
scope or exclusion status.

After all dispositions are settled, Audit 4 must receive its final
machine-readable task index and manifest, exact per-task evidence commits,
validated aggregate counts, and completion timestamp.
