# Faithfulness audit 004

## Snapshot

- Status: `in-progress` (ordinary scope settled; final snapshot pending)
- Baseline: completed `audit_003` at history commit
  `a06728e225be6348dcd72754114d0c9af1b5d4eb`
- Corpus: 20 papers and 60 tasks
- Ordinary audit scope: 52 tasks after eight owner-approved exclusions
- Currently accepted in ordinary scope: 52 tasks
- Pending fresh audits: none
- Audited but still not accepted in ordinary scope: none
- Current-target fourth-pass audits completed: 8; 7 accepted and 1 subsequently
  excluded by owner decision
- Latest completed fourth-pass audit reference: branch
  `benchmark_faithfulness_audit`, commit
  `ca8dd849a69ab8989136f289477c32138cc4f9db`
- Recorded as an in-progress history entry: `2026-08-23`

Task-local `faithfulness/` bundles remain the detailed evidence. The final
`results.json` and `manifest.json` will be generated only after the pass is
settled, so they can pin the final controlled inputs and task-audit commits.

## Progress from Audit 3

| View | Eligible | Accepted | Not accepted | Pending |
|---|---:|---:|---:|---:|
| Audit 4 current state | 52 | 52 | 0 | 0 |
| Audit 3 completed baseline | 57 | 45 | 12 | 0 |

Seven rebuilt tasks have moved from an unaccepted Audit 3 classification into
an accepted category: `P04-T2`, `P06-T1`, `P08-T3`, `P09-T2`, `P11-T1`,
`P12-T3`, and `P15-T3`. Five additional tasks have been excluded by owner
decision: `P16-T3`, `P18-T3`, `P19-T2`, `P19-T3`, and `P20-T3`. These
exclusions reduce the ordinary denominator from 57 to 52 but do not convert
their existing negative audit tags into accepted results.

## Fourth-pass outcomes

| Task | Audit 3 | Current disposition |
|---|---|---|
| `P04-T2` | `not-faithful-weaker` | `faithful-stronger` |
| `P08-T3` | `not-faithful-weaker` | `faithful-stronger` |
| `P11-T1` | `not-faithful-weaker` | `faithful-stronger` |
| `P12-T3` | `not-faithful-weaker` | `faithful-equivalent` |
| `P15-T3` | `not-faithful-different` | `faithful-equivalent`; adjudicated current-target audit at `92a868cdc` |
| `P16-T3` | `not-faithful-different` | excluded after the `not-faithful-different` audit at `ae1a41374`; owner scope decision |
| `P06-T1` | `not-faithful-weaker` | `faithful-stronger` |
| `P09-T2` | `not-faithful-weaker` | `faithful-equivalent`; adjudicated current-target audit at `ca8dd849a` |

The prior current-target P09-T2 audit at `9a6b60b3d` classified the task as
`not-faithful-weaker` because `P09TheoremOneExecution` supplied the propagated
stage estimates that the paper derives in equations (3.7)--(3.8). Rebuild
`9e30712e3` removed that certificate premise: the target now binds only an
operation-linked `P09AsymptoticFftFamily`, while the block, twiddle, propagation,
and global estimates are derived from primitive Wilkinson-model operations and
the rounded stage trace. The fresh audit at `ca8dd849a` classifies this version
as `faithful-equivalent`. It preserves the positive-sign unnormalized Fourier
transform, exact fictional-input equation, RMS identity, both norm bounds,
factorization-sensitive `K`, special radix constants, exact-input condition,
and local `O(epsilon^2)` semantics. Adjudication resolved the blind judge's only
uncertainty by tracing `p09StdAddChar_positive_exp` to the required positive
Fourier sign.

`P15-T3` was reselected with owner approval from Theorem 4.5 to Lemma 3.3,
equations (3.10)--(3.11). The rebuilt target preserves the two low-rank factor
orientations, both permitted three-product evaluation orders, the local
equation-(2.7) rounding certificates, Frobenius norms, the exact
`gamma_(b + 2*r^(3/2))` coefficient, and both complete forward-error bounds.
Adjudication resolved the judges' equivalent-versus-stronger disagreement as
`faithful-equivalent`: the additional natural-dimension boundary cases are
vacuous or trivial, and the signed parameters encode the same nonnegative
approximation budgets rather than new substantive cases.

`P16-T3` retains its `not-faithful-different` tag as provenance. The owner has
excluded it from the ordinary denominator because a faithful replacement would
require reconstructing substantially more of the paper's mixed-precision
analysis or approving a different source result.

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

- `P16-T3` (`not-faithful-different`): correction-level contraction estimates
  and high-precision bounds containing the paper's central work are supplied as
  proof-carrying inputs, while the target replaces the attainable-floor result
  with exact additive recurrences and omits parts of the final conclusion.
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

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different, `U`
undetermined, `P` pending, and `X` excluded. Only `E` and `S` are accepted.

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
| P09 | S | E | E | 3/3 |
| P10 | E | E | E | 3/3 |
| P11 | S | S | S | 3/3 |
| P12 | S | E | E | 3/3 |
| P13 | E | E | S | 3/3 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | E | 3/3 |
| P16 | E | X | X | 1/1 |
| P17 | X | S | S | 2/2 |
| P18 | S | E | X | 2/2 |
| P19 | S | X | X | 1/1 |
| P20 | S | S | X | 2/2 |
| **Current total** |  |  |  | **52/52** |

## Completion condition

All planned current-target fourth-pass reruns now have task-local audits. With
the owner-approved exclusion of `P16-T3`, all 52 tasks in the ordinary scope
are accepted: `52/52`. No eligible task is pending or unaccepted. The excluded
task's existing negative audit remains part of the evidence record and is not
counted as an acceptance.

The task dispositions are settled. Audit 4 still needs its final
machine-readable task index and manifest, exact per-task evidence commits,
validated aggregate counts, and completion timestamp before the history entry
changes from `in-progress` to `completed`.
