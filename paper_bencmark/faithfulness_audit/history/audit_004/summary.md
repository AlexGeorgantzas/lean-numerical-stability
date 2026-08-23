# Faithfulness audit 004

## Snapshot

- Status: `completed`
- Baseline: completed `audit_003` at history commit
  `a06728e225be6348dcd72754114d0c9af1b5d4eb`
- Corpus: 20 papers and 60 tasks
- Ordinary audit scope: 52 tasks after eight owner-approved exclusions
- Accepted in ordinary scope: 50 tasks
- Not accepted in ordinary scope: `P09-T3` and `P11-T3`
- Pending tasks: none
- Current-target fourth-pass audits completed: 10; seven accepted, two eligible
  tasks not accepted, and one subsequently excluded by owner decision
- Latest task-audit reference: branch `benchmark_faithfulness_audit`, commit
  `0185e36049e2bba27f200e34557eb1b33382fa5b`
- Finalized: `2026-08-23T14:10:01Z`

Task-local `faithfulness/` bundles remain the detailed evidence.
[`results.json`](results.json) records every task disposition, result, artifact
hash, evidence commit, and carry-forward validation. [`manifest.json`](manifest.json)
pins this summary and machine-readable index.

## Progress from Audit 3

| View | Eligible | Accepted | Not accepted | Pending |
|---|---:|---:|---:|---:|
| Audit 4 completed | 52 | 50 | 2 | 0 |
| Audit 3 completed baseline | 57 | 45 | 12 | 0 |

Seven rebuilt tasks moved from an unaccepted Audit 3 classification into an
accepted category: `P04-T2`, `P06-T1`, `P08-T3`, `P09-T2`, `P11-T1`,
`P12-T3`, and `P15-T3`. Five additional tasks were excluded by owner decision:
`P16-T3`, `P18-T3`, `P19-T2`, `P19-T3`, and `P20-T3`.

The final consistency check found genuine post-Audit-3 semantic changes in the
imported declarations used by `P09-T3` and `P11-T3`. Fresh independent audits
replaced their carried-forward acceptances with `not-faithful-weaker` and
`not-faithful-different`, respectively. This reduces the final accepted count
from the provisional `52/52` to `50/52`.

## Fourth-pass outcomes

| Task | Audit 3 | Audit 4 disposition |
|---|---|---|
| `P04-T2` | `not-faithful-weaker` | `faithful-stronger` |
| `P06-T1` | `not-faithful-weaker` | `faithful-stronger` |
| `P08-T3` | `not-faithful-weaker` | `faithful-stronger` |
| `P09-T2` | `not-faithful-weaker` | `faithful-equivalent` |
| `P09-T3` | `faithful-equivalent` | `not-faithful-weaker`; semantic-drift re-audit |
| `P11-T1` | `not-faithful-weaker` | `faithful-stronger` |
| `P11-T3` | `faithful-stronger` | `not-faithful-different`; semantic-drift re-audit |
| `P12-T3` | `not-faithful-weaker` | `faithful-equivalent` |
| `P15-T3` | `not-faithful-different` | `faithful-equivalent` |
| `P16-T3` | `not-faithful-different` | excluded after a new `not-faithful-different` audit |

### P09-T3

The target preserves the multidimensional complex transform, positive
unnormalized Fourier phase, nested coordinate order, relative RMS forward
error, factorization-sensitive `K` constants, and a valid quantified reading
of the paper's `O(epsilon^2)` term. It nevertheless takes
`P09TheoremTwoLocalAsymptotic` as `axisBounds`; that input already supplies the
propagated per-axis estimates that the paper derives from Theorem 1 and
equations (4.3)-(4.4). The adjudicated result is therefore
`not-faithful-weaker`: paper implies Lean, but Lean does not establish the
paper theorem from the paper's primitive hypotheses.

### P11-T3

The imported `p11C1` definition uses
`2 * sqrt (2 * m * k) + 2 * sqrt k`, while equation (2) in the paper uses
`2 * sqrt 2 * m * k + 2 * sqrt k`. This changes both the leading coefficient
and the smallness premise. The target also assumes uniform residual and
normal-equation estimates that the paper derives. Both independent judges
classify the current target as `not-faithful-different`.

### Other resolutions

`P09-T2` was rebuilt so its stage, twiddle, propagation, and global estimates
are derived from primitive Wilkinson-model operations and the rounded FFT
trace instead of being supplied as a certificate. Its final adjudicated audit
is `faithful-equivalent`.

`P15-T3` was reselected with owner approval from Theorem 4.5 to Lemma 3.3,
equations (3.10)-(3.11). Its two low-rank factor orientations, permitted
three-product orders, local rounding certificates, Frobenius norms, coefficient,
and complete forward-error bounds were adjudicated `faithful-equivalent`.

## Settled aggregate

| Classification | Count | Accepted |
|---|---:|---|
| `faithful-equivalent` | 20 | yes |
| `faithful-stronger` | 30 | yes |
| `not-faithful-weaker` | 1 | no |
| `not-faithful-different` | 1 | no |
| **Total** | **52** | **50** |

## Results by tier

| Tier | Equivalent | Stronger | Weaker | Different | Accepted |
|---|---:|---:|---:|---:|---:|
| T1 | 5 | 14 | 0 | 0 | 19/19 |
| T2 | 9 | 8 | 0 | 0 | 17/17 |
| T3 | 6 | 8 | 1 | 1 | 14/16 |

The denominators exclude `P17-T1` from T1; `P07-T2`, `P16-T2`, and `P19-T2`
from T2; and `P16-T3`, `P18-T3`, `P19-T3`, and `P20-T3` from T3.

## Exclusion categories

Exclusion means that a task remains in the benchmark corpus but is omitted
from the ordinary paper-faithfulness denominator. Its existing audit tag is
retained as provenance and is not converted into an accepted result.

### Corrected defective source claims

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
  is nonnegative; it also needs `1 - B` to be nonnegative. A concrete
  counterexample satisfies the printed assumptions but violates the bound.
  The project-corrected task adds the missing conditions. See the
  [source-validity record](../../source_validity/P17-T1.md).

These added hypotheses make the corrected mathematics sound but restrict
applicability, so their ordinary audit tags are intentionally not used as
acceptance signals.

### Insufficient exact source data

- `P18-T3` (`not-faithful-different`): Method 4s3pC is published only through
  coefficients rounded to 15 decimal places, but the selected exact
  convergence-order result requires exact coefficient identities. The printed
  decimals do not satisfy all required identities, and no exact tableau was
  available in the checked source material.

### Deferred full-analysis reconstruction

These exclusions do not assert that the selected paper claims are false. The
current targets assume substantial parts of the analysis they are meant to
formalize, and a faithful replacement would require broader reconstruction or
an approved source reselection.

- `P16-T3` (`not-faithful-different`): correction-level contraction estimates
  and high-precision bounds containing the paper's central work are supplied
  as inputs, while parts of the attainable-floor conclusion are omitted.
- `P19-T2` and `P19-T3` (`not-faithful-different`): the tasks preload the main
  MGS and appendix analyses as certificates and omit necessary links among
  nonsingularity, precision, constants, and first-order semantics.
- `P20-T3` (`not-faithful-weaker`): the task assumes the substantive Section 4
  derivation, gives second-order notation insufficient mathematical content,
  and applies equation (4.33) outside its legitimate execution setting.

## Paper matrix

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different, and `X`
excluded. Only `E` and `S` are accepted.

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
| P09 | S | E | W | 2/3 |
| P10 | E | E | E | 3/3 |
| P11 | S | S | D | 2/3 |
| P12 | S | E | E | 3/3 |
| P13 | E | E | S | 3/3 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | E | 3/3 |
| P16 | E | X | X | 1/1 |
| P17 | X | S | S | 2/2 |
| P18 | S | E | X | 2/2 |
| P19 | S | X | X | 1/1 |
| P20 | S | S | X | 2/2 |
| **Total** |  |  |  | **50/52** |

## Validation

All 10 current-target fourth-pass bundles passed complete-phase validation at
their exact evidence commits. The 43 carried-forward accepted results retain
the exact Audit 3 target and paper hashes. For accepted siblings affected by
later shared-module edits, regenerated target-relevant inventories found no
changed, missing, or added declaration semantics for `P04-T1`, `P04-T3`,
`P06-T2`, `P06-T3`, `P08-T1`, `P08-T2`, `P11-T2`, `P12-T1`, `P12-T2`,
`P15-T1`, `P15-T2`, and `P16-T1`. `P09-T1` differed only in declaration owner
module after a module split; declaration names, types, and bodies were
unchanged.

The same check found genuine target-relevant semantic drift for `P09-T3` and
`P11-T3`, which is why they were freshly audited instead of carried forward.
No benchmark target, shared Lean definition, metadata file, context, proof, or
reference PDF was modified by these audits.

## Interpretation

Audit 4 closes with 50 accepted tasks among 52 ordinary eligible tasks, two
eligible tasks not accepted, no pending tasks, and eight documented exclusions.
Acceptance measures faithfulness to the selected paper result; it does not by
itself establish benchmark difficulty, usefulness, or measurement readiness.
