# Faithfulness audit 003

## Snapshot

- Status: `completed`
- Baseline: `audit_002` at history commit
  `ceaed089455cb1a57f69b3c6f93dda9d4f15d947`
- Corpus: 20 papers and 60 tasks
- Ordinary audit scope: 57 tasks after three source-validity exclusions
- Settled ordinary results: 57 tasks; no pending tasks
- Third-pass rebuilt and independently audited tasks: 23
- Initially recorded with three pending decisions: `2026-08-22T03:31:47Z`
- Finalized: `2026-08-22T08:07:16Z`
- Latest task-audit reference: branch `benchmark_faithfulness_audit`,
  commit `cbfd683407c8fbbfc990511c00e7d1c2e542f91d`
- Original preliminary history commit:
  `0a7c74b4ff6574c25849bbcde019d54c271540d3`

Task-local audit bundles remain the detailed evidence. [`results.json`](results.json)
records each task's disposition, Audit 2 result, current result where applicable,
artifact hashes, evidence commit, and validation status.

## Progress from Audit 2

| View | Settled | Accepted | Not accepted | Pending |
|---|---:|---:|---:|---:|
| Audit 3 ordinary scope | 57 | 45 | 12 | 0 |
| Audit 2 eligible corpus | 59 | 34 | 25 | 0 |
| Third-pass reruns only | 23 | 11 | 12 | - |

Pass 3 raised the accepted count from 34 to 45. Eleven of the 23 rebuilt and
audited tasks moved into an accepted category; 12 remain unaccepted. The
ordinary denominator decreased from 59 to 57 because `P07-T2` and `P16-T2`
were rebuilt as explicit corrections to defective source claims and were
excluded alongside the existing `P17-T1` source exception.

Newly accepted in Pass 3:
`P04-T1`, `P05-T1`, `P05-T2`, `P05-T3`, `P09-T3`, `P10-T1`,
`P10-T2`, `P10-T3`, `P11-T3`, `P12-T2`, and `P18-T1`.

## Settled aggregate

| Classification | Count | Accepted |
|---|---:|---|
| `faithful-equivalent` | 18 | yes |
| `faithful-stronger` | 27 | yes |
| `not-faithful-weaker` | 7 | no |
| `not-faithful-different` | 5 | no |
| **Total** | **57** | **45** |

## Results by tier

| Tier | Equivalent | Stronger | Weaker | Different | Accepted |
|---|---:|---:|---:|---:|---:|
| T1 | 5 | 12 | 2 | 0 | 17/19 |
| T2 | 8 | 7 | 2 | 1 | 15/18 |
| T3 | 5 | 8 | 3 | 4 | 13/20 |

The denominators exclude `P17-T1` from T1 and `P07-T2` and `P16-T2`
from T2.

## Paper matrix

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different,
and `X` excluded. Only `E` and `S` are accepted.

| Paper | T1 | T2 | T3 | Accepted/eligible |
|---|---:|---:|---:|---:|
| P01 | E | E | E | 3/3 |
| P02 | S | S | S | 3/3 |
| P03 | S | E | S | 3/3 |
| P04 | S | W | S | 2/3 |
| P05 | S | S | S | 3/3 |
| P06 | W | E | E | 2/3 |
| P07 | S | X | S | 2/2 |
| P08 | S | S | W | 2/3 |
| P09 | S | W | E | 2/3 |
| P10 | E | E | E | 3/3 |
| P11 | W | S | S | 2/3 |
| P12 | S | E | W | 2/3 |
| P13 | E | E | S | 3/3 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | D | 2/3 |
| P16 | E | X | D | 1/2 |
| P17 | X | S | S | 2/2 |
| P18 | S | E | D | 2/3 |
| P19 | S | D | D | 1/3 |
| P20 | S | S | W | 2/3 |
| **Total** |  |  |  | **45/57** |

## Third-pass outcomes

New equivalent results:
`P09-T3`, `P10-T1`, `P10-T2`, `P10-T3`, and `P12-T2`.

New stronger results:
`P04-T1`, `P05-T1`, `P05-T2`, `P05-T3`, `P11-T3`, and
`P18-T1`.

The 12 third-pass tasks that remain unaccepted are:
`P04-T2`, `P06-T1`, `P08-T3`, `P09-T2`, `P11-T1`, `P12-T3`,
`P15-T3`, `P16-T3`, `P18-T3`, `P19-T2`, `P19-T3`, and
`P20-T3`.

## P10-T3 resolution

`P10-T3` was reselected from the defective Sylvester recurrence to the
unnumbered three-by-three block inverse on PDF page 12, printed page 70. The
fresh audit was adjudicated `faithful-equivalent`: the selected result is the
finite inverse identity and exact `A*B` block-extraction fact, while the
asymptotic inversion-to-multiplication complexity claim is surrounding
Theorem 3.3 context rather than an omitted conjunct.

## Exclusions

- `P07-T2`: the paper identifies a perturbed least-squares solution with an
  exact perturbed-system solution, but its pseudoinverse proof does not imply
  that equation for a tall system unless the perturbed right-hand side is in
  the perturbed matrix's range. The proof also needs full column rank. The
  rebuilt target adds both hypotheses, making it a project-corrected theorem
  rather than an ordinary paper-faithful translation.
- `P16-T2`: the published proof uses the unstated first-order comparison
  `||xHat_i||_2 lesssim ||xHat_(i+1)||_2`; without it, the printed recurrence
  has a concrete one-dimensional counterexample. The rebuilt target makes the
  comparison explicit, so it too is a project-corrected theorem.
- `P17-T1`: published Theorem 3.6 is contradicted by a concrete
  counterexample. Its ordinary audit classification remains provenance and is
  not an acceptance signal.

The exclusions do not change the audit protocol. They record source-validity
exceptions for these tasks, whose ordinary faithfulness tags are not counted.

## Validation

All 23 third-pass bundles passed complete-phase validation at their exact
evidence commits. All 34 carried-forward accepted results retain unchanged
targets and target-relevant declaration semantics. After the P07, P10, and P16
corrections, regenerated inventories for the six accepted sibling tasks
`P07-T1`, `P07-T3`, `P10-T1`, `P10-T2`, `P16-T1`, and `P16-T3`
found zero changed, missing, or added semantic dependencies. `P07-T3`'s task
metadata hash changed only because its execution limits changed; its target,
context, paper, and semantic dependency inventory are unchanged.

## Interpretation

Audit 3 closes with 45 accepted tasks among 57 ordinary eligible tasks, 12
unaccepted tasks, no pending tasks, and three documented source-validity
exclusions. Acceptance measures faithfulness to the selected paper result; it
does not establish benchmark difficulty, usefulness, or measurement readiness.
