# Faithfulness audit 003

## Snapshot

- Status: `completed-with-pending-source-decisions`
- Baseline: `audit_002` at history commit
  `ceaed089455cb1a57f69b3c6f93dda9d4f15d947`
- Corpus: 20 papers and 60 tasks
- Eligible scope: 59 tasks after excluding `P17-T1`
- Settled results: 56 tasks
- Pending source decisions: `P07-T2`, `P10-T3`, and `P16-T2`
- Third-pass rebuilt and independently audited tasks: 22
- Recorded: `2026-08-22T03:31:47Z`
- Latest audit reference: branch `benchmark_faithfulness_audit`, commit
  `e826151e14e46ad11fa158c4f141dcb03f181d1e`
- Evidence model: each third-pass result is pinned to its own audit commit.
  Carried-forward Audit 2 successes were retained only after confirming
  unchanged target, context, metadata, paper, and target-relevant declaration
  semantics.

Task-local audit bundles remain the detailed evidence. [`results.json`](results.json)
records each task's disposition, Audit 2 result, current result where settled,
artifact hashes, evidence commit, and validation status.

## Progress from Audit 2

| View | Settled | Accepted | Not accepted | Pending |
|---|---:|---:|---:|---:|
| Audit 3 eligible corpus | 56 | 44 | 12 | 3 |
| Audit 2 eligible corpus | 59 | 34 | 25 | 0 |
| Third-pass reruns only | 22 | 10 | 12 | - |

Pass 3 raised accepted task count from 34 to 44. Ten of the 22 rebuilt and
audited tasks moved into an accepted category; 12 remain unaccepted. The three
source-blocked tasks are outside the settled denominator until the selected
source claim is corrected or replaced.

Newly accepted in Pass 3:
`P04-T1`, `P05-T1`, `P05-T2`, `P05-T3`, `P09-T3`, `P10-T1`,
`P10-T2`, `P11-T3`, `P12-T2`, and `P18-T1`.

## Settled aggregate

| Classification | Count | Accepted |
|---|---:|---|
| `faithful-equivalent` | 17 | yes |
| `faithful-stronger` | 27 | yes |
| `not-faithful-weaker` | 7 | no |
| `not-faithful-different` | 5 | no |
| **Total** | **56** | **44** |

## Results by tier

| Tier | Equivalent | Stronger | Weaker | Different | Accepted |
|---|---:|---:|---:|---:|---:|
| T1 | 5 | 12 | 2 | 0 | 17/19 |
| T2 | 8 | 7 | 2 | 1 | 15/18 |
| T3 | 4 | 8 | 3 | 4 | 12/19 |

Two T2 tasks and one T3 task are pending, so the tier denominators count only
settled eligible tasks.

## Paper matrix

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different,
`P` pending, and `X` excluded. Only `E` and `S` are accepted.

| Paper | T1 | T2 | T3 | Accepted/settled |
|---|---:|---:|---:|---:|
| P01 | E | E | E | 3/3 |
| P02 | S | S | S | 3/3 |
| P03 | S | E | S | 3/3 |
| P04 | S | W | S | 2/3 |
| P05 | S | S | S | 3/3 |
| P06 | W | E | E | 2/3 |
| P07 | S | P | S | 2/2 |
| P08 | S | S | W | 2/3 |
| P09 | S | W | E | 2/3 |
| P10 | E | E | P | 2/2 |
| P11 | W | S | S | 2/3 |
| P12 | S | E | W | 2/3 |
| P13 | E | E | S | 3/3 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | D | 2/3 |
| P16 | E | P | D | 1/2 |
| P17 | X | S | S | 2/2 |
| P18 | S | E | D | 2/3 |
| P19 | S | D | D | 1/3 |
| P20 | S | S | W | 2/3 |
| **Settled total** |  |  |  | **44/56** |

## Third-pass outcomes

New equivalent results:
`P09-T3`, `P10-T1`, `P10-T2`, and `P12-T2`.

New stronger results:
`P04-T1`, `P05-T1`, `P05-T2`, `P05-T3`, `P11-T3`, and
`P18-T1`.

The 12 settled third-pass tasks that remain unaccepted are:
`P04-T2`, `P06-T1`, `P08-T3`, `P09-T2`, `P11-T1`, `P12-T3`,
`P15-T3`, `P16-T3`, `P18-T3`, `P19-T2`, `P19-T3`, and
`P20-T3`.

## Pending source decisions

- `P07-T2`: the selected theorem contains incompatible perturbed-solution
  claims and omits range and rank conditions required by its proof.
- `P10-T3`: the printed recurrence omits first-order terms, so a sound
  correction cannot retain the selected equation-(20) bound unchanged.
- `P16-T2`: the printed recurrence requires an unstated iterate comparison.
  Its latest ordinary audit is valid but remains `not-faithful-weaker`; it
  does not resolve the source-selection problem.

These are pending project decisions, not failed or missing audit executions.
The detailed source evidence is recorded in
[`REBUILD_PASS_003.md`](../../../task_builder/REBUILD_PASS_003.md).

## Excluded task

- `P17-T1`: excluded because published Theorem 3.6 is contradicted. Its
  ordinary audit classification remains provenance and is not an acceptance
  signal.

## Validation

All 22 settled third-pass bundles passed complete-phase validation at their
exact evidence commits. All 34 carried-forward accepted results retain
unchanged targets, contexts, metadata, papers, and target-relevant declaration
semantics. For the 15 accepted sibling tasks whose paper-specific definition
modules changed during Pass 3, regenerated semantic inventories found zero
changed, missing, or added dependencies.

## Interpretation

Pass 3 substantially improved the corpus, but it did not make every settled
task faithful: 12 still require another rebuild or a deliberate source
decision. The snapshot reports 44 accepted tasks among 56 settled eligible
tasks, with three additional tasks pending and one excluded. Acceptance measures
faithfulness to the selected paper result; it does not establish benchmark
difficulty, usefulness, or measurement readiness.
