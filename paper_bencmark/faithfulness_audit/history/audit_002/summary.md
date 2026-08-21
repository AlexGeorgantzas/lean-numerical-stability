# Faithfulness audit 002

## Snapshot

- Status: `in-progress`
- Baseline: `audit_001` at `df483a11408fa7b7440bbc1907c93bb9b3e610fa`
- Corpus: 20 papers and 60 tasks
- Eligible scope: 59 tasks after excluding `P17-T1`
- Fully validated results: 55 tasks
- Additional provisional decisions: 2 tasks
- Pending: `P13-T1`, `P20-T2`
- Recorded: `2026-08-21T07:27:31Z`
- Latest audit reference: branch `benchmark_faithfulness_audit`, commit `f47b4d4e38b47005a87228564a678d60615b76a8`
- Evidence model: every rerun is pinned to its own audit commit because later
  sibling repairs may change a paper's shared definitions

Task-local audit bundles remain the detailed evidence. [`results.json`](results.json)
records each task's disposition, prior and current result, artifact hashes,
evidence commit, and validation status.

## Progress from Audit 1

| View | Resolved | Accepted | Not accepted | Change from Audit 1 |
|---|---:|---:|---:|---:|
| Fully validated | 55 | 31 | 24 | +14 accepted |
| Including provisional P20 decisions | 57 | 32 | 25 | +15 accepted |
| Audit 1 baseline | 60 | 17 | 43 | - |

The validated total consists of 17 unchanged Audit 1 successes and 38 rebuilt
tasks whose second-pass bundles validate at their exact audit commits. Of those
38 rebuilds, 14 became accepted and 24 remain unaccepted. Including the two
provisional P20 decisions adds one accepted result (`P20-T1`) and one
undetermined result (`P20-T3`).

Newly accepted, fully validated:
`P03-T2`, `P03-T3`, `P04-T3`, `P06-T3`, `P07-T1`, `P11-T2`, `P13-T3`, `P14-T1`, `P15-T1`, `P15-T2`, `P16-T1`, `P17-T2`, `P17-T3`, `P18-T2`.

The provisional P20 result would additionally add `P20-T1`.

## Validated aggregate

| Classification | Count | Accepted |
|---|---:|---|
| `faithful-equivalent` | 12 | yes |
| `faithful-stronger` | 19 | yes |
| `not-faithful-weaker` | 11 | no |
| `not-faithful-different` | 12 | no |
| `undetermined` | 1 | no |
| **Total** | **55** | **31** |

## Results by tier

| Tier | Equivalent | Stronger | Weaker | Different | Undetermined | Accepted |
|---|---:|---:|---:|---:|---:|---:|
| T1 | 3 | 8 | 4 | 1 | 1 | 11/17 |
| T2 | 6 | 5 | 3 | 5 | 0 | 11/19 |
| T3 | 3 | 6 | 4 | 6 | 0 | 9/19 |

## Paper matrix

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different, `U`
undetermined, `P` pending, and `X` excluded. `*` marks a decision whose exact
audited controlled inputs are not recoverable from its audit commit. Only `E`
and `S` are accepted.

| Paper | T1 | T2 | T3 | Accepted/resolved |
|---|---:|---:|---:|---:|
| P01 | E | E | E | 3/3 |
| P02 | S | S | S | 3/3 |
| P03 | S | E | S | 3/3 |
| P04 | W | D | S | 1/3 |
| P05 | D | D | W | 0/3 |
| P06 | W | E | E | 2/3 |
| P07 | S | W | S | 2/3 |
| P08 | S | S | D | 2/3 |
| P09 | S | D | D | 1/3 |
| P10 | W | D | D | 0/3 |
| P11 | W | S | D | 1/3 |
| P12 | S | W | W | 1/3 |
| P13 | P | E | S | 2/2 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | D | 2/3 |
| P16 | E | W | D | 1/3 |
| P17 | X | S | S | 2/2 |
| P18 | U | E | W | 1/3 |
| P19 | S | D | W | 1/3 |
| P20 | S* | P | U* | 1/2 |
| **Validated total** |  |  |  | **31/55** |
| **Including provisional** |  |  |  | **32/57** |

## Still not accepted

The 24 fully validated second-pass results that remain unaccepted are:
`P04-T1`, `P04-T2`, `P05-T1`, `P05-T2`, `P05-T3`, `P06-T1`, `P07-T2`, `P08-T3`, `P09-T2`, `P09-T3`, `P10-T1`, `P10-T2`, `P10-T3`, `P11-T1`, `P11-T3`, `P12-T2`, `P12-T3`, `P15-T3`, `P16-T2`, `P16-T3`, `P18-T1`, `P18-T3`, `P19-T2`, `P19-T3`.

`P20-T3` is additionally provisional and undetermined.

## Open items

- `P13-T1`: rebuilt at `0b352487ea2b4b55e09486be9ff06a082724e371`, but never re-audited. Its
  Audit 1 decision is stale for the rebuilt target.
- `P20-T1` and `P20-T3`: second-pass decisions exist, but the exact audited
  targets and `P20Definitions.lean` were not committed with their audit
  artifacts. They are reported provisionally, not counted as fully validated.
- `P20-T2`: the selected comparison is false under literal Model 1 and the task
  awaits source reselection and rebuild around equation (3.16), subject to a
  genuine T2 dependency check.
- `P17-T1`: excluded because published Theorem 3.6 is contradicted. Its normal
  audit classification remains historical provenance and is not an acceptance
  signal.

## Interpretation

The second repair pass produced substantial progress: validated acceptance rose
from 17 to 31 tasks, with 14 repaired tasks crossing into an accepted category.
The decision-reported view reaches 32 accepted tasks when provisional `P20-T1`
is included. Audit 2 is not complete until the pending tasks and P20 provenance
gaps are resolved; these totals must not be presented as the final 59-task
eligible-corpus result.
