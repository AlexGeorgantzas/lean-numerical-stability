# Faithfulness audit 002

## Snapshot

- Status: `completed`
- Baseline: `audit_001` at `df483a11408fa7b7440bbc1907c93bb9b3e610fa`
- Corpus: 20 papers and 60 tasks
- Eligible scope: 59 tasks after excluding `P17-T1`
- Fully validated results: 59 tasks
- Pending: none
- Recorded: `2026-08-21T10:16:27Z`
- Latest audit reference: branch `benchmark_faithfulness_audit`, commit `50ef267005b75d218510bbc148093a2bea89cbc6`
- Evidence model: every rerun is pinned to its own audit commit because later
  sibling repairs may change a paper's shared definitions. P20-T1 and P20-T3
  use the exact input snapshot at `f29d0da116de60c6c23f7d79c75b70997693304d`,
  with their audit artifacts pinned separately.

Task-local audit bundles remain the detailed evidence. [`results.json`](results.json)
records each task's disposition, prior and current result, artifact hashes,
evidence commit, and validation status.

## Progress from Audit 1

| View | Resolved | Accepted | Not accepted | Change from Audit 1 |
|---|---:|---:|---:|---:|
| Fully validated | 59 | 34 | 25 | +17 accepted |
| Audit 1 baseline | 60 | 17 | 43 | - |

The validated total consists of 17 unchanged Audit 1 successes and 42 rebuilt
tasks whose second-pass bundles validate against their exact controlled inputs.
Of those 42 rebuilds, 17 became accepted and 25 remain unaccepted.

Newly accepted, fully validated:
`P03-T2`, `P03-T3`, `P04-T3`, `P06-T3`, `P07-T1`, `P11-T2`, `P13-T1`, `P13-T3`, `P14-T1`, `P15-T1`, `P15-T2`, `P16-T1`, `P17-T2`, `P17-T3`, `P18-T2`, `P20-T1`, `P20-T2`.

The final two audits classified `P13-T1` as `faithful-equivalent` and
`P20-T2` as `faithful-stronger`. P13's finite perturbation bound and attaining
witness are exact consequences of the formalized condition-number statement.
P20 proves equation (3.13) for a broader abstract class of input-rounding maps.

## Validated aggregate

| Classification | Count | Accepted |
|---|---:|---|
| `faithful-equivalent` | 13 | yes |
| `faithful-stronger` | 21 | yes |
| `not-faithful-weaker` | 11 | no |
| `not-faithful-different` | 13 | no |
| `undetermined` | 1 | no |
| **Total** | **59** | **34** |

## Results by tier

| Tier | Equivalent | Stronger | Weaker | Different | Undetermined | Accepted |
|---|---:|---:|---:|---:|---:|---:|
| T1 | 4 | 9 | 4 | 1 | 1 | 13/19 |
| T2 | 6 | 6 | 3 | 5 | 0 | 12/20 |
| T3 | 3 | 6 | 4 | 7 | 0 | 9/20 |

## Paper matrix

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different, `U`
undetermined, `P` pending, and `X` excluded. Only `E` and `S` are accepted.

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
| P13 | E | E | S | 3/3 |
| P14 | S | S | E | 3/3 |
| P15 | E | E | D | 2/3 |
| P16 | E | W | D | 1/3 |
| P17 | X | S | S | 2/2 |
| P18 | U | E | W | 1/3 |
| P19 | S | D | W | 1/3 |
| P20 | S | S | D | 2/3 |
| **Validated total** |  |  |  | **34/59** |

## Still not accepted

The 25 fully validated second-pass results that remain unaccepted are:
`P04-T1`, `P04-T2`, `P05-T1`, `P05-T2`, `P05-T3`, `P06-T1`, `P07-T2`, `P08-T3`, `P09-T2`, `P09-T3`, `P10-T1`, `P10-T2`, `P10-T3`, `P11-T1`, `P11-T3`, `P12-T2`, `P12-T3`, `P15-T3`, `P16-T2`, `P16-T3`, `P18-T1`, `P18-T3`, `P19-T2`, `P19-T3`, `P20-T3`.

## Excluded task

- `P17-T1`: excluded because published Theorem 3.6 is contradicted. Its normal
  audit classification remains historical provenance and is not an acceptance
  signal. The later corrected rebuild is outside this Audit 2 snapshot.

## Interpretation

The second repair pass raised validated acceptance from 17 to 34 tasks, with 17
repaired tasks crossing into an accepted category. Audit 2 is complete for its
59-task eligible corpus; `P17-T1` remains outside the denominator under the
recorded source-validity exception.
