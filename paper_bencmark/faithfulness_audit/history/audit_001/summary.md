# Faithfulness audit 001

## Snapshot

- Status: `completed`
- Scope: 20 papers (`P01`-`P20`), three tasks per paper, 60 tasks total
- Audit window: `2026-08-12T16:15:53.669034+00:00` to
  `2026-08-14T10:42:43.345829+00:00`
- Recorded: `2026-08-14T10:52:35Z`
- Protocol versions represented: `highambench-faithfulness-0.1` and
  `highambench-faithfulness-0.2`
- Repository: branch `benchmark_faithfulness_audit`, commit
  `df483a11408fa7b7440bbc1907c93bb9b3e610fa`
- Validation: all 60 completed task bundles passed
  `validate_audit.py --phase complete`

The task-local audit bundles at the pinned commit are the detailed evidence.
[`results.json`](results.json) records each target and paper hash plus the
hash-bound decision and report paths.

## Aggregate results

| Outcome | Count |
|---|---:|
| Accepted | 17 |
| Not accepted | 43 |
| Adjudicated | 30 |
| Total | 60 |

| Classification | Count | Accepted |
|---|---:|---|
| `faithful-equivalent` | 6 | yes |
| `faithful-stronger` | 11 | yes |
| `not-faithful-weaker` | 6 | no |
| `not-faithful-different` | 36 | no |
| `undetermined` | 1 | no |
| **Total** | **60** | **17** |

Of the 43 tasks not accepted, 42 were classified as unfaithful and one remained
undetermined.

## Results by tier

| Tier | Equivalent | Stronger | Weaker | Different | Undetermined | Accepted |
|---|---:|---:|---:|---:|---:|---:|
| T1 | 1 | 6 | 2 | 10 | 1 | 7/20 |
| T2 | 3 | 3 | 3 | 11 | 0 | 6/20 |
| T3 | 2 | 2 | 1 | 15 | 0 | 4/20 |

## Paper matrix

Legend: `E` equivalent, `S` stronger, `W` weaker, `D` different, and
`U` undetermined. Only `E` and `S` are accepted.

| Paper | T1 | T2 | T3 | Accepted |
|---|---:|---:|---:|---:|
| P01 | E | E | E | 3/3 |
| P02 | S | S | S | 3/3 |
| P03 | S | D | D | 1/3 |
| P04 | D | D | D | 0/3 |
| P05 | D | W | D | 0/3 |
| P06 | D | E | D | 1/3 |
| P07 | D | D | S | 1/3 |
| P08 | S | S | D | 2/3 |
| P09 | S | D | D | 1/3 |
| P10 | D | D | D | 0/3 |
| P11 | D | D | D | 0/3 |
| P12 | S | D | D | 1/3 |
| P13 | W | E | D | 1/3 |
| P14 | D | S | E | 2/3 |
| P15 | U | D | D | 0/3 |
| P16 | D | D | D | 0/3 |
| P17 | W | D | D | 0/3 |
| P18 | D | W | D | 0/3 |
| P19 | S | D | D | 1/3 |
| P20 | D | W | W | 0/3 |
| **Total** | **7/20** | **6/20** | **4/20** | **17/60** |

## Accepted tasks

Equivalent:
`P01-T1`, `P01-T2`, `P01-T3`, `P06-T2`, `P13-T2`, and `P14-T3`.

Stronger:
`P02-T1`, `P02-T2`, `P02-T3`, `P03-T1`, `P07-T3`, `P08-T1`,
`P08-T2`, `P09-T1`, `P12-T1`, `P14-T2`, and `P19-T1`.

## Interpretation

- Only P01 and P02 had all three targets accepted.
- P04, P05, P10, P11, P15, P16, P17, P18, and P20 had no accepted targets.
- T3 had the lowest acceptance rate and the most
  `not-faithful-different` classifications.
- `P15-T1` is the sole unresolved task; its final decision is
  `undetermined`.
- Acceptance here means semantic faithfulness to the selected paper result. It
  does not by itself establish that a task is useful, difficult, representative,
  or appropriate for the final model benchmark.
