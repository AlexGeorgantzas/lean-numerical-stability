# Persistent GPT-5.5 xhigh 40-Minute Suite, May 8 2026

This suite reruns the external-source stability tasks E01-E10 under a stronger
solver protocol:

- `BENCHMARK_CODEX_MODEL=gpt-5.5`
- `BENCHMARK_CODEX_REASONING_EFFORT=xhigh`
- `BENCHMARK_SOLVER_PROMPT_VARIANT=persistent`
- `BENCHMARK_CODEX_TIMEOUT_SECONDS=2400`

The run was archived separately from the earlier standard pass@1 results by
using result task names with the suffix `_gpt55_xhigh_persistent40`.  Therefore
these reruns do not overwrite or replace the standard-prompt pass@1 archives.

Suite metadata and per-task runner logs are in:

`benchmark/results/gpt55_xhigh_persistent40_suite_20260508/`

Plots and aggregate machine-readable metrics are in:

`benchmark/results/plots/persistent40_xhigh_20260508/`

## Outcome

All ten tasks passed in both Condition A and Condition C under this stronger
protocol.

This changes the interpretation relative to the standard-prompt benchmark.
With GPT-5.5 xhigh, persistent instructions, and 40 minutes per condition, the
current E-suite no longer provides pass/fail separation.  It instead shows an
efficiency and proof-size gap: Condition C generally solves the same stability
theorems much faster and with much shorter proofs.

Aggregate timing:

```text
Condition A total solver time: 155.84 minutes
Condition C total solver time: 25.71 minutes
Condition A average per task: 15.58 minutes
Condition C average per task: 2.57 minutes
```

Aggregate proof-body size:

```text
Condition A average proof lines: 254.4
Condition C average proof lines: 47.5
```

## Task Results

| Task | A Result | C Result | A Minutes | C Minutes | A Proof Lines | C Proof Lines |
|---|---:|---:|---:|---:|---:|---:|
| E01 LAPACK BERR | pass | pass | 26.32 | 3.68 | 371 | 43 |
| E02 Residual Stop | pass | pass | 18.85 | 2.78 | 375 | 60 |
| E03 LAPACK FERR | pass | pass | 24.97 | 3.20 | 408 | 139 |
| E04 Level 3 GEMM | pass | pass | 21.37 | 3.20 | 272 | 49 |
| E05 Triangular Residual | pass | pass | 28.45 | 3.65 | 444 | 74 |
| E06 Oettli-Prager | pass | pass | 9.73 | 1.00 | 133 | 6 |
| E07 Stationary Residual | pass | pass | 16.77 | 1.65 | 255 | 15 |
| E08 LS QR | pass | pass | 3.53 | 1.45 | 136 | 7 |
| E09 Normal Equations | pass | pass | 3.93 | 1.83 | 98 | 37 |
| E10 SumK Certificate | pass | pass | 1.92 | 3.27 | 52 | 45 |

## Interpretation

This run should not be used to claim that Condition A fails on the current
E01-E10 suite.  Under this stronger protocol, it does not fail.

The run does support a different claim: the public library materially reduces
solver effort.  For E01-E09, Condition C is faster than Condition A, often by a
large factor, and usually produces substantially shorter proof bodies.  E10 is
an exception in elapsed time and was already identified as too close to its
task-local certificate assumptions.

The benchmark design consequence is that the current E-suite is useful for
testing an efficiency-gap story under strong persistence, but not sufficient
for the intended hard pass/fail separation.  Harder final tasks should avoid
exposing the key stability facts as task-local assumptions and should require
composition of nontrivial library stability contracts that are absent from
Condition A.
