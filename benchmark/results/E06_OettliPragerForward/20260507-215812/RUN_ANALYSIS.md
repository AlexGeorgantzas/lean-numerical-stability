# Run Analysis

- task: `E06_OettliPragerForward`
- run_timestamp: `20260507-215812`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E06_OettliPragerForward/20260507-215812`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `no`
- Condition A classification: failed: final Lean file did not build
- Condition C validation exit: `1`
- Condition C timeout: `no`
- Condition C classification: failed: final Lean file did not build

Interpretation: both conditions failed; inspect failure modes before drawing conclusions.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T18:58:32Z	2026-05-07T19:01:36Z	52	94	88	0	0
condition_c	0	1	no	2026-05-07T19:01:36Z	2026-05-07T19:03:50Z	56	105	99	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E06_OettliPragerForward/20260507-215812/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E06_OettliPragerForward/20260507-215812/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
✖ [1966/1967] Building BenchmarkTask (3.3s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_a/E06_OettliPragerForward/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_a/E06_OettliPragerForward/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_a/E06_OettliPragerForward/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_a/E06_OettliPragerForward/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_a/E06_OettliPragerForward/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_a/E06_OettliPragerForward/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:74:45: Unknown identifier `abs_add`
error: BenchmarkTask.lean:78:20: Application type mismatch: The argument
  fun k => DeltaA j k * xhat k
has type
  Fin n → ℝ
but is expected to have type
  Finset ?m.699
in the application
  Finset.abs_sum_le_sum_abs ?m.707 fun k => DeltaA j k * xhat k
error: BenchmarkTask.lean:77:45: Application type mismatch: The argument
  Finset.univ
has type
  Finset (Fin n)
but is expected to have type
  ?m.699 → ?m.700
in the application
  Finset.abs_sum_le_sum_abs Finset.univ
error: BenchmarkTask.lean:97:67: Application type mismatch: The argument
  fun j => A_inv i j * r j
has type
  Fin n → ℝ
but is expected to have type
  Finset ?m.840
in the application
  Finset.abs_sum_le_sum_abs ?m.848 fun j => A_inv i j * r j
error: BenchmarkTask.lean:97:36: Application type mismatch: The argument
  Finset.univ
has type
  Finset (Fin n)
but is expected to have type
  ?m.840 → ?m.841
in the application
  Finset.abs_sum_le_sum_abs Finset.univ
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```

### condition_c

```text
Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2022/2030] Replayed LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean:122:5: unused variable `hε_G`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean:122:22: unused variable `hε_g`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2023/2030] Replayed LeanFpAnalysis.FP.Algorithms.LeastSquares.LSNormalEquations
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSNormalEquations.lean:101:5: unused variable `hm`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSNormalEquations.lean:205:5: unused variable `hKappa`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2026/2030] Replayed LeanFpAnalysis.FP.Algorithms.FastMatMul
warning: LeanFpAnalysis/FP/Algorithms/FastMatMul.lean:149:5: unused variable `hn`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
✖ [2029/2030] Building BenchmarkTask (3.1s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/condition-c-snapshots/leanprover-lean4-v4.29.0-rc3-835a86d224396016/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_c/E06_OettliPragerForward/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_c/E06_OettliPragerForward/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_c/E06_OettliPragerForward/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_c/E06_OettliPragerForward/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_c/E06_OettliPragerForward/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-215812/condition_c/E06_OettliPragerForward/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:83:38: Application type mismatch: The argument
  abs_sub_le ?m.945 ?m.946
has type
  ∀ (c : ?m.941), |?m.945 - c| ≤ |?m.945 - ?m.946| + |?m.946 - c|
but is expected to have type
  |∑ k, DeltaA j k * xhat k - Deltab j| ≤ |∑ k, DeltaA j k * xhat k| + |Deltab j|
in the application
  mul_le_mul_of_nonneg_left (abs_sub_le ?m.945 ?m.946)
error: BenchmarkTask.lean:89:6: Type mismatch
  add_le_add_right (Finset.abs_sum_le_sum_abs ?m.992 ?m.993) ?m.994
has type
  ?m.994 + |∑ i ∈ ?m.993, ?m.992 i| ≤ ?m.994 + ∑ i ∈ ?m.993, |?m.992 i|
but is expected to have type
  |∑ k, DeltaA j k * xhat k| + |Deltab j| ≤ ∑ k, |DeltaA j k * xhat k| + |Deltab j|
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```
