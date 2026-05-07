# Run Analysis

- task: `E09_LapackNormalEquations`
- run_timestamp: `20260507-223046`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E09_LapackNormalEquations/20260507-223046`

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
condition_a	0	1	no	2026-05-07T19:31:07Z	2026-05-07T19:34:32Z	54	104	98	0	0
condition_c	0	1	no	2026-05-07T19:34:32Z	2026-05-07T19:36:28Z	62	31	25	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E09_LapackNormalEquations/20260507-223046/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E09_LapackNormalEquations/20260507-223046/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
✖ [1966/1967] Building BenchmarkTask (3.7s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_a/E09_LapackNormalEquations/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_a/E09_LapackNormalEquations/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_a/E09_LapackNormalEquations/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_a/E09_LapackNormalEquations/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_a/E09_LapackNormalEquations/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_a/E09_LapackNormalEquations/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:73:20: Unknown identifier `abs_add`
error: BenchmarkTask.lean:96:14: No goals to be solved
error: BenchmarkTask.lean:108:14: `simp` made no progress
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```

### condition_c

```text
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:77:5: unused variable `hΔR`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:144:5: unused variable `hc₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:144:20: unused variable `hc₂`

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
✖ [2029/2030] Building BenchmarkTask (2.9s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/condition-c-snapshots/leanprover-lean4-v4.29.0-rc3-d19a800d98f8fe6f/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_c/E09_LapackNormalEquations/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_c/E09_LapackNormalEquations/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_c/E09_LapackNormalEquations/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_c/E09_LapackNormalEquations/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_c/E09_LapackNormalEquations/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations-20260507-223046/condition_c/E09_LapackNormalEquations/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:45:10: Type mismatch
  mul_le_mul_of_nonneg_right (hDeltaG j k) (abs_nonneg ?m.314)
has type
  |DeltaG j k| * |?m.314| ≤ epsG * |ATA j k| * |?m.314|
but is expected to have type
  |DeltaG j k| * |xhat k| ≤ epsG * (|ATA j k| * |xhat k|)
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```
