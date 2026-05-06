# Run Analysis

- task: `T07_LUSolveGrowth`
- run_timestamp: `20260505-223851`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/T07_LUSolveGrowth/20260505-223851`

## Outcome

- Condition A validation exit: `0`
- Condition A timeout: `no`
- Condition C validation exit: `1`
- Condition C timeout: `no`

Interpretation: Condition A passed while Condition C failed; inspect harness or task setup.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	0	no	2026-05-05T19:39:14Z	2026-05-05T19:48:17Z	86	10	4	0	0
condition_c	0	1	no	2026-05-05T19:48:17Z	2026-05-05T19:50:57Z	61	29	17	0	0
```

## Failure Notes


### condition_a

```text
⚠ [956/957] Built BenchmarkTask (2.6s)
warning: BenchmarkTask.lean:7:8: declaration uses `sorry`
warning: BenchmarkTask.lean:10:5: unused variable `hLdiag`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:11:5: unused variable `hUdiag`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:12:5: unused variable `hLU`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:13:5: unused variable `hn`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:14:5: unused variable `hρ_nonneg`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:15:5: unused variable `hgrowth`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (957 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T07_LUSolveGrowth-20260505-223851/condition_a/T07_LUSolveGrowth
```

### condition_c

```text
Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/GivensQR.lean:70:43: unused variable `hc`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2020/2030] Replayed LeanFpAnalysis.FP.Algorithms.QR.QRSolve
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:67:51: unused variable `hn`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:73:5: unused variable `hΔA₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
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
✔ [2029/2030] Built BenchmarkTask (4.6s)
Build completed successfully (2030 jobs).
```
