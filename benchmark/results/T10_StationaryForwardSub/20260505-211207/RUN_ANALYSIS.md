# Run Analysis

- task: `T10_StationaryForwardSub`
- run_timestamp: `20260505-211207`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/T10_StationaryForwardSub/20260505-211207`

## Outcome

- Condition A validation exit: `0`
- Condition A timeout: `no`
- Condition C validation exit: `0`
- Condition C timeout: `no`

Interpretation: both conditions passed; this task may not separate library access from the bare environment.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	0	no	2026-05-05T18:12:27Z	2026-05-05T18:14:43Z	70	10	4	0	0
condition_c	0	0	no	2026-05-05T18:14:43Z	2026-05-05T18:17:45Z	80	86	80	0	0
```

## Failure Notes


### condition_a

```text
⚠ [854/855] Built BenchmarkTask (1.7s)
warning: BenchmarkTask.lean:12:5: unused variable `hS`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:13:5: unused variable `hAx`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:14:5: unused variable `hMdiag`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:15:5: unused variable `hMLT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:16:5: unused variable `hgamma`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:17:5: unused variable `hstep`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:21:5: unused variable `hq_nonneg`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:22:5: unused variable `hq_lt_one`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:23:5: unused variable `hH`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:24:5: unused variable `hμ_nonneg`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: BenchmarkTask.lean:25:5: unused variable `hlocal`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (855 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T10_StationaryForwardSub-20260505-211207/condition_a/T10_StationaryForwardSub
```

### condition_c

```text
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
✔ [2029/2030] Built BenchmarkTask (2.8s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T10_StationaryForwardSub-20260505-211207/condition_c/T10_StationaryForwardSub
```
