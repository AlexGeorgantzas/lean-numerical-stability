# Run Analysis

- task: `T06_TriangularSolveSingle`
- run_timestamp: `20260505-204309`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/T06_TriangularSolveSingle/20260505-204309`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `no`
- Condition C validation exit: `0`
- Condition C timeout: `no`

Interpretation: Condition A failed while Condition C passed under the same run protocol.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-05T17:43:28Z	2026-05-05T17:46:13Z	47	0	4	0	0
condition_c	0	0	no	2026-05-05T17:46:13Z	2026-05-05T17:49:25Z	80	114	108	0	0
```

## Failure Notes


### condition_a

```text
23:  sorry
validation failed: attempted task still contains sorry/admit
⚠ [854/855] Replayed BenchmarkTask
warning: BenchmarkTask.lean:7:8: declaration uses `sorry`
Build completed successfully (855 jobs).
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
✔ [2029/2030] Built BenchmarkTask (2.7s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-204309/condition_c/T06_TriangularSolveSingle
```
