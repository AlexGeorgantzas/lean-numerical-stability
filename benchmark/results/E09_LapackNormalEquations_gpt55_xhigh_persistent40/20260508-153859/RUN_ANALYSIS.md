# Run Analysis

- task: `E09_LapackNormalEquations_gpt55_xhigh_persistent40`
- run_timestamp: `20260508-153859`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E09_LapackNormalEquations_gpt55_xhigh_persistent40/20260508-153859`

## Outcome

- Condition A validation exit: `0`
- Condition A timeout: `no`
- Condition A classification: passed validation
- Condition C validation exit: `0`
- Condition C timeout: `no`
- Condition C classification: passed validation

Interpretation: both conditions passed; this task may not separate library access from the bare environment.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	0	no	2026-05-08T12:39:23Z	2026-05-08T12:43:19Z	44	104	98	0	0
condition_c	0	0	no	2026-05-08T12:43:19Z	2026-05-08T12:45:09Z	53	43	37	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E09_LapackNormalEquations_gpt55_xhigh_persistent40/20260508-153859/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E09_LapackNormalEquations_gpt55_xhigh_persistent40/20260508-153859/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
✔ [1966/1967] Built BenchmarkTask (14s)
Build completed successfully (1967 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations_gpt55_xhigh_persistent40-20260508-153859/condition_a/E09_LapackNormalEquations
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
✔ [2029/2030] Built BenchmarkTask (3.0s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/E09_LapackNormalEquations_gpt55_xhigh_persistent40-20260508-153859/condition_c/E09_LapackNormalEquations
```
