# Run Analysis

- task: `E01_LapackBerrBackward_gpt55_xhigh_persistent`
- run_timestamp: `20260508-021347`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E01_LapackBerrBackward_gpt55_xhigh_persistent/20260508-021347`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `yes`
- Condition A classification: failed: proof placeholder remained
- Condition C validation exit: `0`
- Condition C timeout: `no`
- Condition C classification: passed validation

Interpretation: Condition A failed while Condition C passed under the same run protocol.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	124	1	yes	2026-05-07T23:14:22Z	2026-05-07T23:34:28Z	88	0	4	1	0
condition_c	0	0	no	2026-05-07T23:34:28Z	2026-05-07T23:39:40Z	74	142	136	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E01_LapackBerrBackward_gpt55_xhigh_persistent/20260508-021347/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E01_LapackBerrBackward_gpt55_xhigh_persistent/20260508-021347/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

timed out after 1200 seconds

```text
31:  sorry
validation failed: attempted task still contains sorry/admit/sorryAx
⚠ [1966/1967] Replayed BenchmarkTask
warning: BenchmarkTask.lean:19:8: declaration uses `sorry`
Build completed successfully (1967 jobs).
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
✔ [2029/2030] Built BenchmarkTask (8.0s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/E01_LapackBerrBackward_gpt55_xhigh_persistent-20260508-021347/condition_c/E01_LapackBerrBackward
```
