# Run Analysis

- task: `E05_LapackTriangularResidual`
- run_timestamp: `20260507-205025`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E05_LapackTriangularResidual/20260507-205025`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `no`
- Condition A classification: failed: final Lean file did not build
- Condition C validation exit: `0`
- Condition C timeout: `no`
- Condition C classification: passed validation

Interpretation: Condition A failed while Condition C passed under the same run protocol.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T17:50:47Z	2026-05-07T18:07:22Z	131	68	62	0	0
condition_c	0	0	no	2026-05-07T18:07:22Z	2026-05-07T18:09:46Z	69	55	49	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E05_LapackTriangularResidual/20260507-205025/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E05_LapackTriangularResidual/20260507-205025/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
✖ [1966/1967] Building BenchmarkTask (2.0s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_a/E05_LapackTriangularResidual/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_a/E05_LapackTriangularResidual/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_a/E05_LapackTriangularResidual/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_a/E05_LapackTriangularResidual/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_a/E05_LapackTriangularResidual/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_a/E05_LapackTriangularResidual/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:35:4: Unknown identifier `LeanFpAnalysis.FP.backSub_backward_error`
error: BenchmarkTask.lean:34:9: Tactic `rcases` failed: `x✝ : ?m.143` is not an inductive datatype
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
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
✔ [2029/2030] Built BenchmarkTask (2.6s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/E05_LapackTriangularResidual-20260507-205025/condition_c/E05_LapackTriangularResidual
```
