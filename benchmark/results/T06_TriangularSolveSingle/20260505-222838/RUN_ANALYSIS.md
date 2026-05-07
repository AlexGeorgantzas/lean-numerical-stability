# Run Analysis

- task: `T06_TriangularSolveSingle`
- run_timestamp: `20260505-222838`
- result_root: `benchmark/results/T06_TriangularSolveSingle/20260505-222838`

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
condition_a	0	1	no	2026-05-05T19:29:00Z	2026-05-05T19:36:00Z	93	20	14	0	0
condition_c	0	0	no	2026-05-05T19:36:00Z	2026-05-05T19:38:51Z	68	117	111	0	0
```

## Public Solver Messages

- Condition A: `benchmark/results/T06_TriangularSolveSingle/20260505-222838/condition_a/agent_messages.md`
- Condition C: `benchmark/results/T06_TriangularSolveSingle/20260505-222838/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
✖ [956/957] Building BenchmarkTask (2.4s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_a/T06_TriangularSolveSingle/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_a/T06_TriangularSolveSingle/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_a/T06_TriangularSolveSingle/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_a/T06_TriangularSolveSingle/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_a/T06_TriangularSolveSingle/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_a/T06_TriangularSolveSingle/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:25:26: failed to synthesize instance of type class
  Nonempty
    (∃ ΔA,
      (∀ (i j : Fin n), |ΔA i j| ≤ (2 * gamma fp n + gamma fp n ^ 2) * ∑ k, |L i k| * |U k j|) ∧
        ∀ (i : Fin n), ∑ j, (∑ k, L i k * U k j + ΔA i j) * fl_backSub fp n U (fl_forwardSub fp n L b) j = b i)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
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
✔ [2029/2030] Built BenchmarkTask (11s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T06_TriangularSolveSingle-20260505-222838/condition_c/T06_TriangularSolveSingle
```
