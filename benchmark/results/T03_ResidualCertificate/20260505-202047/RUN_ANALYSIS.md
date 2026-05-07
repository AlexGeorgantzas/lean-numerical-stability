# Run Analysis

- task: `T03_ResidualCertificate`
- run_timestamp: `20260505-202047`
- result_root: `benchmark/results/T03_ResidualCertificate/20260505-202047`

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
condition_a	0	1	no	2026-05-05T17:21:05Z	2026-05-05T17:26:08Z	68	28	22	0	0
condition_c	0	0	no	2026-05-05T17:26:08Z	2026-05-05T17:29:07Z	73	29	23	0	0
```

## Public Solver Messages

- Condition A: `benchmark/results/T03_ResidualCertificate/20260505-202047/condition_a/agent_messages.md`
- Condition C: `benchmark/results/T03_ResidualCertificate/20260505-202047/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
✖ [854/855] Building BenchmarkTask (1.8s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_a/T03_ResidualCertificate/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_a/T03_ResidualCertificate/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_a/T03_ResidualCertificate/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_a/T03_ResidualCertificate/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_a/T03_ResidualCertificate/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_a/T03_ResidualCertificate/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:24:4: tactic 'aesop' failed, made no progress
Initial goal:
  fp : FPModel
  n : ℕ
  A : Fin n → Fin n → ℝ
  x b τ : Fin n → ℝ
  hn : gammaValid fp n
  hn1 : gammaValid fp (n + 1)
  hτ_nonneg : ∀ (i : Fin n), 0 ≤ τ i
  hsmall : ∀ (i : Fin n), |fl_residual fp n A x b i| ≤ τ i
  i : Fin n
  ⊢ |b i - ∑ j, A i j * x j - fp.fl_sub (b i) (fl_dotProduct fp n (A i) x)| ≤
      gamma fp (n + 1) * (|b i| + ∑ j, |A i j| * |x j|)
error: BenchmarkTask.lean:30:40: Unknown identifier `abs_add`
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```

### condition_c

```text
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:73:5: unused variable `hΔA₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:77:5: unused variable `hΔR`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:144:5: unused variable `hc₁`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/QRSolve.lean:144:20: unused variable `hc₂`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2013/2030] Replayed LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean:122:5: unused variable `hε_G`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean:122:22: unused variable `hε_g`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2014/2030] Replayed LeanFpAnalysis.FP.Algorithms.LeastSquares.LSNormalEquations
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSNormalEquations.lean:101:5: unused variable `hm`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSNormalEquations.lean:205:5: unused variable `hKappa`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2016/2030] Replayed LeanFpAnalysis.FP.Algorithms.FastMatMul
warning: LeanFpAnalysis/FP/Algorithms/FastMatMul.lean:149:5: unused variable `hn`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2025/2030] Replayed LeanFpAnalysis.FP.Algorithms.QR.GivensQR
warning: LeanFpAnalysis/FP/Algorithms/QR/GivensQR.lean:69:44: unused variable `hr`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/GivensQR.lean:70:43: unused variable `hc`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [2029/2030] Built BenchmarkTask (2.7s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T03_ResidualCertificate-20260505-202047/condition_c/T03_ResidualCertificate
```
