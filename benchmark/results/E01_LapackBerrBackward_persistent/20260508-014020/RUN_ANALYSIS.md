# Run Analysis

- task: `E01_LapackBerrBackward_persistent`
- run_timestamp: `20260508-014020`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E01_LapackBerrBackward_persistent/20260508-014020`

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
condition_a	0	1	no	2026-05-07T22:40:58Z	2026-05-07T22:49:28Z	91	147	141	0	0
condition_c	0	0	no	2026-05-07T22:49:28Z	2026-05-07T22:53:07Z	58	180	174	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E01_LapackBerrBackward_persistent/20260508-014020/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E01_LapackBerrBackward_persistent/20260508-014020/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
exactResidual : Fin n → ℝ := fun i => b i - ∑ j, A i j * x j
denom : Fin n → ℝ := lapackBerrDenom n A x b
sgn : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1
theta : Fin n → ℝ := fun i => if denom i = 0 then 0 else exactResidual i / denom i
i j : Fin n
hden : ¬denom i = 0
hden_nonneg : 0 ≤ denom i
hden_pos : 0 < denom i
a✝ : |fl_residual fp n A x b i| + gamma fp (n + 1) * denom i < |exactResidual i|
⊢ False
failed
error: BenchmarkTask.lean:86:12: linarith failed to find a contradiction
case h
fp : FPModel
n : ℕ
A : Fin n → Fin n → ℝ
x b : Fin n → ℝ
eta : ℝ
hn : gammaValid fp n
hn1 : gammaValid fp (n + 1)
heta_nonneg : 0 ≤ eta
hcert :
  ∀ (i : Fin n),
    |fl_residual fp n A x b i| + gamma fp (n + 1) * lapackBerrDenom n A x b i ≤ eta * lapackBerrDenom n A x b i
exactResidual : Fin n → ℝ := fun i => b i - ∑ j, A i j * x j
denom : Fin n → ℝ := lapackBerrDenom n A x b
sgn : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1
theta : Fin n → ℝ := fun i => if denom i = 0 then 0 else exactResidual i / denom i
i : Fin n
hden : ¬denom i = 0
hden_nonneg : 0 ≤ denom i
hden_pos : 0 < denom i
a✝ : |fl_residual fp n A x b i| + gamma fp (n + 1) * denom i < |exactResidual i|
⊢ False
failed
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
✔ [2029/2030] Built BenchmarkTask (4.3s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/E01_LapackBerrBackward_persistent-20260508-014020/condition_c/E01_LapackBerrBackward
```
