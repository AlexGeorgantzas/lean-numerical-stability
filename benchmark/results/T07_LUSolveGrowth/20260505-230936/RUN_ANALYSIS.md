# Run Analysis

- task: `T07_LUSolveGrowth`
- run_timestamp: `20260505-230936`
- result_root: `benchmark/results/T07_LUSolveGrowth/20260505-230936`

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
condition_a	0	1	no	2026-05-05T20:09:59Z	2026-05-05T20:16:21Z	57	30	24	0	0
condition_c	0	0	no	2026-05-05T20:16:21Z	2026-05-05T20:17:29Z	36	20	14	0	0
```

## Public Solver Messages

- Condition A: `benchmark/results/T07_LUSolveGrowth/20260505-230936/condition_a/agent_messages.md`
- Condition C: `benchmark/results/T07_LUSolveGrowth/20260505-230936/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
fp : FPModel
n : ℕ
A Lhat Uhat : Fin n → Fin n → ℝ
b : Fin n → ℝ
ρ : ℝ
hLdiag : ∀ (i : Fin n), Lhat i i ≠ 0
hUdiag : ∀ (i : Fin n), Uhat i i ≠ 0
hLU : LUBackwardError n A Lhat Uhat (gamma fp n)
hn : gammaValid fp n
hρ_nonneg : 0 ≤ ρ
hgrowth : ∀ (i j : Fin n), ∑ k, |Lhat i k| * |Uhat k j| ≤ ρ * |A i j|
yhat : Fin n → ℝ := fl_forwardSub fp n Lhat b
xhat : Fin n → ℝ := fl_backSub fp n Uhat yhat
ΔA : Fin n → Fin n → ℝ := fun i j => ∑ k, Lhat i k * Uhat k j - A i j
i j : Fin n
h₁ : |∑ k, Lhat i k * Uhat k j - A i j| ≤ gamma fp n * ∑ k, |Lhat i k| * |Uhat k j|
h₂ : ∑ k, |Lhat i k| * |Uhat k j| ≤ ρ * |A i j|
⊢ gamma fp n * (ρ * |A i j|) ≤ (3 * gamma fp n + gamma fp n ^ 2) * ρ * |A i j|
error: BenchmarkTask.lean:23:59: unsolved goals
case refine_2
fp : FPModel
n : ℕ
A Lhat Uhat : Fin n → Fin n → ℝ
b : Fin n → ℝ
ρ : ℝ
hLdiag : ∀ (i : Fin n), Lhat i i ≠ 0
hUdiag : ∀ (i : Fin n), Uhat i i ≠ 0
hLU : LUBackwardError n A Lhat Uhat (gamma fp n)
hn : gammaValid fp n
hρ_nonneg : 0 ≤ ρ
hgrowth : ∀ (i j : Fin n), ∑ k, |Lhat i k| * |Uhat k j| ≤ ρ * |A i j|
yhat : Fin n → ℝ := fl_forwardSub fp n Lhat b
xhat : Fin n → ℝ := fl_backSub fp n Uhat yhat
ΔA : Fin n → Fin n → ℝ := fun i j => ∑ k, Lhat i k * Uhat k j - A i j
⊢ ∀ (i : Fin n), ∑ j, (A i j + ΔA i j) * fl_backSub fp n Uhat (fl_forwardSub fp n Lhat b) j = b i
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```

### condition_c

```text
Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/QR/GivensQR.lean:70:43: unused variable `hc`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2013/2030] Replayed LeanFpAnalysis.FP.Algorithms.QR.QRSolve
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
⚠ [2015/2030] Replayed LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean:122:5: unused variable `hε_G`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSQRSolve.lean:122:22: unused variable `hε_g`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2016/2030] Replayed LeanFpAnalysis.FP.Algorithms.LeastSquares.LSNormalEquations
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSNormalEquations.lean:101:5: unused variable `hm`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: LeanFpAnalysis/FP/Algorithms/LeastSquares/LSNormalEquations.lean:205:5: unused variable `hKappa`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [2019/2030] Replayed LeanFpAnalysis.FP.Algorithms.FastMatMul
warning: LeanFpAnalysis/FP/Algorithms/FastMatMul.lean:149:5: unused variable `hn`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T07_LUSolveGrowth-20260505-230936/condition_c/T07_LUSolveGrowth
```
