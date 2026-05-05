# Run Analysis

- task: `T01_ScaledDot`
- run_timestamp: `20260501-140133`
- result_root: `benchmark/results/T01_ScaledDot/20260501-140133`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `no`
- Condition C validation exit: `0`
- Condition C timeout: `no`

Interpretation: Condition A failed while Condition C passed under the same run protocol.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-01T11:02:19Z	2026-05-01T11:09:52Z	95	12	5	0	0
condition_c	0	0	no	2026-05-01T11:09:52Z	2026-05-01T11:13:32Z	72	40	33	0	0
```

## Failure Notes


### condition_a

```text
alpha : ℝ
x y : Fin n → ℝ
hn1 : gammaValid fp (n + 1)
h : ∀ (a : Fin n → ℝ), fl_scaledDot fp n alpha x y = alpha * ∑ i, x i * y i * (1 + a i) → ∃ i, ¬|a i| ≤ gamma fp (n + 1)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] gammaValid fp (n + 1)
    [prop] ∀ (a : Fin n → ℝ),
          fl_scaledDot fp n alpha x y = alpha * ∑ i, x i * y i * (1 + a i) → ∃ i, ¬|a i| ≤ gamma fp (n + 1)
    [prop] gammaValid fp (n + 1) = ((↑n + 1) * fp.u < 1)
  [eqc] True propositions
    [prop] gammaValid fp (n + 1)
    [prop] ∀ (a : Fin n → ℝ),
          fl_scaledDot fp n alpha x y = alpha * ∑ i, x i * y i * (1 + a i) → ∃ i, ¬|a i| ≤ gamma fp (n + 1)
    [prop] gammaValid fp (n + 1) = ((↑n + 1) * fp.u < 1)
    [prop] (↑n + 1) * fp.u < 1
  [ematch] E-matching patterns
    [thm] fl_scaledDot.eq_1: [fl_scaledDot #4 #3 #2 #1 #0]
    [thm] fl_dotProduct.eq_1: [fl_dotProduct #2 `[0] #1 #0]
    [thm] fl_dotProduct.eq_2: [fl_dotProduct #3 (#2 + 1) #1 #0]
    [thm] gamma.eq_1: [gamma #1 #0]
    [thm] gammaValid.eq_1: [gammaValid #1 #0]
  [cutsat] Assignment satisfying linear constraints
    [assign] n := 0
  [linarith] Linarith assignment for `ℝ`
    [assign] alpha := 2
    [assign] fp.u := 0
[grind] Issues
  [issue] failed to create E-match local theorem for
        ∀ (a : Fin n → ℝ),
          fl_scaledDot fp n alpha x y = alpha * ∑ i, x i * y i * (1 + a i) → ∃ i, ¬|a i| ≤ gamma fp (n + 1)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] gammaValid.eq_1 ↦ 1
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
✔ [2029/2030] Built BenchmarkTask (8.4s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T01_ScaledDot-20260501-140133/condition_c/T01_ScaledDot
```
