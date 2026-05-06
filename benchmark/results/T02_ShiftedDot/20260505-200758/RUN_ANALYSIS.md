# Run Analysis

- task: `T02_ShiftedDot`
- run_timestamp: `20260505-200758`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/T02_ShiftedDot/20260505-200758`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `no`
- Condition C validation exit: `0`
- Condition C timeout: `no`

Interpretation: Condition A failed while Condition C passed under the same run protocol.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-05T17:08:22Z	2026-05-05T17:16:23Z	104	10	4	0	0
condition_c	0	0	no	2026-05-05T17:16:23Z	2026-05-05T17:20:47Z	88	62	56	0	0
```

## Failure Notes


### condition_a

```text
    [assign] gamma fp (n + 1) := 0
    [assign] |c| := 0
    [assign] |fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i)| := 23
    [assign] ∑ i, x i * y i := 0
    [assign] ∑ i, |x i| * |y i| := 0
    [assign] fl_shiftedDot fp n c x y := 14
    [assign] fp.u := 0
    [assign] fp.fl_add c (fl_dotProduct fp n x y) := 14
    [assign] fl_dotProduct fp n x y := 15
    [assign] max c (-c) := 0
    [assign] max (fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i))
          (-(fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i))) := 23
  [ring] Ring `ℝ`
    [basis] Basis
      [_] ↑n * fp.u * (1 - (↑n + 1) * fp.u)⁻¹ + fp.u * (1 - (↑n + 1) * fp.u)⁻¹ + -1 * gamma fp (n + 1) = 0
      [_] fl_shiftedDot fp n c x y + |c| + -1 * ∑ i, |x i| * |y i| + |fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i)| =
            0
      [_] c + |c| = 0
      [_] ∑ i, x i * y i + -1 * ∑ i, |x i| * |y i| = 0
      [_] gamma fp (n + 1) + -1 * (1 - (↑n + 1) * fp.u)⁻¹ + 1 = 0
  [assoc] Operator `max`
    [basis] Basis
      [_] max (fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i)) (-(fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i))) =
            -(fl_shiftedDot fp n c x y - (c + ∑ i, x i * y i))
      [_] max c (-c) = -c
    [properties] Properties
      [_] commutative
      [_] idempotent
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] max_def ↦ 2
    [thm] abs.eq_1 ↦ 2
    [thm] fl_shiftedDot.eq_1 ↦ 1
    [thm] gamma.eq_1 ↦ 1
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
✔ [2029/2030] Built BenchmarkTask (2.7s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/T02_ShiftedDot-20260505-200758/condition_c/T02_ShiftedDot
```
