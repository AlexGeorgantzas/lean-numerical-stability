# Run Analysis

- task: `E08_LapackLSQRForward`
- run_timestamp: `20260507-222525`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E08_LapackLSQRForward/20260507-222525`

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
condition_a	0	1	no	2026-05-07T19:25:45Z	2026-05-07T19:28:06Z	51	104	98	0	0
condition_c	0	0	no	2026-05-07T19:28:07Z	2026-05-07T19:29:50Z	63	13	7	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E08_LapackLSQRForward/20260507-222525/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E08_LapackLSQRForward/20260507-222525/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
DeltaG : Fin n → Fin n → ℝ
Deltag : Fin n → ℝ
hPert : ∀ (i : Fin n), matMulVec n (fun a b => ATA a b + DeltaG a b) xhat i = ATb i + Deltag i
hDeltaG : frobNorm DeltaG ≤ cG
hDeltag : ∀ (i : Fin n), |Deltag i| ≤ cg
i : Fin n
hleft : IsLeftInverse n ATA ATA_inv
hrow : ∀ (j : Fin n), ∑ k, ATA j k * (xhat k - x k) = Deltag j - ∑ k, DeltaG j k * xhat k
k : Fin n
a✝ : k ∈ Finset.univ
⊢ (∑ k_1, ATA_inv i k_1 * ATA k_1 k) * (xhat k - x k) = ∑ x_1, ATA_inv i x_1 * (ATA x_1 k * (xhat k - x k))
error: BenchmarkTask.lean:94:44: Application type mismatch: The argument
  Finset.univ
has type
  Finset ?m.617
but is expected to have type
  ?m.612 → ?m.613
in the application
  Finset.abs_sum_le_sum_abs Finset.univ
error: BenchmarkTask.lean:110:22: Unknown identifier `abs_add`
error: BenchmarkTask.lean:112:69: Application type mismatch: The argument
  Finset.univ
has type
  Finset ?m.816
but is expected to have type
  ?m.811 → ?m.812
in the application
  Finset.abs_sum_le_sum_abs Finset.univ
warning: BenchmarkTask.lean:65:22: This simp argument is unused:
  hb

Hint: Omit it from the simp argument list.
  simp ̵[̵h̵b̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
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
✔ [2029/2030] Built BenchmarkTask (2.3s)
Build completed successfully (2030 jobs).
validation passed: /tmp/lean-fp-benchmark-runs/E08_LapackLSQRForward-20260507-222525/condition_c/E08_LapackLSQRForward
```
