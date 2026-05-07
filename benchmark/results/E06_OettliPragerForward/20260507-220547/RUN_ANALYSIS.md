# Run Analysis

- task: `E06_OettliPragerForward`
- run_timestamp: `20260507-220547`
- result_root: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E06_OettliPragerForward/20260507-220547`

## Outcome

- Condition A validation exit: `1`
- Condition A timeout: `no`
- Condition A classification: failed: final Lean file did not build
- Condition C validation exit: `1`
- Condition C timeout: `no`
- Condition C classification: failed: final Lean file did not build

Interpretation: both conditions failed; inspect failure modes before drawing conclusions.

## Metrics

```tsv
condition	codex_exit	validation_exit	timeout	started_at_utc	finished_at_utc	codex_event_lines	diff_lines	proof_lines	placeholder_count	forbidden_decl_count
condition_a	0	1	no	2026-05-07T19:07:04Z	2026-05-07T19:10:47Z	59	130	124	0	0
condition_c	0	1	no	2026-05-07T19:10:47Z	2026-05-07T19:13:53Z	74	114	108	0	0
```

## Public Solver Messages

- Condition A: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E06_OettliPragerForward/20260507-220547/condition_a/agent_messages.md`
- Condition C: `/Users/georgiosalexandrosgeorgantzas/Documents/GitHub/lean-fp-analysis/benchmark/results/E06_OettliPragerForward/20260507-220547/condition_c/agent_messages.md`

These files summarize public solver progress messages extracted from
`codex_events.jsonl`. They are not hidden chain-of-thought.

## Failure Notes


### condition_a

```text
hback_eq : ∀ (i : Fin n), ∑ j, (A i j + DeltaA i j) * xhat j = b i + Deltab i
hres : ∀ (j : Fin n), ∑ k, A j k * (x k - xhat k) = ∑ k, DeltaA j k * xhat k - Deltab j
hrepr : x i - xhat i = ∑ j, A_inv i j * (∑ k, DeltaA j k * xhat k - Deltab j)
j : Fin n
hj : j ∈ Finset.univ
⊢ ∑ k, |DeltaA j k * xhat k| + ∑ k, |Deltab j| = ∑ k, |DeltaA j k * xhat k| + |Deltab j|
error: BenchmarkTask.lean:139:26: No applicable extensionality theorem found for type
  ℝ

Note: Extensionality theorems can be registered by marking them with the `[ext]` attribute
info: BenchmarkTask.lean:143:26: Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
error: BenchmarkTask.lean:142:72: unsolved goals
n : ℕ
A A_inv : Fin n → Fin n → ℝ
x xhat b : Fin n → ℝ
eta : ℝ
hInv : IsLeftInverse n A A_inv
hAx : ∀ (i : Fin n), ∑ j, A i j * x j = b i
heta_nonneg : 0 ≤ eta
i : Fin n
DeltaA : Fin n → Fin n → ℝ
Deltab : Fin n → ℝ
hDeltaA : ∀ (i j : Fin n), |DeltaA i j| ≤ eta * |A i j|
hDeltab : ∀ (i : Fin n), |Deltab i| ≤ eta * |b i|
hback_eq : ∀ (i : Fin n), ∑ j, (A i j + DeltaA i j) * xhat j = b i + Deltab i
hres : ∀ (j : Fin n), ∑ k, A j k * (x k - xhat k) = ∑ k, DeltaA j k * xhat k - Deltab j
hrepr : x i - xhat i = ∑ j, A_inv i j * (∑ k, DeltaA j k * xhat k - Deltab j)
j : Fin n
⊢ |A_inv i j| * eta * ∑ x, |A j x| * |xhat x| + |A_inv i j| * |b j| =
    |A_inv i j| * eta * ∑ x, |A j x| * |xhat x| + |A_inv i j| * eta * |b j|
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```

### condition_c

```text
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
✖ [2029/2030] Building BenchmarkTask (2.5s)
trace: .> LEAN_PATH=/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Cli/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/batteries/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/Qq/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/aesop/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/proofwidgets/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/importGraph/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/LeanSearchClient/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/plausible/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/lake-packages/leanprover-lean4-v4.29.0-rc3-54d24c7bebd8e87d/mathlib/.lake/build/lib/lean:/Users/georgiosalexandrosgeorgantzas/.cache/lean-fp-analysis/condition-c-snapshots/leanprover-lean4-v4.29.0-rc3-d19a800d98f8fe6f/.lake/build/lib/lean:/private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-220547/condition_c/E06_OettliPragerForward/.lake/build/lib/lean /Users/georgiosalexandrosgeorgantzas/.elan/toolchains/leanprover--lean4---v4.29.0-rc3/bin/lean /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-220547/condition_c/E06_OettliPragerForward/BenchmarkTask.lean -o /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-220547/condition_c/E06_OettliPragerForward/.lake/build/lib/lean/BenchmarkTask.olean -i /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-220547/condition_c/E06_OettliPragerForward/.lake/build/lib/lean/BenchmarkTask.ilean -c /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-220547/condition_c/E06_OettliPragerForward/.lake/build/ir/BenchmarkTask.c --setup /private/tmp/lean-fp-benchmark-runs/E06_OettliPragerForward-20260507-220547/condition_c/E06_OettliPragerForward/.lake/build/ir/BenchmarkTask.setup.json --json
error: BenchmarkTask.lean:83:62: Unknown identifier `abs_add`
error: BenchmarkTask.lean:82:14: No goals to be solved
error: BenchmarkTask.lean:87:14: Type mismatch
  add_le_add_right (Finset.abs_sum_le_sum_abs ?m.874 ?m.875) ?m.876
has type
  ?m.876 + |∑ i ∈ ?m.875, ?m.874 i| ≤ ?m.876 + ∑ i ∈ ?m.875, |?m.874 i|
but is expected to have type
  |∑ k, DeltaA j k * xhat k| + |Deltab j| ≤ ∑ k, |DeltaA j k * xhat k| + |Deltab j|
error: Lean exited with code 1
Some required targets logged failures:
- BenchmarkTask
error: build failed
validation failed: lake build BenchmarkTask failed
```
