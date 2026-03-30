-- Benchmark/T09_BlockTriangularSolve.lean
-- Tier 3 (Novel reasoning) — 2×2 block back-substitution

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.MatVec
import LeanFpAnalysis.FP.Algorithms.TriangularSolve

/-!
# Task 9: Blocked triangular solve (2×2 block back-substitution)

**Tier:** 3 (Novel reasoning)
**Higham ref:** §12.1, blocked triangular systems
**Difficulty:** Hard — requires composing matVec, matMul errors with triangular solve

## Task description

Consider a 2×2 block upper triangular system:
  ⎡ U₁₁  U₁₂ ⎤ ⎡ x₁ ⎤   ⎡ b₁ ⎤
  ⎣  0   U₂₂ ⎦ ⎣ x₂ ⎦ = ⎣ b₂ ⎦

The block back-substitution computes:
  1. x̂₂ = fl(U₂₂⁻¹ b₂)              — back substitution
  2. ĉ₁ = fl(b₁ - U₁₂ x̂₂)           — matvec + subtraction
  3. x̂₁ = fl(U₁₁⁻¹ ĉ₁)              — back substitution

Show that the composed solution satisfies a backward error bound
for the full block system.

## Expected approach

1. Apply `backSub_backward_error` for step 1: (U₂₂ + ΔU₂₂)x̂₂ = b₂.
2. Apply `matVec_error_bound` + rounding for step 2 to bound |ĉ₁ - (b₁ - U₁₂x̂₂)|.
3. Apply `backSub_backward_error` for step 3: (U₁₁ + ΔU₁₁)x̂₁ = ĉ₁.
4. Assemble the full block perturbation matrix.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 4 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- **2×2 block back-substitution.**

    Solves the block upper triangular system by:
      x̂₂ = backSub(U₂₂, b₂)
      x̂₁ = backSub(U₁₁, b₁ - fl(U₁₂ · x̂₂)) -/
noncomputable def fl_blockBackSub2 (fp : FPModel) (n₁ n₂ : ℕ)
    (U₁₁ : Fin n₁ → Fin n₁ → ℝ) (U₁₂ : Fin n₁ → Fin n₂ → ℝ)
    (U₂₂ : Fin n₂ → Fin n₂ → ℝ)
    (b₁ : Fin n₁ → ℝ) (b₂ : Fin n₂ → ℝ) :
    (Fin n₁ → ℝ) × (Fin n₂ → ℝ) :=
  let x_hat₂ := fl_backSub fp n₂ U₂₂ b₂
  let c₁ := fun i => fp.fl_sub (b₁ i) (fl_matVec fp n₁ n₂ U₁₂ x_hat₂ i)
  let x_hat₁ := fl_backSub fp n₁ U₁₁ c₁
  (x_hat₁, x_hat₂)

/-- **Block back-substitution backward error for the (2,2) block.**

    The computed x̂₂ = fl(U₂₂⁻¹b₂) satisfies:
      (U₂₂ + ΔU₂₂)x̂₂ = b₂
    with |ΔU₂₂| ≤ γ(n₂)|U₂₂| componentwise. -/
theorem blockBackSub2_block22_error (fp : FPModel) (n₁ n₂ : ℕ)
    (U₁₁ : Fin n₁ → Fin n₁ → ℝ) (U₁₂ : Fin n₁ → Fin n₂ → ℝ)
    (U₂₂ : Fin n₂ → Fin n₂ → ℝ)
    (b₁ : Fin n₁ → ℝ) (b₂ : Fin n₂ → ℝ)
    (hU₂₂_diag : ∀ i, U₂₂ i i ≠ 0)
    (hU₂₂_upper : ∀ i j : Fin n₂, j.val < i.val → U₂₂ i j = 0)
    (hn₂ : gammaValid fp n₂) :
    let (_, x_hat₂) := fl_blockBackSub2 fp n₁ n₂ U₁₁ U₁₂ U₂₂ b₁ b₂
    ∃ ΔU₂₂ : Fin n₂ → Fin n₂ → ℝ,
      (∀ i j, |ΔU₂₂ i j| ≤ gamma fp n₂ * |U₂₂ i j|) ∧
      ∀ i, ∑ j : Fin n₂, (U₂₂ i j + ΔU₂₂ i j) * x_hat₂ j = b₂ i := by
  sorry

end LeanFpAnalysis.FP.Benchmark
