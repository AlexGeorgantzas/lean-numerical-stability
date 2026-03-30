-- Benchmark/T07_ScaledMatVec.lean
-- Tier 3 (Novel reasoning) — Scaled matrix-vector product y = αAx

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.MatVec

/-!
# Task 7: Scaled matrix-vector product y = αAx

**Tier:** 3 (Novel reasoning)
**Higham ref:** §3.5, extending to BLAS-style scaled operation
**Difficulty:** Hard — requires `gamma_mul` composition with scalar rounding

## Task description

The BLAS Level 2 routine xGEMV computes y = αAx + βy₀. As a first step,
analyze the simpler case y = αAx where α is a scalar.

The computation is:
  1. Compute ŝ = fl(Ax) via `fl_matVec`    — error γ(n)
  2. Compute ŷᵢ = fl(α * ŝᵢ)              — one more rounding

Show the combined error bound:
  |ŷᵢ - α·∑ⱼ Aᵢⱼxⱼ| ≤ γ(n+1) * |α| * ∑ⱼ |Aᵢⱼ| * |xⱼ|

## Expected approach

1. Apply `matVec_error_bound` to get |ŝᵢ - ∑ Aᵢⱼxⱼ| ≤ γ(n)·∑|Aᵢⱼ||xⱼ|.
2. Write ŷᵢ = fl(α·ŝᵢ) = α·ŝᵢ·(1 + δ) with |δ| ≤ u.
3. Expand: ŷᵢ = α·(∑ Aᵢⱼxⱼ + εᵢ)·(1 + δ) where |εᵢ| ≤ γ(n)·∑|Aᵢⱼ||xⱼ|.
4. Use `gamma_mul` with j=1, k=n to combine (1+δ)·(1+θ) → (1+θ'), |θ'| ≤ γ(n+1).
5. Conclude with triangle inequality.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 2 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- Floating-point scaled matrix-vector product: ŷᵢ = fl(α · fl(Ax)ᵢ). -/
noncomputable def fl_scaledMatVec (fp : FPModel) (n : ℕ)
    (α : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_mul α (fl_matVec fp n n A x i)

/-- **Scaled matrix-vector forward error bound.**

    The computed y = fl(α · fl(Ax)) satisfies:
      |ŷᵢ - α·∑ⱼ Aᵢⱼxⱼ| ≤ γ(n+1) * |α| * ∑ⱼ |Aᵢⱼ| * |xⱼ| -/
theorem scaledMatVec_error_bound (fp : FPModel) (n : ℕ)
    (α : ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |fl_scaledMatVec fp n α A x i - α * ∑ j : Fin n, A i j * x j| ≤
        gamma fp (n + 1) * |α| * ∑ j : Fin n, |A i j| * |x j| := by
  sorry

end LeanFpAnalysis.FP.Benchmark
