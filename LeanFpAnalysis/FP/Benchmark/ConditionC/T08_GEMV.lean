-- Benchmark/T08_GEMV.lean
-- Tier 3 (Novel reasoning) — Full BLAS Level 2 GEMV: y = αAx + βy₀

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Algorithms.MatVec

/-!
# Task 8: Full BLAS GEMV backward/forward error

**Tier:** 3 (Novel reasoning)
**Higham ref:** §3.5, full BLAS Level 2 generalization
**Difficulty:** Hard — requires composing matVec error, two scalar roundings, and addition

## Task description

The BLAS Level 2 routine xGEMV computes:
  y = α·A·x + β·y₀

The floating-point computation is:
  1. ŝᵢ = fl_matVec(A, x)ᵢ          — inner products, error γ(n)
  2. t̂ᵢ = fl(α · ŝᵢ)               — scalar multiply, +1 rounding
  3. ûᵢ = fl(β · y₀ᵢ)               — scalar multiply, +1 rounding
  4. ŷᵢ = fl(t̂ᵢ + ûᵢ)              — addition, +1 rounding

Show the componentwise forward error bound:
  |ŷᵢ - (α·∑ⱼ Aᵢⱼxⱼ + β·y₀ᵢ)| ≤
    γ(n+2)·|α|·∑ⱼ |Aᵢⱼ|·|xⱼ| + γ(2)·|β|·|y₀ᵢ|

## Expected approach

1. Apply `matVec_error_bound` for ŝ.
2. Track rounding through fl_mul(α, ŝᵢ) and fl_mul(β, y₀ᵢ).
3. Track rounding through fl_add(t̂ᵢ, ûᵢ).
4. Use `gamma_mul` to combine rounding factors.
5. Final bound via triangle inequality.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 3 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- Floating-point GEMV: ŷᵢ = fl(fl(α · fl(Ax)ᵢ) + fl(β · y₀ᵢ)). -/
noncomputable def fl_gemv (fp : FPModel) (n : ℕ)
    (α β : ℝ) (A : Fin n → Fin n → ℝ) (x y₀ : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    fp.fl_add
      (fp.fl_mul α (fl_matVec fp n n A x i))
      (fp.fl_mul β (y₀ i))

/-- **GEMV forward error bound.**

    The computed y = fl(αAx + βy₀) satisfies:
      |ŷᵢ - (α·∑ⱼ Aᵢⱼxⱼ + β·y₀ᵢ)| ≤
        γ(n+2)·|α|·∑ⱼ |Aᵢⱼ|·|xⱼ| + γ(2)·|β|·|y₀ᵢ| -/
theorem gemv_error_bound (fp : FPModel) (n : ℕ)
    (α β : ℝ) (A : Fin n → Fin n → ℝ) (x y₀ : Fin n → ℝ)
    (hn : gammaValid fp (n + 2)) :
    ∀ i : Fin n,
      |fl_gemv fp n α β A x y₀ i -
        (α * ∑ j : Fin n, A i j * x j + β * y₀ i)| ≤
        gamma fp (n + 2) * |α| * ∑ j : Fin n, |A i j| * |x j| +
        gamma fp 2 * |β| * |y₀ i| := by
  sorry

end LeanFpAnalysis.FP.Benchmark
