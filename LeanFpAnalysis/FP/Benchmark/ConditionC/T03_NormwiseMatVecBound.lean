-- Benchmark/T03_NormwiseMatVecBound.lean
-- Tier 1 (Direct application) — Normwise matvec forward error

import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.MatVec

/-!
# Task 3: Normwise matrix-vector forward error bound

**Tier:** 1 (Direct application)
**Higham ref:** §3.5, corollary of equation 3.11
**Difficulty:** Easy — lift `matVec_error_bound` to infinity norm

## Task description

The componentwise bound `matVec_error_bound` gives:
  |ŷᵢ − (Ax)ᵢ| ≤ γ(n) · ∑ⱼ |Aᵢⱼ| · |xⱼ|

Lift this to a normwise bound in the infinity norm:
  ‖ŷ − Ax‖∞ ≤ γ(n) · ‖|A| · |x|‖∞

where |A| is the entrywise absolute value and |A|·|x| denotes the
matrix-vector product of |A| with |x|.

## Expected approach

1. Apply `matVec_error_bound` componentwise.
2. Take the max over i using `infNormVec` (or `Finset.sup'`).
3. Recognize that ∑ⱼ |Aᵢⱼ|·|xⱼ| is the i-th component of |A|·|x|.

## Metrics
- **Pass criterion:** No `sorry` and `lake build` succeeds
- **Partial credit:** Correct statement with ≤ 2 sorry's in helper lemmas
-/

namespace LeanFpAnalysis.FP.Benchmark

open LeanFpAnalysis.FP
open scoped BigOperators

/-- **Normwise matrix-vector forward error.**

    The computed matrix-vector product satisfies:
      ‖fl(Ax) − Ax‖∞ ≤ γ(n) · ‖|A|·|x|‖∞

    where ‖v‖∞ = max_i |v_i| and (|A|·|x|)_i = ∑_j |A_{ij}| · |x_j|. -/
theorem matVec_normwise_error_bound (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNormVec hn_pos (fun i => fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j) ≤
      gamma fp n * infNormVec hn_pos (fun i => ∑ j : Fin n, |A i j| * |x j|) := by
  sorry

end LeanFpAnalysis.FP.Benchmark
