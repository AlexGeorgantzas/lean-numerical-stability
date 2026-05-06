import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem stationary_forwardSub_residual_bound (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A M N Minv : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (xhat : ℕ → Fin n → ℝ)
    (q μ : ℝ) (m : ℕ)
    (hS : SplittingSpec n A M N Minv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hMdiag : ∀ i, M i i ≠ 0)
    (hMLT : ∀ i j : Fin n, i.val < j.val → M i j = 0)
    (hgamma : gammaValid fp n)
    (hstep : ∀ k,
      xhat (k + 1) =
        fl_forwardSub fp n M
          (fun i => ∑ j : Fin n, N i j * xhat k j + b i))
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1)
    (hH : infNorm hnpos (dualIterMatrix n N Minv) ≤ q)
    (hμ_nonneg : 0 ≤ μ)
    (hlocal : ∀ k,
      infNormVec hnpos
        (fun i => gamma fp n * ∑ j : Fin n, |M i j| * |xhat (k + 1) j|)
        ≤ μ) :
    infNormVec hnpos (fun i => b i - ∑ j : Fin n, A i j * xhat (m + 1) j) ≤
      q ^ (m + 1) *
        infNormVec hnpos (fun i => b i - ∑ j : Fin n, A i j * xhat 0 j) +
      μ * infNorm hnpos (matSub_id n (dualIterMatrix n N Minv)) / (1 - q) := by
  sorry

end LeanFpAnalysis.FP
