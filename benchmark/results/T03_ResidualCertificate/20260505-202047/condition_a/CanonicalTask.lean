import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem residual_stopping_certificate (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b τ : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hτ_nonneg : ∀ i, 0 ≤ τ i)
    (hsmall : ∀ i, |fl_residual fp n A x b i| ≤ τ i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x j| ≤
        τ i + gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  sorry

end LeanFpAnalysis.FP
