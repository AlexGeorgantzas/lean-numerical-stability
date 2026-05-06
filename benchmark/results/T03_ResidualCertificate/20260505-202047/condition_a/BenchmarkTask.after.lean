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
  classical
  intro i
  have herr :
      |(b i - ∑ j : Fin n, A i j * x j) - fl_residual fp n A x b i| ≤
        gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
    unfold fl_residual fl_matVec
    aesop
  calc
    |b i - ∑ j : Fin n, A i j * x j|
        = |((b i - ∑ j : Fin n, A i j * x j) - fl_residual fp n A x b i) +
            fl_residual fp n A x b i| := by rw [sub_add_cancel]
    _ ≤ |(b i - ∑ j : Fin n, A i j * x j) - fl_residual fp n A x b i| +
          |fl_residual fp n A x b i| := abs_add _ _
    _ ≤ gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) + τ i := by
        exact add_le_add herr (hsmall i)
    _ = τ i + gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by rw [add_comm]

end LeanFpAnalysis.FP
