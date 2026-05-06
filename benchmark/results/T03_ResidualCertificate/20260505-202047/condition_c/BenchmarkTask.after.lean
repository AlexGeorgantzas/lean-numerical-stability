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
  intro i
  have hτi : 0 ≤ τ i := hτ_nonneg i
  have hconv := conventional_residual_error fp n A x b hn hn1 i
  have htri :
      |b i - ∑ j : Fin n, A i j * x j| ≤
        |fl_residual fp n A x b i - (b i - ∑ j : Fin n, A i j * x j)| +
          |fl_residual fp n A x b i| := by
    calc
      |b i - ∑ j : Fin n, A i j * x j|
          = |(b i - ∑ j : Fin n, A i j * x j) -
              fl_residual fp n A x b i + fl_residual fp n A x b i| := by
            ring_nf
      _ ≤ |(b i - ∑ j : Fin n, A i j * x j) -
              fl_residual fp n A x b i| +
            |fl_residual fp n A x b i| := abs_add_le _ _
      _ = |fl_residual fp n A x b i -
              (b i - ∑ j : Fin n, A i j * x j)| +
            |fl_residual fp n A x b i| := by
            rw [abs_sub_comm]
  linarith [htri, hconv, hsmall i, hτi]

end LeanFpAnalysis.FP
