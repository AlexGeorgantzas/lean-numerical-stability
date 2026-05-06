import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem one_step_refinement_conventional_residual (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (b x0 dhat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hμ_nonneg : 0 ≤ μ)
    (hΔ : ∀ i j, |ΔA i j| ≤ μ * |A i j|)
    (hsolve : ∀ i,
      ∑ j : Fin n, (A i j + ΔA i j) * dhat j =
        fl_residual fp n A x0 b i) :
    let x1 := fun i => x0 i + dhat i
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x1 j| ≤
        μ * ∑ j : Fin n, |A i j| * |dhat j| +
        gamma fp (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x0 j|) := by
  sorry

end LeanFpAnalysis.FP
