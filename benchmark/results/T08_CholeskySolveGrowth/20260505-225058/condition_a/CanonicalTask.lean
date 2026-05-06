import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem cholesky_solve_growth_backward_error (fp : FPModel) (n : ℕ)
    (A Rhat : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (ρ : ℝ)
    (hRdiag : ∀ i, Rhat i i ≠ 0)
    (hChol : CholeskyBackwardError n A Rhat (gamma fp (n + 1)))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n + 1))
    (hρ_nonneg : 0 ≤ ρ)
    (hgrowth : ∀ i j,
      ∑ k : Fin n, |Rhat k i| * |Rhat k j| ≤ ρ * |A i j|) :
    let RhatT := fun i j : Fin n => Rhat j i
    let yhat := fl_forwardSub fp n RhatT b
    let xhat := fl_backSub fp n Rhat yhat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔA i j| ≤ gamma fp (3 * n + 1) * ρ * |A i j|) ∧
      ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * xhat j = b i := by
  sorry

end LeanFpAnalysis.FP
