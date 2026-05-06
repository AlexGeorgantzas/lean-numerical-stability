import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem lu_solve_growth_backward_error (fp : FPModel) (n : ℕ)
    (A Lhat Uhat : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (ρ : ℝ)
    (hLdiag : ∀ i, Lhat i i ≠ 0)
    (hUdiag : ∀ i, Uhat i i ≠ 0)
    (hLU : LUBackwardError n A Lhat Uhat (gamma fp n))
    (hn : gammaValid fp n)
    (hρ_nonneg : 0 ≤ ρ)
    (hgrowth : ∀ i j,
      ∑ k : Fin n, |Lhat i k| * |Uhat k j| ≤ ρ * |A i j|) :
    let yhat := fl_forwardSub fp n Lhat b
    let xhat := fl_backSub fp n Uhat yhat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔA i j| ≤
          ((3 * gamma fp n + gamma fp n ^ 2) * ρ) * |A i j|) ∧
      ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * xhat j = b i := by
  sorry

end LeanFpAnalysis.FP
