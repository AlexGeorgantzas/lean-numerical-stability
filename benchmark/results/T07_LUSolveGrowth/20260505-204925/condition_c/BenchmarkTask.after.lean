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
  intro yhat xhat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error fp n A Lhat Uhat b hLdiag hUdiag hLU hn
  refine ⟨ΔA, ?_, hΔA_eq⟩
  intro i j
  calc
    |ΔA i j| ≤
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |Lhat i k| * |Uhat k j| := hΔA_bound i j
    _ ≤ (3 * gamma fp n + gamma fp n ^ 2) * (ρ * |A i j|) := by
      have hρA_nonneg : 0 ≤ ρ * |A i j| :=
        mul_nonneg hρ_nonneg (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left (hgrowth i j) (by
        have hγ := gamma_nonneg fp hn
        nlinarith [sq_nonneg (gamma fp n), hρA_nonneg])
    _ = ((3 * gamma fp n + gamma fp n ^ 2) * ρ) * |A i j| := by
      ring

end LeanFpAnalysis.FP
