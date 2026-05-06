import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem triangularSolve_single_backward_error (fp : FPModel) (n : ℕ)
    (L U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hLdiag : ∀ i, L i i ≠ 0)
    (hUdiag : ∀ i, U i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    let yhat := fl_forwardSub fp n L b
    let xhat := fl_backSub fp n U yhat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔA i j| ≤
          (2 * gamma fp n + gamma fp n ^ 2) *
            ∑ k : Fin n, |L i k| * |U k j|) ∧
      ∀ i, ∑ j : Fin n,
        ((∑ k : Fin n, L i k * U k j) + ΔA i j) * xhat j = b i := by
  sorry

end LeanFpAnalysis.FP
