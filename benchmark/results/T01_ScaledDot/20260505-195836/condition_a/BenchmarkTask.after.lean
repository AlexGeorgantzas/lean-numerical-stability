import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def fl_scaledDot (fp : FPModel) (n : ℕ)
    (alpha : ℝ) (x y : Fin n → ℝ) : ℝ :=
  fp.fl_mul alpha (fl_dotProduct fp n x y)

theorem scaledDot_backward_error (fp : FPModel) (n : ℕ)
    (alpha : ℝ) (x y : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1)) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (n + 1)) ∧
      fl_scaledDot fp n alpha x y =
        alpha * ∑ i : Fin n, x i * y i * (1 + η i) := by
  sorry

end LeanFpAnalysis.FP
