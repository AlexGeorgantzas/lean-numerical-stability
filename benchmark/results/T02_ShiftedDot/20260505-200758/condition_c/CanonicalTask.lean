import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def fl_shiftedDot (fp : FPModel) (n : ℕ)
    (c : ℝ) (x y : Fin n → ℝ) : ℝ :=
  fp.fl_add c (fl_dotProduct fp n x y)

theorem shiftedDot_forward_error (fp : FPModel) (n : ℕ)
    (c : ℝ) (x y : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1)) :
    |fl_shiftedDot fp n c x y - (c + ∑ i : Fin n, x i * y i)| ≤
      gamma fp (n + 1) *
        (|c| + ∑ i : Fin n, |x i| * |y i|) := by
  sorry

end LeanFpAnalysis.FP
