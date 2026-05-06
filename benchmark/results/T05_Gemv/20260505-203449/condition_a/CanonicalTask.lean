import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def fl_gemv (fp : FPModel) (m n : ℕ)
    (alpha beta : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Fin m → ℝ :=
  fun i =>
    fp.fl_add
      (fp.fl_mul alpha (fl_matVec fp m n A x i))
      (fp.fl_mul beta (y i))

theorem gemv_backward_error (fp : FPModel) (m n : ℕ)
    (alpha beta : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hn2 : gammaValid fp (n + 2)) :
    ∃ ΔA : Fin m → Fin n → ℝ,
    ∃ Δy : Fin m → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (n + 2) * |A i j|) ∧
      (∀ i, |Δy i| ≤ gamma fp (n + 2) * |y i|) ∧
      ∀ i,
        fl_gemv fp m n alpha beta A x y i =
          alpha * ∑ j : Fin n, (A i j + ΔA i j) * x j +
          beta * (y i + Δy i) := by
  sorry

end LeanFpAnalysis.FP
