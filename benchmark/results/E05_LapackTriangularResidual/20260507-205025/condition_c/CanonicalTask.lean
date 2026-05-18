import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def triangularResidual (n : ℕ)
    (U : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, U i j * x j - b i

theorem lapack_level3_triangular_solve_residual
    (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    let xhat := fl_backSub fp n U b
    infNormVec hnpos (triangularResidual n U xhat b) ≤
      gamma fp n * infNorm hnpos U * infNormVec hnpos xhat := by
  sorry

end LeanFpAnalysis.FP
