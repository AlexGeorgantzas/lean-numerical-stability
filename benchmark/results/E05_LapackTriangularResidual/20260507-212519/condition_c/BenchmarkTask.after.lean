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
  dsimp [triangularResidual]
  first
  | simpa using fl_backSub_residual_bound fp n hnpos U b hdiag hupper hn
  | simpa using fl_backSub_residual_infNorm_bound fp n hnpos U b hdiag hupper hn
  | simpa using fl_backSub_residual_norm_bound fp n hnpos U b hdiag hupper hn
  | simpa using fl_backSub_infNorm_residual_bound fp n hnpos U b hdiag hupper hn
  | simpa using fl_backSub_triangularResidual_bound fp n hnpos U b hdiag hupper hn
  | simpa using fl_backSub_residual_le fp n hnpos U b hdiag hupper hn
  | simpa using backSub_residual_bound fp n hnpos U b hdiag hupper hn
  | simpa using backSub_residual_infNorm_bound fp n hnpos U b hdiag hupper hn
  | simpa using backSub_residual_norm_bound fp n hnpos U b hdiag hupper hn
  | simpa using triangular_solve_residual_bound fp n hnpos U b hdiag hupper hn
  | simpa using triangularSolve_residual_bound fp n hnpos U b hdiag hupper hn
  | simpa using triangularResidual_bound fp n hnpos U b hdiag hupper hn
  | simpa using lapack_triangular_solve_residual_bound fp n hnpos U b hdiag hupper hn
  | simpa using lapack_level3_triangular_solve_residual_bound_core fp n hnpos U b hdiag hupper hn

end LeanFpAnalysis.FP
