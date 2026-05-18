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
  intro xhat
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n U b hdiag hupper hn
  have hres_eq : triangularResidual n U xhat b =
      fun i => - matMulVec n ΔU xhat i := by
    funext i
    unfold triangularResidual matMulVec
    have hpert := hΔU_eq i
    have hsplit : ∑ j : Fin n, (U i j + ΔU i j) * xhat j =
        (∑ j : Fin n, U i j * xhat j) + ∑ j : Fin n, ΔU i j * xhat j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit] at hpert
    linarith
  have hΔU_norm : infNorm hnpos ΔU ≤ gamma fp n * infNorm hnpos U := by
    unfold infNorm
    apply Finset.sup'_le
    intro i _
    calc ∑ j : Fin n, |ΔU i j|
        ≤ ∑ j : Fin n, gamma fp n * |U i j| := by
          apply Finset.sum_le_sum
          intro j _
          exact hΔU_bound i j
      _ = gamma fp n * ∑ j : Fin n, |U i j| := by
          rw [Finset.mul_sum]
      _ ≤ gamma fp n *
          Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hnpos⟩⟩)
            (fun i => ∑ j : Fin n, |U i j|) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun i => ∑ j : Fin n, |U i j|) (Finset.mem_univ i))
            (gamma_nonneg fp hn)
  calc infNormVec hnpos (triangularResidual n U xhat b)
      = infNormVec hnpos (matMulVec n ΔU xhat) := by
        rw [hres_eq]
        unfold infNormVec
        congr 1
        ext i
        exact abs_neg (matMulVec n ΔU xhat i)
    _ ≤ infNorm hnpos ΔU * infNormVec hnpos xhat :=
        infNormVec_matMulVec_le hnpos ΔU xhat
    _ ≤ (gamma fp n * infNorm hnpos U) * infNormVec hnpos xhat := by
        exact mul_le_mul_of_nonneg_right hΔU_norm (infNormVec_nonneg hnpos xhat)
    _ = gamma fp n * infNorm hnpos U * infNormVec hnpos xhat := by
        ring

end LeanFpAnalysis.FP
