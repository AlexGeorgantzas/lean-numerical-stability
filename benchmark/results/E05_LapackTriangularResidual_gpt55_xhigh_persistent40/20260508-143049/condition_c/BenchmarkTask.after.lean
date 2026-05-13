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
  let xhat := fl_backSub fp n U b
  change infNormVec hnpos (triangularResidual n U xhat b) ≤
      gamma fp n * infNorm hnpos U * infNormVec hnpos xhat
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n U b hdiag hupper hn
  have hγ_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hpoint : ∀ i : Fin n,
      |triangularResidual n U xhat b i| ≤
        gamma fp n * infNorm hnpos U * infNormVec hnpos xhat := by
    intro i
    have hx_le : ∀ j : Fin n, |xhat j| ≤ infNormVec hnpos xhat := by
      intro j
      unfold infNormVec
      exact Finset.le_sup' (fun j : Fin n => |xhat j|) (Finset.mem_univ j)
    have hres_eq :
        ∑ j : Fin n, U i j * xhat j - b i =
          -(∑ j : Fin n, ΔU i j * xhat j) := by
      have hsplit :
          ∑ j : Fin n, (U i j + ΔU i j) * xhat j =
            ∑ j : Fin n, U i j * xhat j + ∑ j : Fin n, ΔU i j * xhat j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hsum_eq :
          ∑ j : Fin n, U i j * xhat j + ∑ j : Fin n, ΔU i j * xhat j = b i := by
        rw [← hsplit]
        exact hΔU_eq i
      linarith
    calc |triangularResidual n U xhat b i|
        = |∑ j : Fin n, U i j * xhat j - b i| := by
            simp only [triangularResidual]
      _ = |-(∑ j : Fin n, ΔU i j * xhat j)| := by rw [hres_eq]
      _ = |∑ j : Fin n, ΔU i j * xhat j| := by rw [abs_neg]
      _ ≤ ∑ j : Fin n, |ΔU i j * xhat j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |ΔU i j| * |xhat j| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
      _ ≤ ∑ j : Fin n, (gamma fp n * |U i j|) * |xhat j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (hΔU_bound i j) (abs_nonneg _)
      _ = gamma fp n * ∑ j : Fin n, |U i j| * |xhat j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ ≤ gamma fp n * ∑ j : Fin n, |U i j| * infNormVec hnpos xhat := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left (hx_le j) (abs_nonneg _)
            · exact hγ_nonneg
      _ = gamma fp n * (∑ j : Fin n, |U i j|) * infNormVec hnpos xhat := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ gamma fp n * infNorm hnpos U * infNormVec hnpos xhat := by
            have hrow_scaled :
                gamma fp n * (∑ j : Fin n, |U i j|) ≤
                  gamma fp n * infNorm hnpos U :=
              mul_le_mul_of_nonneg_left (row_sum_le_infNorm hnpos U i) hγ_nonneg
            exact mul_le_mul_of_nonneg_right hrow_scaled
              (infNormVec_nonneg hnpos xhat)
  change Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hnpos⟩⟩)
      (fun i : Fin n => |triangularResidual n U xhat b i|) ≤
    gamma fp n * infNorm hnpos U * infNormVec hnpos xhat
  apply Finset.sup'_le
  intro i _
  exact hpoint i

end LeanFpAnalysis.FP
