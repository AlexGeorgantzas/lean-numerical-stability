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
  dsimp only
  rcases backSub_backward_error fp n U b hdiag hupper hn with ⟨ΔU, hΔU, hsolve⟩
  have hres_eq :
      triangularResidual n U (fl_backSub fp n U b) b =
        fun i => -matMulVec n ΔU (fl_backSub fp n U b) i := by
    funext i
    simp [triangularResidual, matMulVec]
    have hs := hsolve i
    rw [← hs]
    have hsum :
        (∑ j, (U i j + ΔU i j) * fl_backSub fp n U b j) =
          (∑ j, U i j * fl_backSub fp n U b j) +
            ∑ j, ΔU i j * fl_backSub fp n U b j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring
  have hneg_norm :
      infNormVec hnpos (fun i => -matMulVec n ΔU (fl_backSub fp n U b) i) =
        infNormVec hnpos (matMulVec n ΔU (fl_backSub fp n U b)) := by
    simp [infNormVec]
  rw [hres_eq, hneg_norm]
  calc
    infNormVec hnpos (matMulVec n ΔU (fl_backSub fp n U b)) ≤
        infNorm hnpos ΔU * infNormVec hnpos (fl_backSub fp n U b) :=
      infNormVec_matMulVec_le hnpos ΔU (fl_backSub fp n U b)
    _ ≤ (gamma fp n * infNorm hnpos U) * infNormVec hnpos (fl_backSub fp n U b) := by
      gcongr
      · exact infNormVec_nonneg hnpos (fl_backSub fp n U b)
      dsimp [infNorm]
      apply Finset.sup'_le
      intro i hi
      calc
        ∑ j, |ΔU i j| ≤ ∑ j, gamma fp n * |U i j| := by
          apply Finset.sum_le_sum
          intro j hj
          exact hΔU i j
        _ = gamma fp n * ∑ j, |U i j| := by
          rw [Finset.mul_sum]
        _ ≤ gamma fp n *
            Finset.univ.sup'
              (Finset.univ_nonempty_iff.mpr (Nonempty.intro ⟨0, hnpos⟩))
              (fun i => ∑ j, |U i j|) := by
          gcongr
          · exact gamma_nonneg fp hn
          · exact Finset.le_sup' (fun i => ∑ j, |U i j|) (Finset.mem_univ i)
    _ = gamma fp n * infNorm hnpos U * infNormVec hnpos (fl_backSub fp n U b) := by
      ring

end LeanFpAnalysis.FP
