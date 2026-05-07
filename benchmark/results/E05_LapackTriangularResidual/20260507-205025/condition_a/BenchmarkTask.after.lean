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
  classical
  let xhat : Fin n → ℝ := fl_backSub fp n U b
  have hn' : (n : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hn
  have hγ_nonneg : 0 ≤ gamma fp n := by
    unfold gamma
    apply div_nonneg
    · exact mul_nonneg (by exact_mod_cast Nat.cast_nonneg n) fp.u_nonneg
    · exact le_of_lt (by linarith)
  have hxnorm_nonneg : 0 ≤ infNormVec hnpos xhat := by
    exact le_trans (abs_nonneg (xhat ⟨0, hnpos⟩))
      (by
        unfold infNormVec
        exact Finset.le_sup' (fun i : Fin n => |xhat i|) (Finset.mem_univ ⟨0, hnpos⟩))
  obtain ⟨ΔU, hΔU, hrow⟩ :=
    LeanFpAnalysis.FP.backSub_backward_error fp n U b hdiag hupper hn
  have hpoint : ∀ i : Fin n,
      |triangularResidual n U xhat b i| ≤
        gamma fp n * infNorm hnpos U * infNormVec hnpos xhat := by
    intro i
    have hx_le : ∀ j : Fin n, |xhat j| ≤ infNormVec hnpos xhat := by
      intro j
      unfold infNormVec
      exact Finset.le_sup' (fun k : Fin n => |xhat k|) (Finset.mem_univ j)
    have hrow_norm : (∑ j : Fin n, |U i j|) ≤ infNorm hnpos U := by
      unfold infNorm
      exact Finset.le_sup' (fun i : Fin n => ∑ j : Fin n, |U i j|) (Finset.mem_univ i)
    have hi : (∑ j : Fin n, (U i j + ΔU i j) * xhat j) = b i := by
      simpa [xhat] using hrow i
    have hsum_expand : (∑ j : Fin n, (U i j + ΔU i j) * xhat j) =
        (∑ j : Fin n, U i j * xhat j) + ∑ j : Fin n, ΔU i j * xhat j := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    have hres_eq : triangularResidual n U xhat b i = -∑ j : Fin n, ΔU i j * xhat j := by
      dsimp [triangularResidual]
      rw [← hi, hsum_expand]
      ring
    calc
      |triangularResidual n U xhat b i| = |∑ j : Fin n, ΔU i j * xhat j| := by
        rw [hres_eq, abs_neg]
      _ ≤ ∑ j : Fin n, |ΔU i j * xhat j| := by
        simpa using Finset.abs_sum_le_sum_abs (fun j : Fin n => ΔU i j * xhat j) Finset.univ
      _ = ∑ j : Fin n, |ΔU i j| * |xhat j| := by
        simp [abs_mul]
      _ ≤ ∑ j : Fin n, (gamma fp n * |U i j|) * infNormVec hnpos xhat := by
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul (hΔU i j) (hx_le j) (abs_nonneg _)
          (mul_nonneg hγ_nonneg (abs_nonneg _))
      _ = gamma fp n * (∑ j : Fin n, |U i j|) * infNormVec hnpos xhat := by
        rw [← Finset.sum_mul]
        rw [← Finset.mul_sum]
      _ ≤ gamma fp n * infNorm hnpos U * infNormVec hnpos xhat := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrow_norm hγ_nonneg) hxnorm_nonneg
  dsimp only
  unfold infNormVec
  exact Finset.sup'_le (Finset.univ_nonempty_iff.mpr ⟨⟨0, hnpos⟩⟩)
    (fun i : Fin n => |triangularResidual n U xhat b i|) (fun i _ => hpoint i)

end LeanFpAnalysis.FP
