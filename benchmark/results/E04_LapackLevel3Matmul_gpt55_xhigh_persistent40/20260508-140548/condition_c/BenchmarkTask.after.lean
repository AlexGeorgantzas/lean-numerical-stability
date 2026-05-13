import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def rectInfNorm (m n : ℕ) (hm : 0 < m)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => ∑ j : Fin n, |A i j|)

theorem lapack_level3_matmul_forward_error
    (fp : FPModel) (m n p : ℕ) (hm : 0 < m) (hnpos : 0 < n)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    rectInfNorm m p hm
        (fun i j => fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * rectInfNorm m n hm A * rectInfNorm n p hnpos B := by
  have hγ_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hArow : ∀ i : Fin m, ∑ k : Fin n, |A i k| ≤ rectInfNorm m n hm A := by
    intro i
    unfold rectInfNorm
    exact Finset.le_sup' (fun i => ∑ k : Fin n, |A i k|) (Finset.mem_univ i)
  have hBrow : ∀ k : Fin n, ∑ j : Fin p, |B k j| ≤ rectInfNorm n p hnpos B := by
    intro k
    unfold rectInfNorm
    exact Finset.le_sup' (fun k => ∑ j : Fin p, |B k j|) (Finset.mem_univ k)
  have hBnorm_nonneg : 0 ≤ rectInfNorm n p hnpos B := by
    unfold rectInfNorm
    exact le_trans
      (Finset.sum_nonneg (fun j _ => abs_nonneg (B ⟨0, hnpos⟩ j)))
      (Finset.le_sup' (fun k => ∑ j : Fin p, |B k j|)
        (Finset.mem_univ (⟨0, hnpos⟩ : Fin n)))
  unfold rectInfNorm
  apply Finset.sup'_le
  intro i _
  calc
    ∑ j : Fin p, |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j|
        ≤ ∑ j : Fin p, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
          apply Finset.sum_le_sum
          intro j _
          exact matMul_error_bound fp m n p A B hn i j
    _ = gamma fp n * ∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j| := by
          rw [Finset.mul_sum]
    _ = gamma fp n * ∑ k : Fin n, |A i k| * ∑ j : Fin p, |B k j| := by
          congr 1
          rw [Finset.sum_comm]
          congr 1
          ext k
          rw [Finset.mul_sum]
    _ ≤ gamma fp n * ∑ k : Fin n, |A i k| * rectInfNorm n p hnpos B := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hBrow k) (abs_nonneg (A i k))
          · exact hγ_nonneg
    _ = gamma fp n * ((∑ k : Fin n, |A i k|) * rectInfNorm n p hnpos B) := by
          rw [Finset.sum_mul]
    _ ≤ gamma fp n * (rectInfNorm m n hm A * rectInfNorm n p hnpos B) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right (hArow i) hBnorm_nonneg
          · exact hγ_nonneg
    _ = gamma fp n * rectInfNorm m n hm A * rectInfNorm n p hnpos B := by
          ring

end LeanFpAnalysis.FP
