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
  have row_le_rect :
      ∀ {r c : ℕ} (hr : 0 < r) (M : Fin r → Fin c → ℝ) (i : Fin r),
        (∑ j : Fin c, |M i j|) ≤ rectInfNorm r c hr M := by
    intro r c hr M i
    unfold rectInfNorm
    exact Finset.le_sup' (fun i => ∑ j : Fin c, |M i j|) (Finset.mem_univ i)
  have rect_nonneg :
      ∀ {r c : ℕ} (hr : 0 < r) (M : Fin r → Fin c → ℝ),
        0 ≤ rectInfNorm r c hr M := by
    intro r c hr M
    have h0 : (∑ j : Fin c, |M ⟨0, hr⟩ j|) ≤ rectInfNorm r c hr M :=
      row_le_rect hr M ⟨0, hr⟩
    exact le_trans (Finset.sum_nonneg (fun j _ => abs_nonneg (M ⟨0, hr⟩ j))) h0
  have hgamma_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  unfold rectInfNorm
  apply Finset.sup'_le
  intro i _
  calc
    ∑ j : Fin p, |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j|
        ≤ ∑ j : Fin p, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
          apply Finset.sum_le_sum
          intro j _
          exact matMul_error_bound fp m n p A B hn i j
    _ = gamma fp n * ∑ k : Fin n, |A i k| * ∑ j : Fin p, |B k j| := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
    _ ≤ gamma fp n * ∑ k : Fin n, |A i k| * rectInfNorm n p hnpos B := by
          apply mul_le_mul_of_nonneg_left _ hgamma_nonneg
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (row_le_rect hnpos B k) (abs_nonneg (A i k))
    _ = gamma fp n * ((∑ k : Fin n, |A i k|) * rectInfNorm n p hnpos B) := by
          rw [Finset.sum_mul]
    _ ≤ gamma fp n * (rectInfNorm m n hm A * rectInfNorm n p hnpos B) := by
          apply mul_le_mul_of_nonneg_left _ hgamma_nonneg
          exact mul_le_mul_of_nonneg_right (row_le_rect hm A i) (rect_nonneg hnpos B)
    _ = gamma fp n * rectInfNorm m n hm A * rectInfNorm n p hnpos B := by
          ring

end LeanFpAnalysis.FP
