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
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn1
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hn1
  obtain ⟨η, hη, hdot⟩ := dotProduct_backward_error fp n x y hn
  obtain ⟨δ, hδu, hadd⟩ := fp.model_add c (fl_dotProduct fp n x y)
  have hδ1 : |δ| ≤ gamma fp 1 :=
    le_trans hδu (u_le_gamma fp one_pos h1)
  have hδn1 : |δ| ≤ gamma fp (n + 1) := by
    exact le_trans hδ1 (gamma_mono fp (by omega) hn1)
  let ε : Fin n → ℝ := fun i => η i + δ + η i * δ
  have hε : ∀ i, |ε i| ≤ gamma fp (n + 1) := fun i => by
    obtain ⟨e, he, heq⟩ := gamma_mul fp n 1 (η i) δ (hη i) hδ1 hn1
    have hval : e = ε i := by
      have hring : (1 + η i) * (1 + δ) = 1 + ε i := by
        simp only [ε]
        ring
      linarith [heq, hring]
    rw [← hval]
    exact he
  have herr :
      fl_shiftedDot fp n c x y - (c + ∑ i : Fin n, x i * y i) =
        c * δ + ∑ i : Fin n, x i * y i * ε i := by
    unfold fl_shiftedDot
    rw [hadd, hdot]
    rw [add_mul, Finset.sum_mul]
    simp only [ε]
    ring_nf
    rw [← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr]
  calc
    |c * δ + ∑ i : Fin n, x i * y i * ε i|
        ≤ |c * δ| + |∑ i : Fin n, x i * y i * ε i| := abs_add_le _ _
    _ ≤ |c * δ| + ∑ i : Fin n, |x i * y i * ε i| := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left
          (Finset.abs_sum_le_sum_abs (fun i : Fin n => x i * y i * ε i) Finset.univ)
          |c * δ|
    _ = |c| * |δ| + ∑ i : Fin n, |x i| * |y i| * |ε i| := by
      simp only [abs_mul]
    _ ≤ |c| * gamma fp (n + 1) +
          ∑ i : Fin n, |x i| * |y i| * gamma fp (n + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hδn1 (abs_nonneg _))
        (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hε i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = gamma fp (n + 1) *
          (|c| + ∑ i : Fin n, |x i| * |y i|) := by
      rw [← Finset.sum_mul]
      ring

end LeanFpAnalysis.FP
