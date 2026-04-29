import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def fl_scaledDot (fp : FPModel) (n : ℕ)
    (alpha : ℝ) (x y : Fin n → ℝ) : ℝ :=
  fp.fl_mul alpha (fl_dotProduct fp n x y)

theorem scaledDot_backward_error (fp : FPModel) (n : ℕ)
    (alpha : ℝ) (x y : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1)) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (n + 1)) ∧
      fl_scaledDot fp n alpha x y =
        alpha * ∑ i : Fin n, x i * y i * (1 + η i) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hn1
  obtain ⟨θ, hθ, hdot⟩ := dotProduct_backward_error fp n x y hn
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul alpha (fl_dotProduct fp n x y)
  have hδγ : |δ| ≤ gamma fp 1 := by
    exact le_trans hδ (u_le_gamma fp one_pos (gammaValid_mono fp (by omega) hn1))
  let η : Fin n → ℝ := fun i =>
    Classical.choose (gamma_mul fp n 1 (θ i) δ (hθ i) hδγ hn1)
  have hη : ∀ i, |η i| ≤ gamma fp (n + 1) := by
    intro i
    exact (Classical.choose_spec (gamma_mul fp n 1 (θ i) δ (hθ i) hδγ hn1)).1
  have hηeq : ∀ i, (1 + θ i) * (1 + δ) = 1 + η i := by
    intro i
    exact (Classical.choose_spec (gamma_mul fp n 1 (θ i) δ (hθ i) hδγ hn1)).2
  refine ⟨η, hη, ?_⟩
  unfold fl_scaledDot
  rw [hmul, hdot]
  calc
    (alpha * (∑ i : Fin n, x i * y i * (1 + θ i))) * (1 + δ)
        = alpha * ((∑ i : Fin n, x i * y i * (1 + θ i)) * (1 + δ)) := by
            ring
    _ = alpha * (∑ i : Fin n, (x i * y i * (1 + θ i)) * (1 + δ)) := by
            rw [Finset.sum_mul]
    _ = alpha * ∑ i : Fin n, x i * y i * (1 + η i) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [← hηeq i]
            ring

end LeanFpAnalysis.FP
