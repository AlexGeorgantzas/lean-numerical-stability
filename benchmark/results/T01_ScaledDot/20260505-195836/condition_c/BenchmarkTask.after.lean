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
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hn1
  obtain ⟨η, hη, hdot⟩ := dotProduct_backward_error fp n x y hn
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul alpha (fl_dotProduct fp n x y)
  have hδ1 : |δ| ≤ gamma fp 1 :=
    le_trans hδ (u_le_gamma fp one_pos h1)
  have hcomb : ∀ i : Fin n,
      ∃ θ : ℝ, |θ| ≤ gamma fp (n + 1) ∧
        (1 + η i) * (1 + δ) = 1 + θ := by
    intro i
    simpa [Nat.add_comm] using
      gamma_mul fp n 1 (η i) δ (hη i) hδ1 hn1
  let θ : Fin n → ℝ := fun i => Classical.choose (hcomb i)
  have hθ : ∀ i, |θ i| ≤ gamma fp (n + 1) := fun i =>
    (Classical.choose_spec (hcomb i)).1
  have hθeq : ∀ i, (1 + η i) * (1 + δ) = 1 + θ i := fun i =>
    (Classical.choose_spec (hcomb i)).2
  refine ⟨θ, hθ, ?_⟩
  unfold fl_scaledDot
  rw [hmul, hdot]
  calc
    alpha * (∑ i : Fin n, x i * y i * (1 + η i)) * (1 + δ)
        = alpha * ((∑ i : Fin n, x i * y i * (1 + η i)) * (1 + δ)) := by
          ring
    _ = alpha * ∑ i : Fin n, (x i * y i * (1 + η i)) * (1 + δ) := by
          rw [Finset.sum_mul]
    _ = alpha * ∑ i : Fin n, x i * y i * (1 + θ i) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [← hθeq i]
          ring

end LeanFpAnalysis.FP
