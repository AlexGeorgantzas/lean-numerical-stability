import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem forwardSub_residual_certificate (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    let xhat := fl_forwardSub fp n L b
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, L i j * xhat j| ≤
        gamma fp n * ∑ j : Fin n, |L i j| * |xhat j| := by
  dsimp
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n L b hdiag hlower hn
  intro i
  have hres :
      b i - ∑ j : Fin n, L i j * fl_forwardSub fp n L b j =
        ∑ j : Fin n, ΔL i j * fl_forwardSub fp n L b j := by
    rw [← hΔL_eq i]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring
  calc
    |b i - ∑ j : Fin n, L i j * fl_forwardSub fp n L b j|
        = |∑ j : Fin n, ΔL i j * fl_forwardSub fp n L b j| := by
            rw [hres]
    _ ≤ ∑ j : Fin n, |ΔL i j * fl_forwardSub fp n L b j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |ΔL i j| * |fl_forwardSub fp n L b j| := by
        simp_rw [abs_mul]
    _ ≤ ∑ j : Fin n, (gamma fp n * |L i j|) * |fl_forwardSub fp n L b j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i j) (abs_nonneg _)
    _ = gamma fp n * ∑ j : Fin n, |L i j| * |fl_forwardSub fp n L b j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

end LeanFpAnalysis.FP
