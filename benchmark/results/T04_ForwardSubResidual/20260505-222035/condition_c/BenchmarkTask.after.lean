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
  dsimp only
  let xhat := fl_forwardSub fp n L b
  obtain ⟨ΔL, hΔL, hsolve⟩ :=
    forwardSub_backward_error fp n L b hdiag hlower hn
  intro i
  have hsolve_i : ∑ j : Fin n, (L i j + ΔL i j) * xhat j = b i := by
    simpa [xhat] using hsolve i
  have hres_eq :
      b i - ∑ j : Fin n, L i j * xhat j =
        ∑ j : Fin n, ΔL i j * xhat j := by
    rw [← hsolve_i]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring
  calc
    |b i - ∑ j : Fin n, L i j * xhat j|
        = |∑ j : Fin n, ΔL i j * xhat j| := by rw [hres_eq]
    _ ≤ ∑ j : Fin n, |ΔL i j * xhat j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, gamma fp n * |L i j| * |xhat j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hΔL i j) (abs_nonneg _)
    _ = gamma fp n * ∑ j : Fin n, |L i j| * |xhat j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end LeanFpAnalysis.FP
