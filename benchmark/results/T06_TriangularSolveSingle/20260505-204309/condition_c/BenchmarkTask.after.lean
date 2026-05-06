import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem triangularSolve_single_backward_error (fp : FPModel) (n : ℕ)
    (L U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hLdiag : ∀ i, L i i ≠ 0)
    (hUdiag : ∀ i, U i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    let yhat := fl_forwardSub fp n L b
    let xhat := fl_backSub fp n U yhat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j,
        |ΔA i j| ≤
          (2 * gamma fp n + gamma fp n ^ 2) *
            ∑ k : Fin n, |L i k| * |U k j|) ∧
      ∀ i, ∑ j : Fin n,
        ((∑ k : Fin n, L i k * U k j) + ΔA i j) * xhat j = b i := by
  intro yhat xhat
  obtain ⟨ΔL, ΔU, hΔL_bound, hΔU_bound, hsolve⟩ :=
    triangularSolve_backward_error fp n L U b hLdiag hUdiag hLT hUT hn
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    ∑ k : Fin n, L i k * ΔU k j +
    ∑ k : Fin n, ΔL i k * U k j +
    ∑ k : Fin n, ΔL i k * ΔU k j
  refine ⟨ΔA, fun i j => ?_, fun i => ?_⟩
  · have hγ_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have h1 : |∑ k : Fin n, L i k * ΔU k j| ≤
        gamma fp n * ∑ k : Fin n, |L i k| * |U k j| := by
      calc |∑ k : Fin n, L i k * ΔU k j|
          ≤ ∑ k : Fin n, |L i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |L i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
        _ ≤ ∑ k : Fin n, |L i k| * (gamma fp n * |U k j|) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hΔU_bound k j) (abs_nonneg _)
        _ = gamma fp n * ∑ k : Fin n, |L i k| * |U k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    have h2 : |∑ k : Fin n, ΔL i k * U k j| ≤
        gamma fp n * ∑ k : Fin n, |L i k| * |U k j| := by
      calc |∑ k : Fin n, ΔL i k * U k j|
          ≤ ∑ k : Fin n, |ΔL i k * U k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |U k j| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |U k j| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
        _ = gamma fp n * ∑ k : Fin n, |L i k| * |U k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    have h3 : |∑ k : Fin n, ΔL i k * ΔU k j| ≤
        gamma fp n ^ 2 * ∑ k : Fin n, |L i k| * |U k j| := by
      calc |∑ k : Fin n, ΔL i k * ΔU k j|
          ≤ ∑ k : Fin n, |ΔL i k * ΔU k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |ΔL i k| * |ΔU k j| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
        _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * (gamma fp n * |U k j|) := by
            apply Finset.sum_le_sum
            intro k _
            apply mul_le_mul (hΔL_bound i k) (hΔU_bound k j)
              (abs_nonneg _) (mul_nonneg hγ_nonneg (abs_nonneg _))
        _ = gamma fp n ^ 2 * ∑ k : Fin n, |L i k| * |U k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    let W := ∑ k : Fin n, |L i k| * |U k j|
    have habs : |(∑ k, L i k * ΔU k j) +
          (∑ k, ΔL i k * U k j) + (∑ k, ΔL i k * ΔU k j)| ≤
        |∑ k, L i k * ΔU k j| +
          |∑ k, ΔL i k * U k j| + |∑ k, ΔL i k * ΔU k j| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (∑ k, L i k * ΔU k j),
          neg_abs_le (∑ k, ΔL i k * U k j),
          neg_abs_le (∑ k, ΔL i k * ΔU k j)]
      · linarith [le_abs_self (∑ k, L i k * ΔU k j),
          le_abs_self (∑ k, ΔL i k * U k j),
          le_abs_self (∑ k, ΔL i k * ΔU k j)]
    calc |ΔA i j|
        = |(∑ k, L i k * ΔU k j) +
            (∑ k, ΔL i k * U k j) + (∑ k, ΔL i k * ΔU k j)| := rfl
      _ ≤ |∑ k, L i k * ΔU k j| +
          |∑ k, ΔL i k * U k j| + |∑ k, ΔL i k * ΔU k j| := habs
      _ ≤ gamma fp n * W + gamma fp n * W + gamma fp n ^ 2 * W := by
          linarith [h1, h2, h3]
      _ = (2 * gamma fp n + gamma fp n ^ 2) * W := by ring
  · have hexpand : ∀ j : Fin n,
        ∑ k : Fin n, (L i k + ΔL i k) * (U k j + ΔU k j) =
        (∑ k : Fin n, L i k * U k j) + ΔA i j := by
      intro j
      have hprod : ∑ k : Fin n, (L i k + ΔL i k) * (U k j + ΔU k j) =
          ∑ k, L i k * U k j + ∑ k, L i k * ΔU k j +
          ∑ k, ΔL i k * U k j + ∑ k, ΔL i k * ΔU k j := by
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
        ring
      rw [hprod]
      show ∑ k, L i k * U k j + ∑ k, L i k * ΔU k j +
          ∑ k, ΔL i k * U k j + ∑ k, ΔL i k * ΔU k j =
        (∑ k, L i k * U k j) +
          (∑ k, L i k * ΔU k j + ∑ k, ΔL i k * U k j +
            ∑ k, ΔL i k * ΔU k j)
      ring
    rw [← hsolve i]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hexpand j]

end LeanFpAnalysis.FP
