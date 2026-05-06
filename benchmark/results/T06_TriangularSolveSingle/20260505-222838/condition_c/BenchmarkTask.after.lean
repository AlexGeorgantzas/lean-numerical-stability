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
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    forwardSub_backward_error fp n L b hLdiag hLT hn
  obtain ⟨ΔU, hΔU_bound, hΔU_eq⟩ :=
    backSub_backward_error fp n U yhat hUdiag hUT hn
  let ΔA : Fin n → Fin n → ℝ := fun i j =>
    ∑ k : Fin n, L i k * ΔU k j +
    ∑ k : Fin n, ΔL i k * U k j +
    ∑ k : Fin n, ΔL i k * ΔU k j
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    have h2 : |∑ k : Fin n, L i k * ΔU k j| ≤
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
    have h3 : |∑ k : Fin n, ΔL i k * U k j| ≤
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
    have h4 : |∑ k : Fin n, ΔL i k * ΔU k j| ≤
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
              (abs_nonneg _) (mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _))
        _ = gamma fp n ^ 2 * ∑ k : Fin n, |L i k| * |U k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    let W := ∑ k : Fin n, |L i k| * |U k j|
    let a := ∑ k : Fin n, L i k * ΔU k j
    let b' := ∑ k : Fin n, ΔL i k * U k j
    let c := ∑ k : Fin n, ΔL i k * ΔU k j
    have habc : |a + b' + c| ≤ |a| + |b'| + |c| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le a, neg_abs_le b', neg_abs_le c]
      · linarith [le_abs_self a, le_abs_self b', le_abs_self c]
    calc |ΔA i j|
        = |a + b' + c| := rfl
      _ ≤ |a| + |b'| + |c| := habc
      _ ≤ gamma fp n * W + gamma fp n * W + gamma fp n ^ 2 * W := by
          linarith [h2, h3, h4]
      _ = (2 * gamma fp n + gamma fp n ^ 2) * W := by ring
  · intro i
    have hb : ∑ k : Fin n, (L i k + ΔL i k) *
        (∑ j : Fin n, (U k j + ΔU k j) * xhat j) = b i := by
      rw [← hΔL_eq i]
      apply Finset.sum_congr rfl
      intro k _
      rw [hΔU_eq k]
    have hexpand : ∀ j : Fin n,
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
          (∑ k, L i k * ΔU k j +
           ∑ k, ΔL i k * U k j + ∑ k, ΔL i k * ΔU k j)
      ring
    rw [← hb]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hexpand j]

end LeanFpAnalysis.FP
