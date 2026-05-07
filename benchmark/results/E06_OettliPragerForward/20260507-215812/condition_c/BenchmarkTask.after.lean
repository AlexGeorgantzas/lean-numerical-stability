import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

def opBackwardCompatible (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (eta : ℝ) : Prop :=
  ∃ DeltaA : Fin n → Fin n → ℝ,
  ∃ Deltab : Fin n → ℝ,
    (∀ i j, |DeltaA i j| ≤ eta * |A i j|) ∧
    (∀ i, |Deltab i| ≤ eta * |b i|) ∧
    ∀ i, ∑ j : Fin n, (A i j + DeltaA i j) * x j = b i + Deltab i

theorem oettli_prager_backward_to_forward_error
    (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (x xhat b : Fin n → ℝ) (eta : ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (heta_nonneg : 0 ≤ eta)
    (hback : opBackwardCompatible n A xhat b eta) :
    ∀ i : Fin n, |x i - xhat i| ≤
      eta * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
  obtain ⟨DeltaA, Deltab, hDeltaA, hDeltab, hpert⟩ := hback
  have hDiff : ∀ i, ∑ j : Fin n, A i j * (x j - xhat j) =
      (∑ j : Fin n, DeltaA i j * xhat j) - Deltab i := by
    intro i
    have hsub : ∑ j : Fin n, A i j * (x j - xhat j) =
        (∑ j : Fin n, A i j * x j) - ∑ j : Fin n, A i j * xhat j := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    rw [hsub, hAx i]
    have hpert' : ∑ j : Fin n, A i j * xhat j + ∑ j : Fin n, DeltaA i j * xhat j =
        b i + Deltab i := by
      rw [← Finset.sum_add_distrib]
      convert hpert i using 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    linarith
  have hSol : ∀ i, x i - xhat i =
      ∑ j : Fin n, A_inv i j * ((∑ k : Fin n, DeltaA j k * xhat k) - Deltab j) := by
    intro i
    have key : ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * (x k - xhat k)) =
        ∑ j : Fin n, A_inv i j * ((∑ k : Fin n, DeltaA j k * xhat k) - Deltab j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hDiff j]
    have lhs_eq : ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * (x k - xhat k)) =
        ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) * (x k - xhat k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [lhs_eq] at key
    have inv_eq : ∀ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) =
        if i = k then 1 else 0 := fun k => hInv i k
    have lhs_simp : ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) * (x k - xhat k) =
        x i - xhat i := by
      simp_rw [inv_eq]
      simp
    linarith
  intro i
  rw [hSol i]
  calc
    |∑ j : Fin n, A_inv i j * ((∑ k : Fin n, DeltaA j k * xhat k) - Deltab j)|
        ≤ ∑ j : Fin n, |A_inv i j * ((∑ k : Fin n, DeltaA j k * xhat k) - Deltab j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A_inv i j| * |(∑ k : Fin n, DeltaA j k * xhat k) - Deltab j| := by
      apply Finset.sum_congr rfl
      intro j _
      exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        (|∑ k : Fin n, DeltaA j k * xhat k| + |Deltab j|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (abs_sub_le _ _) (abs_nonneg _)
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        ((∑ k : Fin n, |DeltaA j k * xhat k|) + |Deltab j|) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ = ∑ j : Fin n, |A_inv i j| *
        ((∑ k : Fin n, |DeltaA j k| * |xhat k|) + |Deltab j|) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        ((∑ k : Fin n, eta * |A j k| * |xhat k|) + eta * |b j|) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hDeltaA j k) (abs_nonneg _)
      · exact hDeltab j
    _ = eta * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hinner : ∑ k : Fin n, eta * |A j k| * |xhat k| =
          eta * ∑ k : Fin n, |A j k| * |xhat k| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hinner]
      ring

end LeanFpAnalysis.FP
