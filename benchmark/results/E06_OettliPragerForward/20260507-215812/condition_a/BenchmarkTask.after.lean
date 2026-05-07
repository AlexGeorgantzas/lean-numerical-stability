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
  classical
  rcases hback with ⟨DeltaA, Deltab, hDeltaA, hDeltab, hpert⟩
  intro i
  let r : Fin n → ℝ := fun j => ∑ k : Fin n, A j k * (x k - xhat k)
  have hleft_vec : ∀ i : Fin n, ∑ j : Fin n, A_inv i j * r j = x i - xhat i := by
    intro i
    calc
      ∑ j : Fin n, A_inv i j * r j
          = ∑ j : Fin n, A_inv i j *
              (∑ k : Fin n, A j k * (x k - xhat k)) := by
                rfl
      _ = ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) * (x k - xhat k) := by
            simp_rw [Finset.mul_sum, ← mul_assoc]
            rw [Finset.sum_comm]
            simp_rw [← Finset.sum_mul]
      _ = ∑ k : Fin n, (if i = k then 1 else 0) * (x k - xhat k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hInv i k]
      _ = x i - xhat i := by
            simp
  have hr_eq :
      ∀ j : Fin n, r j = (∑ k : Fin n, DeltaA j k * xhat k) - Deltab j := by
    intro j
    have hx : ∑ k : Fin n, A j k * x k = b j := hAx j
    have hxh :
        ∑ k : Fin n, A j k * xhat k + ∑ k : Fin n, DeltaA j k * xhat k =
          b j + Deltab j := by
      calc
        ∑ k : Fin n, A j k * xhat k + ∑ k : Fin n, DeltaA j k * xhat k
            = ∑ k : Fin n, (A j k + DeltaA j k) * xhat k := by
                simp_rw [add_mul]
                rw [Finset.sum_add_distrib]
        _ = b j + Deltab j := hpert j
    calc
      r j = ∑ k : Fin n, (A j k * x k - A j k * xhat k) := by
              simp [r, mul_sub]
      _ = (∑ k : Fin n, A j k * x k) - ∑ k : Fin n, A j k * xhat k := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ k : Fin n, DeltaA j k * xhat k) - Deltab j := by
              linarith
  have hr_bound :
      ∀ j : Fin n, |r j| ≤ eta * (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
    intro j
    calc
      |r j| = |(∑ k : Fin n, DeltaA j k * xhat k) - Deltab j| := by
                rw [hr_eq j]
      _ ≤ |∑ k : Fin n, DeltaA j k * xhat k| + |Deltab j| := by
                simpa [sub_eq_add_neg] using abs_add (∑ k : Fin n, DeltaA j k * xhat k) (-Deltab j)
      _ ≤ (∑ k : Fin n, |DeltaA j k * xhat k|) + |Deltab j| := by
                exact add_le_add_right
                  (Finset.abs_sum_le_sum_abs (Finset.univ : Finset (Fin n))
                    (fun k => DeltaA j k * xhat k)) _
      _ = (∑ k : Fin n, |DeltaA j k| * |xhat k|) + |Deltab j| := by
                simp_rw [abs_mul]
      _ ≤ (∑ k : Fin n, eta * |A j k| * |xhat k|) + eta * |b j| := by
                apply add_le_add
                · apply Finset.sum_le_sum
                  intro k hk
                  exact mul_le_mul_of_nonneg_right (hDeltaA j k) (abs_nonneg (xhat k))
                · exact hDeltab j
      _ = eta * (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
                rw [mul_add, Finset.mul_sum]
                congr 1
                apply Finset.sum_congr rfl
                intro k hk
                ring
  calc
    |x i - xhat i| = |∑ j : Fin n, A_inv i j * r j| := by
          rw [hleft_vec i]
    _ ≤ ∑ j : Fin n, |A_inv i j * r j| :=
          Finset.abs_sum_le_sum_abs (Finset.univ : Finset (Fin n)) (fun j => A_inv i j * r j)
    _ = ∑ j : Fin n, |A_inv i j| * |r j| := by
          simp_rw [abs_mul]
    _ ≤ ∑ j : Fin n, |A_inv i j| *
          (eta * (∑ k : Fin n, |A j k| * |xhat k| + |b j|)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hr_bound j) (abs_nonneg (A_inv i j))
    _ = eta * ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

end LeanFpAnalysis.FP
