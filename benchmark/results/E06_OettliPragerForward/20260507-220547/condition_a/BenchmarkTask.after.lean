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
  intro i
  rcases hback with ⟨DeltaA, Deltab, hDeltaA, hDeltab, hback_eq⟩
  have hres : ∀ j : Fin n,
      ∑ k : Fin n, A j k * (x k - xhat k) =
        ∑ k : Fin n, DeltaA j k * xhat k - Deltab j := by
    intro j
    have hbackj := hback_eq j
    have hAxj := hAx j
    calc
      ∑ k : Fin n, A j k * (x k - xhat k)
          = (∑ k : Fin n, A j k * x k) -
              ∑ k : Fin n, A j k * xhat k := by
            simp only [mul_sub, Finset.sum_sub_distrib]
      _ = ∑ k : Fin n, DeltaA j k * xhat k - Deltab j := by
            rw [hAxj]
            have hbackj' :
                (∑ k : Fin n, A j k * xhat k) +
                    ∑ k : Fin n, DeltaA j k * xhat k =
                  b j + Deltab j := by
              simpa only [add_mul, Finset.sum_add_distrib] using hbackj
            linarith
  have hrepr :
      x i - xhat i =
        ∑ j : Fin n, A_inv i j *
          (∑ k : Fin n, DeltaA j k * xhat k - Deltab j) := by
    calc
      x i - xhat i
          = ∑ k : Fin n, (if i = k then 1 else 0) * (x k - xhat k) := by
            simp
      _ = ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) *
            (x k - xhat k) := by
            simp only [hInv]
      _ = ∑ j : Fin n, A_inv i j *
            (∑ k : Fin n, A j k * (x k - xhat k)) := by
            rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            congr 1
            ext j
            rw [Finset.mul_sum]
            congr 1
            ext k
            ring
      _ = ∑ j : Fin n, A_inv i j *
            (∑ k : Fin n, DeltaA j k * xhat k - Deltab j) := by
            congr 1
            ext j
            rw [hres j]
  rw [hrepr]
  calc
    |∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, DeltaA j k * xhat k - Deltab j)|
        ≤ ∑ j : Fin n,
            |A_inv i j *
              (∑ k : Fin n, DeltaA j k * xhat k - Deltab j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n,
          |A_inv i j| *
            |∑ k : Fin n, DeltaA j k * xhat k - Deltab j| := by
          simp only [abs_mul]
    _ ≤ ∑ j : Fin n,
          |A_inv i j| *
            (∑ k : Fin n, |DeltaA j k * xhat k| + |Deltab j|) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc
            |∑ k : Fin n, DeltaA j k * xhat k - Deltab j|
                ≤ |∑ k : Fin n, DeltaA j k * xhat k| + |Deltab j| := by
                  simpa [sub_eq_add_neg] using
                    abs_add (∑ k : Fin n, DeltaA j k * xhat k) (-Deltab j)
            _ ≤ (∑ k : Fin n, |DeltaA j k * xhat k|) + |Deltab j| := by
                  gcongr
                  exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ (∑ k : Fin n, |DeltaA j k * xhat k|) +
                  ∑ k : Fin n, |Deltab j| := by
                  exact add_le_add_left
                    (Finset.single_le_sum
                      (fun _ _ => abs_nonneg (Deltab j))
                      (Finset.mem_univ i)) _
            _ = ∑ k : Fin n, |DeltaA j k * xhat k| + |Deltab j| := by
                  rw [Finset.sum_add_distrib]
    _ ≤ ∑ j : Fin n,
          |A_inv i j| *
            (∑ k : Fin n, eta * |A j k| * |xhat k| + eta * |b j|) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          gcongr with k
          · calc
              |DeltaA j k * xhat k| = |DeltaA j k| * |xhat k| := abs_mul _ _
              _ ≤ (eta * |A j k|) * |xhat k| := by
                exact mul_le_mul_of_nonneg_right (hDeltaA j k) (abs_nonneg _)
              _ = eta * |A j k| * |xhat k| := by ring
          · exact hDeltab j
    _ = eta * ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
          calc
            ∑ j : Fin n,
                |A_inv i j| *
                  (∑ k : Fin n, eta * |A j k| * |xhat k| + eta * |b j|)
                = ∑ j : Fin n,
                    eta * (|A_inv i j| *
                      (∑ k : Fin n, |A j k| * |xhat k| + |b j|)) := by
                  congr 1
                  ext j
                  calc
                    |A_inv i j| *
                        (∑ k : Fin n, eta * |A j k| * |xhat k| + eta * |b j|)
                        = |A_inv i j| *
                            (eta * ∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
                          congr 1
                          rw [Finset.mul_sum]
                          congr 1
                          ext k
                          ring
                    _ = eta * (|A_inv i j| *
                          (∑ k : Fin n, |A j k| * |xhat k| + |b j|)) := by
                          ring
            _ = eta * ∑ j : Fin n, |A_inv i j| *
                  (∑ k : Fin n, |A j k| * |xhat k| + |b j|) := by
                  rw [Finset.mul_sum]

end LeanFpAnalysis.FP
