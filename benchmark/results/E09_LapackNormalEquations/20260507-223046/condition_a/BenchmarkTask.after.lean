import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem lapack_normal_equations_forward_error_certificate
    (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (ATb x xhat : Fin n → ℝ)
    (DeltaG : Fin n → Fin n → ℝ) (Deltag : Fin n → ℝ)
    (epsG epsg : ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (hExact : ∀ i, matMulVec n ATA x i = ATb i)
    (hPerturbed : ∀ i,
      ∑ j : Fin n, (ATA i j + DeltaG i j) * xhat j = ATb i + Deltag i)
    (hDeltaG : ∀ i j, |DeltaG i j| ≤ epsG * |ATA i j|)
    (hDeltag : ∀ i, |Deltag i| ≤ epsg * |ATb i|)
    (hepsG_nonneg : 0 ≤ epsG)
    (hepsg_nonneg : 0 ≤ epsg) :
    ∀ i : Fin n, |xhat i - x i| ≤
      ∑ j : Fin n, |ATA_inv i j| *
        (epsG * ∑ k : Fin n, |ATA j k| * |xhat k| +
          epsg * |ATb j|) := by
  intro i
  let r : Fin n → ℝ := fun j => ∑ k : Fin n, ATA j k * (xhat k - x k)
  have hr_eq : ∀ j : Fin n, r j = Deltag j - ∑ k : Fin n, DeltaG j k * xhat k := by
    intro j
    have hExact_j : ∑ k : Fin n, ATA j k * x k = ATb j := by
      simpa [matMulVec] using hExact j
    have hPert_j :
        (∑ k : Fin n, ATA j k * xhat k) +
          (∑ k : Fin n, DeltaG j k * xhat k) = ATb j + Deltag j := by
      calc
        (∑ k : Fin n, ATA j k * xhat k) +
            (∑ k : Fin n, DeltaG j k * xhat k)
            = ∑ k : Fin n, (ATA j k + DeltaG j k) * xhat k := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = ATb j + Deltag j := hPerturbed j
    calc
      r j = (∑ k : Fin n, ATA j k * xhat k) -
          (∑ k : Fin n, ATA j k * x k) := by
            simp [r, Finset.sum_sub_distrib, mul_sub]
      _ = Deltag j - ∑ k : Fin n, DeltaG j k * xhat k := by
            linarith
  have hr_bound : ∀ j : Fin n, |r j| ≤
      epsG * (∑ k : Fin n, |ATA j k| * |xhat k|) + epsg * |ATb j| := by
    intro j
    have hDG_sum :
        |∑ k : Fin n, DeltaG j k * xhat k| ≤
          epsG * (∑ k : Fin n, |ATA j k| * |xhat k|) := by
      calc
        |∑ k : Fin n, DeltaG j k * xhat k|
            ≤ ∑ k : Fin n, |DeltaG j k * xhat k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |DeltaG j k| * |xhat k| := by
              simp [abs_mul]
        _ ≤ ∑ k : Fin n, epsG * |ATA j k| * |xhat k| := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_right (hDeltaG j k) (abs_nonneg (xhat k))
        _ = epsG * (∑ k : Fin n, |ATA j k| * |xhat k|) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
    calc
      |r j| = |Deltag j - ∑ k : Fin n, DeltaG j k * xhat k| := by rw [hr_eq j]
      _ ≤ |Deltag j| + |∑ k : Fin n, DeltaG j k * xhat k| := by
            simpa [sub_eq_add_neg, abs_neg, add_comm, add_left_comm, add_assoc]
              using abs_add (Deltag j) (-(∑ k : Fin n, DeltaG j k * xhat k))
      _ ≤ epsg * |ATb j| + epsG * (∑ k : Fin n, |ATA j k| * |xhat k|) := by
            exact add_le_add (hDeltag j) hDG_sum
      _ = epsG * (∑ k : Fin n, |ATA j k| * |xhat k|) + epsg * |ATb j| := by
            ring
  have herror_eq : xhat i - x i = ∑ j : Fin n, ATA_inv i j * r j := by
    have hsingle :
        (∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * (xhat k - x k)) =
          xhat i - x i := by
      simp
    calc
      xhat i - x i
          = ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * (xhat k - x k) := by
              exact hsingle.symm
      _ = ∑ k : Fin n, (∑ j : Fin n, ATA_inv i j * ATA j k) * (xhat k - x k) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [(hInv.1) i k]
      _ = ∑ k : Fin n, ∑ j : Fin n,
            ATA_inv i j * ATA j k * (xhat k - x k) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = ∑ j : Fin n, ∑ k : Fin n,
            ATA_inv i j * ATA j k * (xhat k - x k) := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, ATA_inv i j * r j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              simp [r]
              ring
  calc
    |xhat i - x i| = |∑ j : Fin n, ATA_inv i j * r j| := by rw [herror_eq]
    _ ≤ ∑ j : Fin n, |ATA_inv i j * r j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |ATA_inv i j| * |r j| := by
          simp [abs_mul]
    _ ≤ ∑ j : Fin n, |ATA_inv i j| *
          (epsG * ∑ k : Fin n, |ATA j k| * |xhat k| + epsg * |ATb j|) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hr_bound j) (abs_nonneg (ATA_inv i j))

end LeanFpAnalysis.FP
