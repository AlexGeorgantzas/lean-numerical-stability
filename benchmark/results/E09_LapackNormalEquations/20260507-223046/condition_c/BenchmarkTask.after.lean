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
  have hFwd :=
    ls_normal_equations_forward_error n ATA ATA_inv hInv ATb x xhat
      hExact DeltaG Deltag hPerturbed
  intro i
  calc
    |xhat i - x i|
        ≤ ∑ j : Fin n, |ATA_inv i j| *
            (∑ k : Fin n, |DeltaG j k| * |xhat k| + |Deltag j|) := hFwd i
    _ ≤ ∑ j : Fin n, |ATA_inv i j| *
          (epsG * ∑ k : Fin n, |ATA j k| * |xhat k| +
            epsg * |ATb j|) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hDeltaG_sum :
            ∑ k : Fin n, |DeltaG j k| * |xhat k| ≤
              epsG * ∑ k : Fin n, |ATA j k| * |xhat k| := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_right (hDeltaG j k) (abs_nonneg _)
        linarith [hDeltaG_sum, hDeltag j]

end LeanFpAnalysis.FP
