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
  have _ : 0 ≤ epsG := hepsG_nonneg
  have _ : 0 ≤ epsg := hepsg_nonneg
  have hFwd :
      |x i - xhat i| ≤
        ∑ j : Fin n, |ATA_inv i j| *
          (∑ k : Fin n, |DeltaG j k| * |xhat k| + |Deltag j|) :=
    normwise_perturbation_bound n ATA ATA_inv x xhat ATb DeltaG Deltag
      hInv.1 (fun i => hExact i) hPerturbed i
  rw [abs_sub_comm]
  calc
    |x i - xhat i|
        ≤ ∑ j : Fin n, |ATA_inv i j| *
            (∑ k : Fin n, |DeltaG j k| * |xhat k| + |Deltag j|) := hFwd
    _ ≤ ∑ j : Fin n, |ATA_inv i j| *
          (epsG * ∑ k : Fin n, |ATA j k| * |xhat k| +
            epsg * |ATb j|) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left
        · apply add_le_add
          · calc
              ∑ k : Fin n, |DeltaG j k| * |xhat k|
                  ≤ ∑ k : Fin n, (epsG * |ATA j k|) * |xhat k| := by
                    apply Finset.sum_le_sum
                    intro k _
                    exact mul_le_mul_of_nonneg_right (hDeltaG j k) (abs_nonneg _)
              _ = epsG * ∑ k : Fin n, |ATA j k| * |xhat k| := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
          · exact hDeltag j
        · exact abs_nonneg _

end LeanFpAnalysis.FP
