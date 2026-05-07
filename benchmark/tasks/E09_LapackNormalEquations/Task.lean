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
  sorry

end LeanFpAnalysis.FP
