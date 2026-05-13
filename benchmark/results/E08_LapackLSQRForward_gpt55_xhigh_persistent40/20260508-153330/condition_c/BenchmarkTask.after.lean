import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

theorem lapack_ls_qr_forward_error_certificate
    (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (ATb x xhat : Fin n → ℝ)
    (cG cg : ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (hExact : ∀ i, matMulVec n ATA x i = ATb i)
    (hQR : LSQRSolveBackwardError n ATA ATb xhat cG cg) :
    ∃ DeltaG : Fin n → Fin n → ℝ,
    ∃ Deltag : Fin n → ℝ,
      (∀ i,
        matMulVec n (fun a b => ATA a b + DeltaG a b) xhat i =
          ATb i + Deltag i) ∧
      frobNorm DeltaG ≤ cG ∧
      (∀ i, |Deltag i| ≤ cg) ∧
      ∀ i : Fin n, |xhat i - x i| ≤
        ∑ j : Fin n, |ATA_inv i j| *
          (∑ k : Fin n, |DeltaG j k| * |xhat k| + |Deltag j|) := by
  obtain ⟨DeltaG, Deltag, hPerturbed, hDeltaG, hDeltag⟩ := hQR.result
  refine ⟨DeltaG, Deltag, hPerturbed, hDeltaG, hDeltag, ?_⟩
  exact ls_qr_forward_error n ATA ATA_inv hInv ATb x xhat hExact
    DeltaG Deltag hPerturbed

end LeanFpAnalysis.FP
