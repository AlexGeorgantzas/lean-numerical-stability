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
  rcases hQR.result with ⟨DeltaG, Deltag, hPert, hDeltaG, hDeltag⟩
  refine ⟨DeltaG, Deltag, hPert, hDeltaG, hDeltag, ?_⟩
  intro i
  have hleft : IsLeftInverse n ATA ATA_inv := hInv.1
  have hdiff :
      xhat i - x i =
        ∑ j : Fin n, ATA_inv i j *
          (Deltag j - ∑ k : Fin n, DeltaG j k * xhat k) := by
    have hrow : ∀ j : Fin n,
        ∑ k : Fin n, ATA j k * (xhat k - x k) =
          Deltag j - ∑ k : Fin n, DeltaG j k * xhat k := by
      intro j
      have hp := hPert j
      have he := hExact j
      simp [matMulVec] at hp he ⊢
      calc
        ∑ k : Fin n, ATA j k * (xhat k - x k)
            = (∑ k : Fin n, ATA j k * xhat k) -
                ∑ k : Fin n, ATA j k * x k := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = Deltag j - ∑ k : Fin n, DeltaG j k * xhat k := by
              rw [← he]
              have hp' : (∑ x_1 : Fin n, (ATA j x_1 + DeltaG j x_1) * xhat x_1)
                    = (∑ x_1 : Fin n, ATA j x_1 * xhat x_1) +
                      ∑ x_1 : Fin n, DeltaG j x_1 * xhat x_1 := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro k _
                ring
              rw [hp'] at hp
              linarith
    calc
      xhat i - x i
          = ∑ j : Fin n, (if i = j then 1 else 0) * (xhat j - x j) := by
              rw [Finset.sum_eq_single i]
              · simp
              · intro b _ hb
                simp [hb]
              · intro hi
                simp at hi
        _ = ∑ j : Fin n, (∑ k : Fin n, ATA_inv i k * ATA k j) * (xhat j - x j) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hleft i j]
        _ = ∑ k : Fin n, ATA_inv i k *
              (∑ j : Fin n, ATA k j * (xhat j - x j)) := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ∑ j : Fin n, ATA_inv i j *
              (Deltag j - ∑ k : Fin n, DeltaG j k * xhat k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hrow j]
  rw [hdiff]
  calc
    |∑ j : Fin n, ATA_inv i j *
          (Deltag j - ∑ k : Fin n, DeltaG j k * xhat k)|
        ≤ ∑ j : Fin n,
            |ATA_inv i j *
              (Deltag j - ∑ k : Fin n, DeltaG j k * xhat k)| := by
            exact Finset.abs_sum_le_sum_abs Finset.univ _
    _ = ∑ j : Fin n,
            |ATA_inv i j| *
              |Deltag j - ∑ k : Fin n, DeltaG j k * xhat k| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul]
    _ ≤ ∑ j : Fin n, |ATA_inv i j| *
          (∑ k : Fin n, |DeltaG j k| * |xhat k| + |Deltag j|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc
              |Deltag j - ∑ k : Fin n, DeltaG j k * xhat k|
                  ≤ |Deltag j| + |∑ k : Fin n, DeltaG j k * xhat k| := by
                    simpa [sub_eq_add_neg] using
                      abs_add (Deltag j) (-(∑ k : Fin n, DeltaG j k * xhat k))
              _ ≤ |Deltag j| + ∑ k : Fin n, |DeltaG j k * xhat k| := by
                    exact add_le_add_left (Finset.abs_sum_le_sum_abs Finset.univ _) _
              _ = |Deltag j| + ∑ k : Fin n, |DeltaG j k| * |xhat k| := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [abs_mul]
              _ = ∑ k : Fin n, |DeltaG j k| * |xhat k| + |Deltag j| := by
                    ring

end LeanFpAnalysis.FP
