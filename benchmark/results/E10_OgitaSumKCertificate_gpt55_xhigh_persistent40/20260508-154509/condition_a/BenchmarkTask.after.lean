import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def sumAbs (n : ℕ) (p : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |p i|

structure SumKDistillationCertificate (fp : FPModel) (n K : ℕ)
    (p0 : Fin n → ℝ) (res s : ℝ) where
  stage : ℕ → Fin n → ℝ
  stage_zero : ∀ i, stage 0 i = p0 i
  sum_preserved : ∀ k, k ≤ K - 1 → ∑ i : Fin n, stage k i = s
  abs_stage_bound : ∀ k,
    1 ≤ k → k ≤ K - 1 →
      sumAbs n (stage k) ≤
        3 * |s| + gamma fp (2 * n - 2) ^ k * sumAbs n p0
  final_rounding_bound :
    |res - s| ≤
      fp.u * |s| + gamma fp (n - 1) ^ 2 * sumAbs n (stage (K - 2))

theorem ogita_sumK_absolute_error_certificate
    (fp : FPModel) (n K : ℕ) (p0 : Fin n → ℝ) (res s : ℝ)
    (hK : 3 ≤ K)
    (hgamma_nonneg : 0 ≤ gamma fp (2 * n - 2))
    (hgamma_sq :
      gamma fp (n - 1) ^ 2 ≤ gamma fp (2 * n - 2) ^ 2)
    (hS_nonneg : 0 ≤ sumAbs n p0)
    (hcert : SumKDistillationCertificate fp n K p0 res s) :
    |res - s| ≤
      (fp.u + 3 * gamma fp (n - 1) ^ 2) * |s| +
        gamma fp (2 * n - 2) ^ K * sumAbs n p0 := by
  have hK2_pos : 1 ≤ K - 2 := by omega
  have hK2_le : K - 2 ≤ K - 1 := by omega
  have hstage :=
    hcert.abs_stage_bound (K - 2) hK2_pos hK2_le
  have hA_nonneg : 0 ≤ gamma fp (n - 1) ^ 2 := sq_nonneg _
  have hstage_mul :
      gamma fp (n - 1) ^ 2 * sumAbs n (hcert.stage (K - 2)) ≤
        gamma fp (n - 1) ^ 2 *
          (3 * |s| + gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0) :=
    mul_le_mul_of_nonneg_left hstage hA_nonneg
  have hfirst :
      |res - s| ≤
        fp.u * |s| +
          gamma fp (n - 1) ^ 2 *
            (3 * |s| + gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0) := by
    linarith [hcert.final_rounding_bound, hstage_mul]
  have hpow_nonneg : 0 ≤ gamma fp (2 * n - 2) ^ (K - 2) :=
    pow_nonneg hgamma_nonneg _
  have htail_factor_nonneg :
      0 ≤ gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0 :=
    mul_nonneg hpow_nonneg hS_nonneg
  have htail :
      gamma fp (n - 1) ^ 2 *
          (gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0) ≤
        gamma fp (2 * n - 2) ^ K * sumAbs n p0 := by
    calc
      gamma fp (n - 1) ^ 2 *
          (gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0)
          ≤ gamma fp (2 * n - 2) ^ 2 *
              (gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0) :=
            mul_le_mul_of_nonneg_right hgamma_sq htail_factor_nonneg
      _ = gamma fp (2 * n - 2) ^ K * sumAbs n p0 := by
            rw [← mul_assoc]
            congr 1
            rw [← pow_add]
            congr 1
            omega
  calc
    |res - s| ≤
        fp.u * |s| +
          gamma fp (n - 1) ^ 2 *
            (3 * |s| + gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0) :=
      hfirst
    _ = (fp.u + 3 * gamma fp (n - 1) ^ 2) * |s| +
          gamma fp (n - 1) ^ 2 *
            (gamma fp (2 * n - 2) ^ (K - 2) * sumAbs n p0) := by ring
    _ ≤ (fp.u + 3 * gamma fp (n - 1) ^ 2) * |s| +
          gamma fp (2 * n - 2) ^ K * sumAbs n p0 :=
      add_le_add_right htail _

end LeanFpAnalysis.FP
