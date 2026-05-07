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
  set a : ℝ := gamma fp (n - 1) ^ 2
  set g : ℝ := gamma fp (2 * n - 2)
  set S : ℝ := sumAbs n p0
  set A : ℝ := |s|
  have hK2_pos : 1 ≤ K - 2 := by omega
  have hK2_le : K - 2 ≤ K - 1 := by omega
  have hstage :
      sumAbs n (hcert.stage (K - 2)) ≤ 3 * A + g ^ (K - 2) * S := by
    simpa [A, g, S] using hcert.abs_stage_bound (K - 2) hK2_pos hK2_le
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using sq_nonneg (gamma fp (n - 1))
  have hg_nonneg : 0 ≤ g := by
    simpa [g] using hgamma_nonneg
  have hS_nonneg' : 0 ≤ S := by
    simpa [S] using hS_nonneg
  have hstage_mul :
      a * sumAbs n (hcert.stage (K - 2)) ≤
        a * (3 * A + g ^ (K - 2) * S) :=
    mul_le_mul_of_nonneg_left hstage ha_nonneg
  have hpow_mul :
      a * (g ^ (K - 2) * S) ≤ g ^ K * S := by
    have hgpow_nonneg : 0 ≤ g ^ (K - 2) := pow_nonneg hg_nonneg _
    have hsq : a ≤ g ^ 2 := by
      simpa [a, g] using hgamma_sq
    have hmul := mul_le_mul_of_nonneg_right hsq hgpow_nonneg
    have hmulS := mul_le_mul_of_nonneg_right hmul hS_nonneg'
    have hKpow : g ^ K = g ^ 2 * g ^ (K - 2) := by
      rw [← pow_add]
      congr 1
      omega
    nlinarith
  calc
    |res - s|
        ≤ fp.u * A + a * sumAbs n (hcert.stage (K - 2)) := by
          simpa [a, A] using hcert.final_rounding_bound
    _ ≤ fp.u * A + a * (3 * A + g ^ (K - 2) * S) := by
          nlinarith
    _ ≤ (fp.u + 3 * a) * A + g ^ K * S := by
          nlinarith
    _ = (fp.u + 3 * gamma fp (n - 1) ^ 2) * |s| +
          gamma fp (2 * n - 2) ^ K * sumAbs n p0 := by
          simp [a, g, S, A]

end LeanFpAnalysis.FP
