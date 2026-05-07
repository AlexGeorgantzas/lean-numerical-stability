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
  let g : ℝ := gamma fp (2 * n - 2)
  let q : ℝ := gamma fp (n - 1) ^ 2
  let A : ℝ := sumAbs n p0
  have hK2_one : 1 ≤ K - 2 := by omega
  have hK2_le : K - 2 ≤ K - 1 := by omega
  have hstage :
      sumAbs n (hcert.stage (K - 2)) ≤ 3 * |s| + g ^ (K - 2) * A := by
    simpa [g, A] using hcert.abs_stage_bound (K - 2) hK2_one hK2_le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hg_nonneg : 0 ≤ g := by
    simpa [g] using hgamma_nonneg
  have hgpow_nonneg : 0 ≤ g ^ (K - 2) := pow_nonneg hg_nonneg _
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using hS_nonneg
  have hmul_stage :
      q * sumAbs n (hcert.stage (K - 2)) ≤
        q * (3 * |s| + g ^ (K - 2) * A) := by
    exact mul_le_mul_of_nonneg_left hstage hq_nonneg
  have hprod :
      q * (g ^ (K - 2) * A) ≤ g ^ K * A := by
    have hq_le_g2 : q ≤ g ^ 2 := by
      simpa [q, g] using hgamma_sq
    have hmul : q * g ^ (K - 2) ≤ g ^ 2 * g ^ (K - 2) := by
      exact mul_le_mul_of_nonneg_right hq_le_g2 hgpow_nonneg
    have hmulA : (q * g ^ (K - 2)) * A ≤ (g ^ 2 * g ^ (K - 2)) * A := by
      exact mul_le_mul_of_nonneg_right hmul hA_nonneg
    have hpow : g ^ 2 * g ^ (K - 2) = g ^ K := by
      rw [← pow_add]
      congr
      omega
    calc
      q * (g ^ (K - 2) * A) = (q * g ^ (K - 2)) * A := by ring
      _ ≤ (g ^ 2 * g ^ (K - 2)) * A := hmulA
      _ = g ^ K * A := by rw [hpow]
  have hq_stage_bound :
      q * sumAbs n (hcert.stage (K - 2)) ≤
        3 * q * |s| + g ^ K * A := by
    calc
      q * sumAbs n (hcert.stage (K - 2))
          ≤ q * (3 * |s| + g ^ (K - 2) * A) := hmul_stage
      _ = 3 * q * |s| + q * (g ^ (K - 2) * A) := by ring
      _ ≤ 3 * q * |s| + g ^ K * A := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hprod (3 * q * |s|)
  have hfinal :
      |res - s| ≤ fp.u * |s| + q * sumAbs n (hcert.stage (K - 2)) := by
    simpa [q] using hcert.final_rounding_bound
  calc
    |res - s|
        ≤ fp.u * |s| + q * sumAbs n (hcert.stage (K - 2)) := hfinal
    _ ≤ fp.u * |s| + (3 * q * |s| + g ^ K * A) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hq_stage_bound (fp.u * |s|)
    _ = (fp.u + 3 * q) * |s| + g ^ K * A := by ring
    _ = (fp.u + 3 * gamma fp (n - 1) ^ 2) * |s| +
          gamma fp (2 * n - 2) ^ K * sumAbs n p0 := by
      simp [q, g, A]

end LeanFpAnalysis.FP
