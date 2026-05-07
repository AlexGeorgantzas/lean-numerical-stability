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
  sorry

end LeanFpAnalysis.FP
