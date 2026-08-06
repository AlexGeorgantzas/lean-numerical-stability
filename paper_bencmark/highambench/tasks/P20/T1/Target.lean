import HighamBench.P20Definitions

namespace HighamBench

/-- P20-T1: the upper and lower scaling guarantees encoded by (3.4a).
The maximum scaled row coefficient lies in `(theta / 2, theta]`. -/
theorem p20_t1_scaled_row_range {n : ℕ}
    (x : Fin n → ℝ) (lambda theta : ℝ)
    (hn : 0 < n) (hlambda : 0 ≤ lambda)
    (hnorm : 0 < p20InfNormVec x)
    (hlower : theta / (2 * p20InfNormVec x) < lambda)
    (hupper : lambda ≤ theta / p20InfNormVec x) :
    (∀ i : Fin n, |p20ScaleVec lambda x i| ≤ theta) ∧
      ∃ i : Fin n, theta / 2 < |p20ScaleVec lambda x i| := by
  -- PROOF_START
  sorry

end HighamBench
