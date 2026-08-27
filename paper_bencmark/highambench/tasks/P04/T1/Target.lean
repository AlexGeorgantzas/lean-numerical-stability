import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T1: same-precision specialization of the chained factor estimate
used in the derivation of equation (3.4). -/
theorem p04_t1_chained_rounding_factor
    (u : ℝ) (q n : ℕ) (α β : ℝ)
    (hu : 0 ≤ u)
    (hvalid : P04GammaValid u (q + n))
    (hα : |α| ≤ p04Gamma u q)
    (hβ : |β| ≤ p04Gamma u n) :
    |α + β + α * β| ≤ p04Gamma u (q + n) := by
  -- PROOF_START
  sorry

end HighamBench
