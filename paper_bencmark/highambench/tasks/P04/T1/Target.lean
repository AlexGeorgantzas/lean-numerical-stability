import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T1: same-precision specialization of the chained factor estimate
used in the derivation of equation (3.4). -/
theorem p04_t1_chained_rounding_factor
    (u : ℝ) (q n : ℕ) (α β : ℝ)
    (hu : 0 ≤ u)
    (hvalid : GammaValid u (q + n))
    (hα : |α| ≤ gamma u q)
    (hβ : |β| ≤ gamma u n) :
    |α + β + α * β| ≤ gamma u (q + n) := by
  -- PROOF_START
  sorry

end HighamBench
