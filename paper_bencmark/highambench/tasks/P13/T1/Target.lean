import HighamBench.P13Definitions

namespace HighamBench

/-- P13-T1: the lower-bound clause in Lemma 2.2. -/
theorem p13_t1_condition_ge_one {n : ℕ} (ell f : Fin n → ℝ)
    (hvalue : p13InterpolationValue ell f ≠ 0) :
    1 ≤ p13Condition ell f := by
  -- PROOF_START
  sorry

end HighamBench
