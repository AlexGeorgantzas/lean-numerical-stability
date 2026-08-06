import HighamBench.P20Definitions

namespace HighamBench

/-- P20-T2: in the regime described after (3.26), the accumulation-underflow
contribution is bounded by the input-underflow contribution. -/
theorem p20_t2_accumulation_underflow_le_input {m n q : ℕ}
    (theta gmin Gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ)
    (htheta : 1 ≤ theta) (hGmin : 0 ≤ Gmin) (hGg : Gmin ≤ gmin) :
    p20SingleAccumUnderflowBound theta Gmin A B ≤
      p20SingleInputUnderflowBound theta gmin A B := by
  -- PROOF_START
  sorry

end HighamBench
