import HighamBench.P10Definitions

namespace HighamBench

/-- P10-T1: one inherited-error amplification term from equation (8). -/
theorem p10_t1_inherited_right_product_error {n : ℕ}
    (A dB : P10Matrix n) :
    p10FrobNorm (p10MatMul n A dB) ≤
      p10FrobNorm A * p10FrobNorm dB := by
  -- PROOF_START
  sorry

end HighamBench
