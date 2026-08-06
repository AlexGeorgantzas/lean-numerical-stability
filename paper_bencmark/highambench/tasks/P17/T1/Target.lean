import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

/-- P17-T1: deterministic one-atom specialization of Theorem 3.6's envelope
for the accumulated product of limited-precision rounding factors. -/
theorem p17_t1_product_bias_envelope (n : ℕ) (B : ℝ)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (delta : Fin n → ℝ)
    (hdelta : ∀ i, |delta i| ≤ B) :
    (1 - B) ^ n ≤ ∏ i, (1 + delta i) ∧
      (∏ i, (1 + delta i)) ≤ (1 + B) ^ n := by
  -- PROOF_START
  sorry

end HighamBench
