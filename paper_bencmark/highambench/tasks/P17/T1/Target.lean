import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

/-- P17-T1: corrected finite-probability form of Theorem 3.6, with the
nonnegativity conditions required by the paper's induction made explicit. -/
theorem p17_t1_corrected_product_bias_envelope
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17CorrectedProductBiasRun n Ω) :
    (1 - run.B) ^ n ≤ p17ExpectedErrorProduct run ∧
      p17ExpectedErrorProduct run ≤ (1 + run.B) ^ n := by
  -- PROOF_START
  sorry

end HighamBench
