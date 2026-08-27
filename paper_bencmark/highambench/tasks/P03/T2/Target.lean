import HighamBench.P03Definitions

namespace HighamBench

/-- P03-T2: the exact normwise residual recurrence in Theorem 4.1. -/
theorem p03_t2_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i := by
  -- PROOF_START
  sorry

end HighamBench
