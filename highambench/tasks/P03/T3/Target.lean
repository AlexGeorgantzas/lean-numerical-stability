import HighamBench.P03Definitions

namespace HighamBench

/-- P03-T3: the exact componentwise Algorithm 1.1 recurrence in Theorem 5.1. -/
theorem p03_t3_componentwise_residual_recurrence
    {n : ℕ} (run : P03ComponentwiseIRRun n) (i : ℕ) :
    ∀ j : Fin n,
      |p03ComponentwiseExactResidual run (i + 1) j| ≤
        p03MatVec (p03W run i)
            (p03VecAbs (p03ComponentwiseExactResidual run i)) j +
          p03Y run i j := by
  -- PROOF_START
  sorry

end HighamBench
