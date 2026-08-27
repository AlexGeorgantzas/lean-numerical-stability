import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T2: Theorem 3.2 and equation (3.6), the componentwise forward-error
bound for mixed-input rectangular matrix multiplication by Algorithm 3.1. -/
theorem p04_t2_mixed_input_product_bound
    {m n t b1 b b2 p q r : ℕ}
    (run : P04MixedInputMatMulRun m n t b1 b b2 p q r) :
    ∀ i j,
      |run.computed i j - p04RectMatMul run.A run.B i j| ≤
        (2 * run.uLow + run.uLow ^ 2 +
            p04BlockFmaCoeff
                (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
                run.uBar q n * (1 + run.uLow) ^ 2) *
          p04AbsRectMatMul run.A run.B i j := by
  -- PROOF_START
  sorry

end HighamBench
