import HighamBench.P17Definitions

namespace HighamBench

/-- P17-T2: Theorem 4.1's relative bias bound for a left-to-right recursive
sum computed with limited-precision stochastic rounding `SR_{p,r}`. Here
`m + 1` is the paper's input count `n`, so `m` is the number of rounded
additions. -/
theorem p17_t2_recursive_sum_bias_condition_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω)
    (hsum : p17ExactSum run.a ≠ 0) :
    |p17ExpectedRecursiveSum run - p17ExactSum run.a| /
        |p17ExactSum run.a| ≤
      p17SummationCondition run.a *
        p17Gamma m (p17UnitRoundoff (run.p + run.r)) := by
  -- PROOF_START
  sorry

end HighamBench
