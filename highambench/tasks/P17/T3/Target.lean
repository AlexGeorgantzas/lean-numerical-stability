import HighamBench.P17Definitions

namespace HighamBench

/-- P17-T3: Theorem 4.3's variance-based relative forward-error bound for
left-to-right recursive summation under limited-precision stochastic rounding
`SR_{p,r}`. Lean uses `m = n - 1` rounded additions. -/
theorem p17_t3_variance_plus_bias_probability_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω)
    (hsum : p17ExactSum run.a ≠ 0)
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (hlambda_lt_one : lambda < 1) :
    1 - lambda ≤
      p17EventProb run.probability {ω |
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
            p17ExactSum run.a| / |p17ExactSum run.a| ≤
          p17SummationCondition run.a *
            (Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
              p17Gamma m
                  (p17UnitRoundoff run.p +
                    p17UnitRoundoff (run.p + run.r)) -
                p17Gamma m (p17UnitRoundoff run.p))} := by
  -- PROOF_START
  sorry

end HighamBench
