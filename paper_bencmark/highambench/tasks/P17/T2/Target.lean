import HighamBench.P17Definitions

namespace HighamBench

/-- P17-T2: the effective expected suffix-product factors in the recursive
sum turn Theorem 3.6's coefficientwise envelope into Theorem 4.1's relative
summation-bias bound. -/
theorem p17_t2_recursive_sum_bias_condition_bound {n : ℕ}
    (a factor : Fin n → ℝ) (gamma : ℝ)
    (hsum : p17ExactSum a ≠ 0)
    (hfactor : ∀ i, |factor i - 1| ≤ gamma) :
    |p17EffectiveExpectedSum a factor - p17ExactSum a| /
        |p17ExactSum a| ≤
      gamma * p17SummationCondition a := by
  -- PROOF_START
  sorry

end HighamBench
