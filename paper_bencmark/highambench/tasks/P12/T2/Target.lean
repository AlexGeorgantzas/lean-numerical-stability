import HighamBench.P12Definitions

namespace HighamBench

/-- P12-T2: Lange and Oishi Theorem 2 for the original FastTwoSum algorithm. -/
theorem p12_t2_fast_two_sum_exact
    (fmt : P12RadixFormat) (x y : ℝ) (tr : P12FastTwoSumTrace)
    (hx : p12Representable fmt x) (hy : p12Representable fmt y)
    (hcondition7 : ∃ rx : P12Representation fmt x,
      |y| ≤
        (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale rx.exponent)
    (run : P12FastTwoSumExecution fmt x y tr) :
    tr.t = tr.s - x ∧
      tr.e = y - tr.t ∧
      tr.s + tr.e = x + y ∧
      |tr.s - (x + y)| ≤ |y| := by
  -- PROOF_START
  sorry

end HighamBench
