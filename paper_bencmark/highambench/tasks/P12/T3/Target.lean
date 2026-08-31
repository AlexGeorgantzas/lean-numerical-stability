import HighamBench.P12Definitions

namespace HighamBench

/-- P12-T3: Lange and Oishi Lemma 4, including the exact intermediate
identities used to establish equation (18). -/
theorem p12_t3_three_product_exact
    (fmt : P12RadixFormat) (x1 x2 x3 : ℝ)
    (tr : P12ThreeProductTrace)
    (run : P12ThreeProductExecution fmt x1 x2 x3 tr) :
    (∃ ra2 : P12Representation fmt tr.a2,
        |tr.a3| ≤
          fmt.condition7Ceiling * fmt.scale ra2.exponent) ∧
      tr.t = tr.s2 - tr.a2 ∧
      tr.r = tr.a3 - tr.t ∧
      tr.s2 + tr.r = tr.a2 + tr.a3 ∧
      tr.s3 = tr.r + tr.a4 ∧
      tr.s1 + tr.s2 + tr.s3 = x1 * x2 * x3 := by
  -- PROOF_START
  sorry

end HighamBench
