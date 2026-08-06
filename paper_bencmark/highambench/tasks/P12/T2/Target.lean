import HighamBench.P12Definitions

namespace HighamBench

/-- P12-T2: certificate form of Theorem 2's error-free FastTwoSum transform. -/
theorem p12_t2_fast_two_sum_exact
    (representable : ℝ → Prop) (x y : ℝ) (tr : P12FastTwoSumTrace)
    (hx : representable x)
    (hs : p12Nearest representable (x + y) tr.s)
    (hst : representable (tr.s - x))
    (ht : p12Nearest representable (tr.s - x) tr.t)
    (hye : representable (y - tr.t))
    (he : p12Nearest representable (y - tr.t) tr.e) :
    tr.s + tr.e = x + y ∧ |tr.s - (x + y)| ≤ |y| := by
  -- PROOF_START
  sorry

end HighamBench
