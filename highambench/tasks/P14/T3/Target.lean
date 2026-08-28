import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

/-- P14-T3: shift invariance (1.4) together with the exact normalization and
absolute-mass identities of the softmax vector. -/
theorem p14_t3_softmax_shift_and_normalization {n : ℕ}
    (x : Fin n → ℝ) (a : ℝ) (j : Fin n) :
    p14Softmax (fun i => x i - a) j = p14Softmax x j ∧
      (∑ i, p14Softmax x i) = 1 ∧
      (∑ i, |p14Softmax x i|) = 1 := by
  -- PROOF_START
  sorry

end HighamBench
