import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

/-- P14-T1: exact-p14Gamma form of the positive exponential-summation stage
preceding equation (3.3). -/
theorem p14_t1_positive_recursive_sum_relative_error
    (fp : P14StandardAddModel) (n : ℕ) (w : Fin n → ℝ)
    (hvalid : P14GammaValid fp.u (n - 1))
    (hw : ∀ i, 0 ≤ w i)
    (hsum : (∑ i, w i) ≠ 0) :
    |p14RecursiveSum fp.fl_add n w - ∑ i, w i| / |∑ i, w i| ≤
      p14Gamma fp.u (n - 1) := by
  -- PROOF_START
  sorry

end HighamBench
