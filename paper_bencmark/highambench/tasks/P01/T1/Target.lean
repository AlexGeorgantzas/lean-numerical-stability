import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

/-- P01-T1: pairwise summation bound for nonnegative inputs. -/
theorem p01_t1_pairwise_nonnegative
    (fp : P01StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : P01GammaValid fp.u r)
    (hv : ∀ i, 0 ≤ v i) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      p01Gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  -- PROOF_START
  sorry

end HighamBench
