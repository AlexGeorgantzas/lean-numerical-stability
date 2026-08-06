import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

/-- P01-T2: the pairwise and recursive bounds, and their coefficient comparison. -/
theorem p01_t2_pairwise_vs_recursive_bounds
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u (2 ^ r - 1)) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| ∧
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u (2 ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| ∧
    gamma fp.u r ≤ gamma fp.u (2 ^ r - 1) := by
  -- PROOF_START
  sorry

end HighamBench
