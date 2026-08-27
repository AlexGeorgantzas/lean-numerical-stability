import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

/-- P01-T2: the pairwise and recursive bounds, and their coefficient comparison. -/
theorem p01_t2_pairwise_vs_recursive_bounds
    (fp : P01StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : P01GammaValid fp.u (2 ^ r - 1)) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        p01Gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| ∧
    |p01RecursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        p01Gamma fp.u (2 ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| ∧
    p01Gamma fp.u r ≤ p01Gamma fp.u (2 ^ r - 1) := by
  -- PROOF_START
  sorry

end HighamBench
