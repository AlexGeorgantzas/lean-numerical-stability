import HighamBench.P10Definitions

open scoped BigOperators

namespace HighamBench

/-- P10-T3: finite unrolling certificate for the recursive Sylvester error bound (20). -/
theorem p10_t3_recursive_sylvester_error_unroll {n depth : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ)
    (hsep : 0 < sep) (err : ℕ → ℝ)
    (hstep : ∀ k, k < depth →
      err (k + 1) ≤
        p10SylvesterGrowth A B sep * err k +
          p10SylvesterForcing A B C R sep epsilon mu) :
    err depth ≤
      (p10SylvesterGrowth A B sep) ^ depth * err 0 +
        p10SylvesterForcing A B C R sep epsilon mu *
          (∑ k ∈ Finset.range depth, (p10SylvesterGrowth A B sep) ^ k) := by
  -- PROOF_START
  sorry

end HighamBench
