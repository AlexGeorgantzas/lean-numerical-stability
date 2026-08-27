import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

/-- P01-T3: Higham (1993), equations (5.2)--(5.3). -/
theorem p01_t3_noGuard_recursive_running_error_bound
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ) :
    |p01RecursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      fp.u * noGuardRecursiveRunningBudget fp n v := by
  -- PROOF_START
  sorry

end HighamBench
