import HighamBench.Definitions

namespace HighamBench

open scoped BigOperators

/-- P02-T1: the error-free `VecSum` transformation preserves the exact sum. -/
theorem p02_t1_vecSum_preserves_sum
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  -- PROOF_START
  sorry

end HighamBench
