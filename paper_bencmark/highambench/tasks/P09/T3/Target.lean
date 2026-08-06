import HighamBench.P09Definitions

namespace HighamBench

open scoped BigOperators

/-- P09-T3: an exact finite-remainder form of Theorem 2(a). The vectors
`term i` are the propagated local errors in the paper's telescoping identity. -/
theorem p09_t3_multidimensional_rms_error_budget
    {m n : ℕ}
    (term : Fin m → Fin n → ℝ) (total : Fin n → ℝ)
    (ε yRms : ℝ) (K remainder : Fin m → ℝ)
    (hdecomp : total = p09VectorSum term)
    (hlocal : ∀ i, p09Rms (term i) ≤ ε * K i * yRms + remainder i) :
    p09Rms total ≤
      ε * (∑ i : Fin m, K i) * yRms + ∑ i : Fin m, remainder i := by
  -- PROOF_START
  sorry

end HighamBench
