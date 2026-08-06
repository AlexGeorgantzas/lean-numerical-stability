import HighamBench.P11Definitions

namespace HighamBench

/-- P11-T1: the first-column residual-action estimate in equation (16). -/
theorem p11_t1_first_column_residual_action {n : ℕ}
    (G : P11Matrix n) (a : Fin n → ℝ) (epsilon : ℝ)
    (hG : p11FrobNorm G ≤ epsilon) :
    p11VecNorm (p11MatVec G a) ≤ epsilon * p11VecNorm a := by
  -- PROOF_START
  sorry

end HighamBench
