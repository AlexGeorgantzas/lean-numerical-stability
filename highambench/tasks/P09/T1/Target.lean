import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T1: the exact maximum-versus-RMS step used in Theorem 1(b). -/
theorem p09_t1_max_error_le_sqrt_card_mul_rms
    {n : ℕ} (hn : 0 < n) (e : Fin n → ℝ) :
    p09Max e ≤ Real.sqrt (n : ℝ) * p09Rms e := by
  -- PROOF_START
  sorry

end HighamBench
