import HighamBench.P03Definitions

namespace HighamBench

/-- P03-T1: exact one-step residual identity, equation (4.1). -/
theorem p03_t1_one_step_residual_identity
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x d Δx b rHat Δr y : Fin n → ℝ)
    (hres : ∀ i, rHat i = b i - p03MatVec A x i + Δr i)
    (hupdate : ∀ i, y i = x i + d i + Δx i) :
    ∀ i : Fin n,
      p03MatVec A y i - b i =
        Δr i + p03MatVec A d i - rHat i + p03MatVec A Δx i := by
  -- PROOF_START
  sorry

end HighamBench
