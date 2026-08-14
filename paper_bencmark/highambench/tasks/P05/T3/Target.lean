import HighamBench.P05Definitions

namespace HighamBench

/-- P05-T3: Theorem 4.4 and the local conventional-Cholesky estimates (4.5),
with zero-based Lean indices. -/
theorem p05_t3_cholesky_backward_error
    {n : ℕ} (run : P05CholeskyRun n) :
    (∀ i j, i.val < j.val →
      |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat i j) ∧
    (∀ j,
      |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
        ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat j j) ∧
    ∃ ΔA : Fin n → Fin n → ℝ,
      p05MatMul (p05Transpose run.RHat) run.RHat = run.A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j) ∧
      ∀ i j,
        |ΔA i j| ≤ ((n + 1 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j := by
  -- PROOF_START
  sorry

end HighamBench
