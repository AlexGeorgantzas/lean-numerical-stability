import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T3: Theorem 4.4's exact perturbation assembly for a block-FMA LU
factorization from Algorithm 4.1 followed by two triangular solves, with the
mandatory `|A| + |Lhat||Uhat|` scale and every term of equation (4.7). -/
theorem p04_t3_block_lu_solve_backward_error
    {n b q : ℕ} (run : P04BlockLUSolveRun n b q) :
    ∃ deltaA : Fin n → Fin n → ℝ,
      p04MatVec (run.A + deltaA) run.xHat = run.rhs ∧
      ∀ i j,
        |deltaA i j| ≤
          (p04FactorizationCoeff
              run.uLow run.uBar run.uFma run.uWork q n b +
              2 * gamma run.uWork n + (gamma run.uWork n) ^ 2) *
            p04LUSolveScale run.A run.LHat run.UHat i j := by
  -- PROOF_START
  sorry

end HighamBench
