import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T3: Theorem 4.4's exact perturbation assembly for a block-FMA LU
factorization followed by two triangular solves, together with its displayed
`cFact + 2*gamma_n + gamma_n^2` componentwise coefficient. -/
theorem p04_t3_block_lu_solve_backward_error
    {N : ℕ} (uLow uFma u : ℝ) (q n bdim : ℕ)
    (A L U ΔF ΔL ΔU M : Fin N → Fin N → ℝ)
    (x y rhs : Fin N → ℝ)
    (hfact : p04MatMul L U = A + ΔF)
    (hforward : p04MatVec (L + ΔL) y = rhs)
    (hbackward : p04MatVec (U + ΔU) x = y)
    (hΔF : ∀ i j,
      |ΔF i j| ≤ p04FactorizationCoeff uLow uFma u q n bdim * M i j)
    (hLΔU : ∀ i j,
      |p04MatMul L ΔU i j| ≤ gamma u n * M i j)
    (hΔLU : ∀ i j,
      |p04MatMul ΔL U i j| ≤ gamma u n * M i j)
    (hΔLΔU : ∀ i j,
      |p04MatMul ΔL ΔU i j| ≤ (gamma u n) ^ 2 * M i j) :
    ∃ ΔA : Fin N → Fin N → ℝ,
      p04MatVec (A + ΔA) x = rhs ∧
      ∀ i j,
        |ΔA i j| ≤
          (p04FactorizationCoeff uLow uFma u q n bdim +
              2 * gamma u n + (gamma u n) ^ 2) * M i j := by
  -- PROOF_START
  sorry

end HighamBench
