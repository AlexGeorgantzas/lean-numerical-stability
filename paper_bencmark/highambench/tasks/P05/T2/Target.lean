import HighamBench.P05Definitions

namespace HighamBench

/-- P05-T2: the square-case sharpening in Theorem 4.2. Local Doolittle
residuals with zero-based row coefficient `i` assemble into one perturbation,
and every row coefficient is at most `n-1`. -/
theorem p05_t2_square_lu_backward_error
    {n : ℕ} (u : ℝ)
    (A L U : Fin n → Fin n → ℝ)
    (hu : 0 ≤ u)
    (hlocal : ∀ i j,
      |p05MatMul L U i j - A i j| ≤
        (i.val : ℝ) * u * p05AbsMatMul L U i j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      p05MatMul L U = A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ (i.val : ℝ) * u * p05AbsMatMul L U i j) ∧
      ∀ i j,
        |ΔA i j| ≤ ((n - 1 : ℕ) : ℝ) * u * p05AbsMatMul L U i j := by
  -- PROOF_START
  sorry

end HighamBench
