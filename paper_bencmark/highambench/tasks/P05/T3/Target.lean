import HighamBench.P05Definitions

namespace HighamBench

/-- P05-T3: Theorem 4.4's symmetry step. The local Cholesky estimates on the
computed upper triangle extend to the full `diag((i+1)u)` componentwise bound
and hence to the uniform `(n+1)u` bound. Indices are zero-based in Lean. -/
theorem p05_t3_cholesky_backward_error
    {n : ℕ} (u : ℝ)
    (A R : Fin n → Fin n → ℝ)
    (hu : 0 ≤ u)
    (hA_symm : ∀ i j, A i j = A j i)
    (hupper : ∀ i j, i.val ≤ j.val →
      |p05MatMul (p05Transpose R) R i j - A i j| ≤
        ((i.val + 2 : ℕ) : ℝ) * u *
          p05AbsMatMul (p05Transpose R) R i j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      p05MatMul (p05Transpose R) R = A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) * u *
          p05AbsMatMul (p05Transpose R) R i j) ∧
      ∀ i j,
        |ΔA i j| ≤ ((n + 1 : ℕ) : ℝ) * u *
          p05AbsMatMul (p05Transpose R) R i j := by
  -- PROOF_START
  sorry

end HighamBench
