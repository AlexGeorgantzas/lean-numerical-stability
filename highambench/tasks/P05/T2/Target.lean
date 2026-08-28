import HighamBench.P05Definitions

namespace HighamBench

/-- P05-T2: Theorem 4.2 and its local estimates (4.3), with zero-based Lean
indices. A completed rectangular Doolittle run yields the general `n*u`
componentwise backward error; in the square case it also yields the rowwise
`i*u` and uniform `(n-1)*u` bounds. -/
theorem p05_t2_lu_backward_error
    {m n : ℕ} (run : P05DoolittleRun m n) :
    (∀ k j, k.val ≤ j.val →
      |run.A (p05RectRow run.rows_ge_columns k) j -
          p05DoolittleThroughPivotDot run.LHat run.UHat
            (p05RectRow run.rows_ge_columns k) j k| ≤
        (k.val : ℝ) * run.format.unitRoundoff *
          p05DoolittleThroughPivotAbsDot run.LHat run.UHat
            (p05RectRow run.rows_ge_columns k) j k) ∧
    (∀ i k, k.val < i.val →
      |run.A i k - p05DoolittleThroughPivotDot run.LHat run.UHat i k k| ≤
        ((k.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05DoolittleThroughPivotAbsDot run.LHat run.UHat i k k) ∧
    ∃ ΔA : Fin m → Fin n → ℝ,
      p05RectMatMul run.LHat run.UHat = run.A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ (n : ℝ) * run.format.unitRoundoff *
          p05RectAbsMatMul run.LHat run.UHat i j) ∧
      (m = n →
        (∀ i j,
          |ΔA i j| ≤ (i.val : ℝ) * run.format.unitRoundoff *
            p05RectAbsMatMul run.LHat run.UHat i j) ∧
        ∀ i j,
          |ΔA i j| ≤ ((n - 1 : ℕ) : ℝ) * run.format.unitRoundoff *
            p05RectAbsMatMul run.LHat run.UHat i j) := by
  -- PROOF_START
  sorry

end HighamBench
