import HighamBench.P04Definitions

namespace HighamBench

/-- P04-T1: Algorithm 3.1's compact perturbation factorization, equation
(3.4), its right-to-left refinement, and its same-precision specialization. -/
theorem p04_t1_chained_rounding_factor
    {n b q : ℕ} (run : P04BlockFmaDotRun n b q) :
    ∃ alpha beta : Fin n → ℝ,
      run.computed = ∑ i : Fin n,
        run.x i * run.y i * (1 + alpha i) * (1 + beta i) ∧
      (∀ i, |alpha i| ≤
        gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q) ∧
      (∀ i, |beta i| ≤ gamma run.uBar n) ∧
      |p04Dot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff
            (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
            run.uBar q n *
          p04AbsDot run.x run.y ∧
      (run.rightToLeft →
        (∀ i, |beta i| ≤ gamma run.uBar (q + b - 1)) ∧
        |p04Dot run.x run.y - run.computed| ≤
          p04BlockFmaCoeff
              (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
              run.uBar q (q + b - 1) *
            p04AbsDot run.x run.y) ∧
      (run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
        (∀ i, alpha i = 0) ∧
        |p04Dot run.x run.y - run.computed| ≤
          gamma run.uBar n * p04AbsDot run.x run.y) := by
  -- PROOF_START
  sorry

end HighamBench
