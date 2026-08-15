import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T3: the complete finite execution form of Theorem 4.5, equations
(4.23)--(4.25), for a completed UFC or UCF BLR solve. -/
theorem p15_t3_blr_lu_solve_backward_error {b p r : ℕ}
    (run : P15BLRLinearSolveExecution b p r) :
    let c := p15BLRSolveCost b p r
    let gammaP := p15GammaReal (p : ℝ) run.unitRoundoff
    let gammaC := p15GammaReal c run.unitRoundoff
    let gamma3C := p15GammaReal (3 * c) run.unitRoundoff
    let xi := p15BLRXi p run.threshold run.recompression
    let matrixError :=
      p15ComposedMatrixError run.factorError run.lowerError run.upperError
        run.L run.U
    let rhsError :=
      p15ComposedRhsError run.lowerRhsError run.upperRhsError
        run.L run.lowerError
    let solveScale :=
      p15FrobNorm run.L * p15FrobNorm run.U * p15VecNorm run.xHat
    let rhsFiniteCoefficient :=
      gammaP * (1 + gammaC) ^ 2 / (1 - gammaP)
    let rhsHigherOrderCoefficient := rhsFiniteCoefficient - gammaP
    p15MatVec (run.A + matrixError) run.xHat = run.v + rhsError ∧
    p15FrobNorm matrixError ≤
      (xi * run.epsilon + gammaP) * p15FrobNorm run.A +
        (3 * gammaC + gammaC ^ 2) *
          p15FrobNorm run.L * p15FrobNorm run.U +
        run.factorMixedConstant * run.unitRoundoff * run.epsilon ∧
    p15FrobNorm matrixError ≤
      (xi * run.epsilon + gammaP) * p15FrobNorm run.A +
        gamma3C * p15FrobNorm run.L * p15FrobNorm run.U +
        run.factorMixedConstant * run.unitRoundoff * run.epsilon ∧
    p15VecNorm rhsError ≤
      gammaP * p15VecNorm run.v + rhsFiniteCoefficient * solveScale ∧
    p15VecNorm rhsError ≤
      gammaP * (p15VecNorm run.v + solveScale) +
        rhsHigherOrderCoefficient * solveScale ∧
    p15VecNorm rhsError ≤
      gammaP * (p15VecNorm run.v + solveScale) +
        16 * c ^ 2 * run.unitRoundoff ^ 2 * solveScale ∧
    0 ≤ rhsHigherOrderCoefficient ∧
      rhsHigherOrderCoefficient ≤ 16 * c ^ 2 * run.unitRoundoff ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
