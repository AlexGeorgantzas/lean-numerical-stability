import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T3: Theorem 4.5, equations (4.23)--(4.25), derived for one completed
UFC or UCF factorization followed by the two ordered block triangular solves. -/
theorem p15_t3_blr_lu_solve_backward_error {b p r : ℕ}
    (run : P15BLRLinearSolveExecution b p r) :
    let c := p15BLRSolveCost b p r
    let gammaP := p15GammaReal (p : ℝ) run.unitRoundoff
    let gamma3C := p15GammaReal (3 * c) run.unitRoundoff
    let xi := p15BLRXi p run.threshold run.recompression
    let solveScale :=
      p15FrobNorm run.L * p15FrobNorm run.U * p15VecNorm run.xHat
    ∃ factor : P15FactorizationBackwardError r run.threshold
        run.recompression run.unitRoundoff run.epsilon run.A run.L run.U,
      ∃ lower : P15TriangularSolveBackwardError r .lower
          run.unitRoundoff run.L run.v run.yHat,
        ∃ upper : P15TriangularSolveBackwardError r .upper
            run.unitRoundoff run.U run.yHat run.xHat,
          ∃ matrixError : P15Matrix (p * b),
            ∃ rhsError : P15Vector (p * b),
              ∃ rhsRemainder : ℝ → ℝ → ℝ,
                matrixError =
                    p15ComposedMatrixError factor.error lower.matrixError
                      upper.matrixError run.L run.U ∧
                  rhsError =
                    p15ComposedRhsError lower.rhsError upper.rhsError
                      run.L lower.matrixError ∧
                  p15IsBigOMixedAtRun factor.remainder
                    run.unitRoundoff run.epsilon ∧
                  p15IsBigOSquareRelativeAtRun rhsRemainder
                    (fun _ _ => solveScale) run.unitRoundoff run.epsilon ∧
                  p15MatVec (run.A + matrixError) run.xHat =
                    run.v + rhsError ∧
                  p15FrobNorm matrixError ≤
                    (xi * run.epsilon + gammaP) * p15FrobNorm run.A +
                      gamma3C * p15FrobNorm run.L * p15FrobNorm run.U +
                      factor.remainder run.unitRoundoff run.epsilon ∧
                  p15VecNorm rhsError ≤
                    gammaP * (p15VecNorm run.v + solveScale) +
                      rhsRemainder run.unitRoundoff run.epsilon := by
  -- PROOF_START
  sorry

end HighamBench
