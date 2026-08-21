import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T3: Theorem 4.5, equations (4.23)--(4.25), uniformly over a
successful UFC or UCF BLR solve family. -/
theorem p15_t3_blr_lu_solve_backward_error {b p r : ℕ}
    (run : P15BLRLinearSolveFamily b p r) :
    let c := p15BLRSolveCost b p r
    let xi := p15BLRXi p run.threshold run.recompression
    let solveScale := fun u epsilon =>
      p15FrobNorm (run.L u epsilon) *
        p15FrobNorm (run.U u epsilon) *
        p15VecNorm (run.xHat u epsilon)
    ∃ matrixError : ℝ → ℝ → P15Matrix (p * b),
      ∃ rhsError : ℝ → ℝ → P15Vector (p * b),
        ∃ rhsRemainder : ℝ → ℝ → ℝ,
          matrixError = (fun u epsilon =>
            p15ComposedMatrixError (run.factorError u epsilon)
              (run.lowerError u epsilon) (run.upperError u epsilon)
              (run.L u epsilon) (run.U u epsilon)) ∧
          rhsError = (fun u epsilon =>
            p15ComposedRhsError (run.lowerRhsError u epsilon)
              (run.upperRhsError u epsilon) (run.L u epsilon)
              (run.lowerError u epsilon)) ∧
          p15IsBigOMixedAtZero run.factorRemainder ∧
          p15IsBigOSquareRelativeAtZero rhsRemainder solveScale ∧
          ∀ u epsilon,
            p15AdmissiblePrecision c u epsilon →
              let gammaP := p15GammaReal (p : ℝ) u
              let gamma3C := p15GammaReal (3 * c) u
              0 ≤ run.factorRemainder u epsilon ∧
              0 ≤ rhsRemainder u epsilon ∧
              p15MatVec (run.A + matrixError u epsilon)
                  (run.xHat u epsilon) =
                run.v + rhsError u epsilon ∧
              p15FrobNorm (matrixError u epsilon) ≤
                (xi * epsilon + gammaP) * p15FrobNorm run.A +
                  gamma3C * p15FrobNorm (run.L u epsilon) *
                    p15FrobNorm (run.U u epsilon) +
                  run.factorRemainder u epsilon ∧
              p15VecNorm (rhsError u epsilon) ≤
                gammaP * (p15VecNorm run.v + solveScale u epsilon) +
                  rhsRemainder u epsilon := by
  -- PROOF_START
  sorry

end HighamBench
