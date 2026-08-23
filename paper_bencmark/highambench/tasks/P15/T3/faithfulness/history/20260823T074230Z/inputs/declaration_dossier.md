# Declaration dossier for P15-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
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
                      rhsRemainder run.unitRoundoff run.epsilon
```

## Elaborated target type

```lean
∀ {b p r : Nat} (run : HighamBench.P15BLRLinearSolveExecution b p r),
  have c := HighamBench.p15BLRSolveCost b p r;
  have gammaP := HighamBench.p15GammaReal p.cast run.unitRoundoff;
  have gamma3C := HighamBench.p15GammaReal (instHMul.hMul 3 c) run.unitRoundoff;
  have xi := HighamBench.p15BLRXi p run.threshold run.recompression;
  have solveScale :=
    instHMul.hMul (instHMul.hMul (HighamBench.p15FrobNorm run.L) (HighamBench.p15FrobNorm run.U))
      (HighamBench.p15VecNorm run.xHat);
  Exists fun factor =>
    Exists fun lower =>
      Exists fun upper =>
        Exists fun matrixError =>
          Exists fun rhsError =>
            Exists fun rhsRemainder =>
              And
                (Eq matrixError
                  (HighamBench.p15ComposedMatrixError factor.error lower.matrixError upper.matrixError run.L run.U))
                (And
                  (Eq rhsError (HighamBench.p15ComposedRhsError lower.rhsError upper.rhsError run.L lower.matrixError))
                  (And (HighamBench.p15IsBigOMixedAtRun factor.remainder run.unitRoundoff run.epsilon)
                    (And
                      (HighamBench.p15IsBigOSquareRelativeAtRun rhsRemainder (fun x x_1 => solveScale) run.unitRoundoff
                        run.epsilon)
                      (And
                        (Eq (HighamBench.p15MatVec (instHAdd.hAdd run.A matrixError) run.xHat)
                          (instHAdd.hAdd run.v rhsError))
                        (And
                          (Real.instLE.le (HighamBench.p15FrobNorm matrixError)
                            (instHAdd.hAdd
                              (instHAdd.hAdd
                                (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi run.epsilon) gammaP)
                                  (HighamBench.p15FrobNorm run.A))
                                (instHMul.hMul (instHMul.hMul gamma3C (HighamBench.p15FrobNorm run.L))
                                  (HighamBench.p15FrobNorm run.U)))
                              (factor.remainder run.unitRoundoff run.epsilon)))
                          (Real.instLE.le (HighamBench.p15VecNorm rhsError)
                            (instHAdd.hAdd
                              (instHMul.hMul gammaP (instHAdd.hAdd (HighamBench.p15VecNorm run.v) solveScale))
                              (rhsRemainder run.unitRoundoff run.epsilon))))))))
```

## Fully explicit elaborated target type

```lean
∀ {b p r : Nat} (run : HighamBench.P15BLRLinearSolveExecution b p r),
  have c : Real := HighamBench.p15BLRSolveCost b p r;
  have gammaP : Real :=
    HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p)
      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run);
  have gamma3C : Real :=
    HighamBench.p15GammaReal
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        c)
      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run);
  have xi : Real :=
    HighamBench.p15BLRXi p (@HighamBench.P15BLRLinearSolveExecution.threshold b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.recompression b p r run);
  have solveScale : Real :=
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@HighamBench.P15BLRLinearSolveExecution.L b p r run))
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@HighamBench.P15BLRLinearSolveExecution.U b p r run)))
      (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
        (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run));
  @Exists.{1}
    (@HighamBench.P15FactorizationBackwardError b p r (@HighamBench.P15BLRLinearSolveExecution.threshold b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.recompression b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run) (@HighamBench.P15BLRLinearSolveExecution.A b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.L b p r run) (@HighamBench.P15BLRLinearSolveExecution.U b p r run))
    fun
      (factor :
        @HighamBench.P15FactorizationBackwardError b p r (@HighamBench.P15BLRLinearSolveExecution.threshold b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.recompression b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.A b p r run) (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.U b p r run)) =>
    @Exists.{1}
      (@HighamBench.P15TriangularSolveBackwardError p b r HighamBench.P15TriangularSolveDirection.lower
        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
        (@HighamBench.P15BLRLinearSolveExecution.L b p r run) (@HighamBench.P15BLRLinearSolveExecution.v b p r run)
        (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run))
      fun
        (lower :
          @HighamBench.P15TriangularSolveBackwardError p b r HighamBench.P15TriangularSolveDirection.lower
            (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
            (@HighamBench.P15BLRLinearSolveExecution.L b p r run) (@HighamBench.P15BLRLinearSolveExecution.v b p r run)
            (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run)) =>
      @Exists.{1}
        (@HighamBench.P15TriangularSolveBackwardError p b r HighamBench.P15TriangularSolveDirection.upper
          (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.U b p r run) (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run)
          (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run))
        fun
          (upper :
            @HighamBench.P15TriangularSolveBackwardError p b r HighamBench.P15TriangularSolveDirection.upper
              (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
              (@HighamBench.P15BLRLinearSolveExecution.U b p r run)
              (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run)
              (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run)) =>
        @Exists.{1} (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
          fun
            (matrixError :
              HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
          @Exists.{1} (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
            fun
              (rhsError :
                HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
            @Exists.{1} (Real → Real → Real) fun (rhsRemainder : Real → Real → Real) =>
              And
                (@Eq.{1} (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                  matrixError
                  (@HighamBench.p15ComposedMatrixError
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                    (@HighamBench.P15FactorizationBackwardError.error b p r
                      (@HighamBench.P15BLRLinearSolveExecution.threshold b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.recompression b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.A b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.U b p r run) factor)
                    (@HighamBench.P15TriangularSolveBackwardError.matrixError p b r
                      HighamBench.P15TriangularSolveDirection.lower
                      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.v b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run) lower)
                    (@HighamBench.P15TriangularSolveBackwardError.matrixError p b r
                      HighamBench.P15TriangularSolveDirection.upper
                      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.U b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run) upper)
                    (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                    (@HighamBench.P15BLRLinearSolveExecution.U b p r run)))
                (And
                  (@Eq.{1} (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                    rhsError
                    (@HighamBench.p15ComposedRhsError
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                      (@HighamBench.P15TriangularSolveBackwardError.rhsError p b r
                        HighamBench.P15TriangularSolveDirection.lower
                        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.v b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run) lower)
                      (@HighamBench.P15TriangularSolveBackwardError.rhsError p b r
                        HighamBench.P15TriangularSolveDirection.upper
                        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.U b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run) upper)
                      (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                      (@HighamBench.P15TriangularSolveBackwardError.matrixError p b r
                        HighamBench.P15TriangularSolveDirection.lower
                        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.v b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.yHat b p r run) lower)))
                  (And
                    (HighamBench.p15IsBigOMixedAtRun
                      (@HighamBench.P15FactorizationBackwardError.remainder b p r
                        (@HighamBench.P15BLRLinearSolveExecution.threshold b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.recompression b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.A b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.U b p r run) factor)
                      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                      (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))
                    (And
                      (HighamBench.p15IsBigOSquareRelativeAtRun rhsRemainder (fun (x x_1 : Real) => solveScale)
                        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                        (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))
                      (And
                        (@Eq.{1}
                          (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@HighamBench.p15MatVec (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                            (@HAdd.hAdd.{0, 0, 0}
                              (HighamBench.P15Matrix
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (HighamBench.P15Matrix
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (HighamBench.P15Matrix
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (@instHAdd.{0}
                                (HighamBench.P15Matrix
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                (@Matrix.add.{0, 0, 0}
                                  (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                  (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                                  Real.instAdd))
                              (@HighamBench.P15BLRLinearSolveExecution.A b p r run) matrixError)
                            (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run))
                          (@HAdd.hAdd.{0, 0, 0}
                            (HighamBench.P15Vector
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (HighamBench.P15Vector
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (HighamBench.P15Vector
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (@instHAdd.{0}
                              (HighamBench.P15Vector
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (@Pi.instAdd.{0, 0}
                                (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                (fun (a : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                                  Real)
                                fun (i : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                                Real.instAdd))
                            (@HighamBench.P15BLRLinearSolveExecution.v b p r run) rhsError))
                        (And
                          (@LE.le.{0} Real Real.instLE
                            (@HighamBench.p15FrobNorm
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) matrixError)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi
                                      (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))
                                    gammaP)
                                  (@HighamBench.p15FrobNorm
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                    (@HighamBench.P15BLRLinearSolveExecution.A b p r run)))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gamma3C
                                    (@HighamBench.p15FrobNorm
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                      (@HighamBench.P15BLRLinearSolveExecution.L b p r run)))
                                  (@HighamBench.p15FrobNorm
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                    (@HighamBench.P15BLRLinearSolveExecution.U b p r run))))
                              (@HighamBench.P15FactorizationBackwardError.remainder b p r
                                (@HighamBench.P15BLRLinearSolveExecution.threshold b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.recompression b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.A b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.U b p r run) factor
                                (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))))
                          (@LE.le.{0} Real Real.instLE
                            (@HighamBench.p15VecNorm
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) rhsError)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HighamBench.p15VecNorm
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                    (@HighamBench.P15BLRLinearSolveExecution.v b p r run))
                                  solveScale))
                              (rhsRemainder (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                                (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run)))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P15Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P15Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P15BLRLinearSolveExecution`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `48c46a478eff0fa22f0898ad08185950e64ed035455b313237ed0de36e6ce742`

Type:

```lean
Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(b p r : Nat) → Type
```

### D002: `HighamBench.P15BLRLinearSolveExecution.A`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4faf24f64a56296b99377806a186ba87857ca1c06ce54cd4110fde3419f5cf11`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveExecution b p r) →
    HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.7
```

### D003: `HighamBench.P15BLRLinearSolveExecution.L`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `dd1bb5831e63b5325a0a0fd68a380122fd9bc54824c1a10da5dda9f098ce01ae`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveExecution b p r) →
    HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.9
```

### D004: `HighamBench.P15BLRLinearSolveExecution.U`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bfb02ddb14a49b2eecf6522f2756e6d7c9fb989dbb530746e1d922cf0a5bf210`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveExecution b p r) →
    HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.10
```

### D005: `HighamBench.P15BLRLinearSolveExecution.epsilon`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f4eee8e255cd7780044fcfedef79478296d5d53cec840c6ebcf4ccf63d499b23`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → Real
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveExecution b p r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.15
```

### D006: `HighamBench.P15BLRLinearSolveExecution.recompression`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e7f1b55868e45e12b0d6c040ff1ec13a5cfbf49d154d6a3977c3263be2ba9be7`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15BLRRecompression
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveExecution b p r) → HighamBench.P15BLRRecompression
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.6
```

### D007: `HighamBench.P15BLRLinearSolveExecution.threshold`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b2081b192b5bec9d5c1c2d74651461f29c272f0a650849e68edfb770160ff00f`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15BLRThreshold
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveExecution b p r) → HighamBench.P15BLRThreshold
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.5
```

### D008: `HighamBench.P15BLRLinearSolveExecution.unitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bc26714304c3ad22cc758e91dddfa3e38c62a45a7633594f4e9248dad85dd665`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → Real
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveExecution b p r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.14
```

### D009: `HighamBench.P15BLRLinearSolveExecution.v`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `00f246fb21beb0a4eda222b738f2836a34ea1b7bb1b45e9f25b02b46a676ffc1`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveExecution b p r) →
    HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.11
```

### D010: `HighamBench.P15BLRLinearSolveExecution.xHat`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9c50fb0ae5c74f9edf68d152b71b37707e8f398a9bffb607240e598a54ceda18`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveExecution b p r) →
    HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.13
```

### D011: `HighamBench.P15BLRLinearSolveExecution.yHat`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1201727d6be0b699f134b9d5011bc0933c4f28e7be805627fbba65adeafd400a`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveExecution b p r → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveExecution b p r) →
    HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.12
```

### D012: `HighamBench.P15FactorizationBackwardError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `29540236a99a51e28a07c05d1e8c644bc289246e3d6594216df46cdb4a063d8f`

Type:

```lean
{b p : Nat} →
  Nat →
    HighamBench.P15BLRThreshold →
      HighamBench.P15BLRRecompression →
        Real →
          Real →
            HighamBench.P15Matrix (instHMul.hMul p b) →
              HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{b p : Nat} →
  (r : Nat) →
    (threshold : HighamBench.P15BLRThreshold) →
      (recompression : HighamBench.P15BLRRecompression) →
        (u epsilon : Real) →
          (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D013: `HighamBench.P15FactorizationBackwardError.error`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `51713d1e185fd5bd6d37326cd7a2cc35e49fb49a72f397beb8510df20624eb9f`

Type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (instHMul.hMul p b)} →
          HighamBench.P15FactorizationBackwardError r threshold recompression u epsilon A L U →
            HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (self : @HighamBench.P15FactorizationBackwardError b p r threshold recompression u epsilon A L U) →
            HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r threshold recompression u epsilon A L U self => self.1
```

### D014: `HighamBench.P15FactorizationBackwardError.remainder`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `45bbfad18b6a707e22d4f92995eeb68ffbfd28402392b9bdaec6b9f4eb2faead`

Type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (instHMul.hMul p b)} →
          HighamBench.P15FactorizationBackwardError r threshold recompression u epsilon A L U → Real → Real → Real
```

Fully explicit type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (self : @HighamBench.P15FactorizationBackwardError b p r threshold recompression u epsilon A L U) →
            Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r threshold recompression u epsilon A L U self => self.2
```

### D015: `HighamBench.P15Matrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `869888198c7e16028812ecb8af419ae2eacf78a03074fe8308f98d5758ed7656`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D016: `HighamBench.P15TriangularSolveBackwardError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f8de43b84e486344112ceab5018166dbcef9539ab431ee0e2a96439bf38d4d38`

Type:

```lean
{p b : Nat} →
  Nat →
    HighamBench.P15TriangularSolveDirection →
      Real →
        HighamBench.P15Matrix (instHMul.hMul p b) →
          HighamBench.P15Vector (instHMul.hMul p b) → HighamBench.P15Vector (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (direction : HighamBench.P15TriangularSolveDirection) →
      (u : Real) →
        (T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
          (rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D017: `HighamBench.P15TriangularSolveBackwardError.matrixError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5ad9d8c57258a4f49109ef282c32eb1aa7cc58dcb25c2737ca87d5d6f80645f4`

Type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (instHMul.hMul p b)} →
        {rhs x : HighamBench.P15Vector (instHMul.hMul p b)} →
          HighamBench.P15TriangularSolveBackwardError r direction u T rhs x → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
        {rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (self : @HighamBench.P15TriangularSolveBackwardError p b r direction u T rhs x) →
            HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun p b r direction u T rhs x self => self.1
```

### D018: `HighamBench.P15TriangularSolveBackwardError.rhsError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9b74ae70391cb70072e3a0078f9ba238fa3e2d45e2165b325bb862769c631c4e`

Type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (instHMul.hMul p b)} →
        {rhs x : HighamBench.P15Vector (instHMul.hMul p b)} →
          HighamBench.P15TriangularSolveBackwardError r direction u T rhs x → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
        {rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (self : @HighamBench.P15TriangularSolveBackwardError p b r direction u T rhs x) →
            HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun p b r direction u T rhs x self => self.2
```

### D019: `HighamBench.P15TriangularSolveDirection.lower`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `1`
- Semantic SHA-256: `ed7c8315fcb03c4458bf042d8e255dbdd43a81b2256e12ed8cedcaa4b4901e2b`

Type:

```lean
HighamBench.P15TriangularSolveDirection
```

Fully explicit type:

```lean
HighamBench.P15TriangularSolveDirection
```

### D020: `HighamBench.P15TriangularSolveDirection.upper`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `1`
- Semantic SHA-256: `e6d13e0fa0da3a432d462199fc5932439303d796406010f67483ae2716235cb0`

Type:

```lean
HighamBench.P15TriangularSolveDirection
```

Fully explicit type:

```lean
HighamBench.P15TriangularSolveDirection
```

### D021: `HighamBench.P15Vector`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `15e7e37c5731d7df61fbacb22e39e6f80678f5f9880fecbb579e57644d05505c`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D022: `HighamBench.p15BLRSolveCost`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e7760f878caa60b3dc61c72221f5221bd67e85cb18d96a0f3d138f5c6026151e`

Type:

```lean
Nat → Nat → Nat → Real
```

Fully explicit type:

```lean
(b p r : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r => instHAdd.hAdd (instHAdd.hAdd b.cast (instHMul.hMul (instHMul.hMul 2 r.cast) r.cast.sqrt)) p.cast
```

### D023: `HighamBench.p15BLRXi`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `65929a6bf33f8b7c99b156c0f9eb0b7289d5220cbf07cd19e2c7a5f7aa28c95d`

Type:

```lean
Nat → HighamBench.P15BLRThreshold → HighamBench.P15BLRRecompression → Real
```

Fully explicit type:

```lean
(p : Nat) → (threshold : HighamBench.P15BLRThreshold) → (recompression : HighamBench.P15BLRRecompression) → Real
```

Definition body (one-level semantic boundary):

```lean
fun p threshold recompression =>
  HighamBench.p15BLRXi.match_1 (fun recompression threshold => Real) recompression threshold (fun _ => 1)
    (fun _ => p.cast) (fun _ => p.cast) fun _ => instHDiv.hDiv (instHPow.hPow p.cast 2) (Real.sqrt 6)
```

### D024: `HighamBench.p15ComposedMatrixError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7fea7f458b67ea6c52b1dbb4c20be145a0a762071dd49829d699a2b06da7bfd2`

Type:

```lean
{n : Nat} →
  HighamBench.P15Matrix n →
    HighamBench.P15Matrix n →
      HighamBench.P15Matrix n → HighamBench.P15Matrix n → HighamBench.P15Matrix n → HighamBench.P15Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (factorError lowerError upperError L U : HighamBench.P15Matrix n) → HighamBench.P15Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} factorError lowerError upperError L U =>
  instHAdd.hAdd
    (instHAdd.hAdd (instHAdd.hAdd factorError (HighamBench.p15MatMul lowerError U))
      (HighamBench.p15MatMul L upperError))
    (HighamBench.p15MatMul lowerError upperError)
```

### D025: `HighamBench.p15ComposedRhsError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `af0b640c8d0046428cf87fce5a7328baeb6b0ab688f048dbfbae91dcef566e77`

Type:

```lean
{n : Nat} →
  HighamBench.P15Vector n →
    HighamBench.P15Vector n → HighamBench.P15Matrix n → HighamBench.P15Matrix n → HighamBench.P15Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  (rhsLower rhsUpper : HighamBench.P15Vector n) → (L lowerError : HighamBench.P15Matrix n) → HighamBench.P15Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} rhsLower rhsUpper L lowerError =>
  instHAdd.hAdd (instHAdd.hAdd rhsLower (HighamBench.p15MatVec L rhsUpper)) (HighamBench.p15MatVec lowerError rhsUpper)
```

### D026: `HighamBench.p15FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837bd1b4fd433e90b49e653f1245c95156c8bd043250d89a7117737646408c28`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P15Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => HighamBench.p15RectFrobNorm A
```

### D027: `HighamBench.p15GammaReal`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `271296c936d7dd54bb763543aed321ddd01215dbcf43ad0f046996eedec71821`

Type:

```lean
Real → Real → Real
```

Fully explicit type:

```lean
(k u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun k u => instHDiv.hDiv (instHMul.hMul k u) (instHSub.hSub 1 (instHMul.hMul k u))
```

### D028: `HighamBench.p15IsBigOMixedAtRun`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1a22b98c021c672a2ed9caa18686e56b5b7aca6336752e03b6722087f4e8de70`

Type:

```lean
(Real → Real → Real) → Real → Real → Prop
```

Fully explicit type:

```lean
(remainder : Real → Real → Real) → (unitRoundoff epsilon : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder unitRoundoff epsilon =>
  Exists fun C =>
    Exists fun deltaU =>
      Exists fun deltaEpsilon =>
        And (Real.instLE.le 0 C)
          (And (Real.instLT.lt 0 deltaU)
            (And (Real.instLT.lt 0 deltaEpsilon)
              (And (Real.instLE.le unitRoundoff deltaU)
                (And (Real.instLE.le epsilon deltaEpsilon)
                  (∀ (u epsilon' : Real),
                    Real.instLT.lt 0 u →
                      Real.instLT.lt 0 epsilon' →
                        Real.instLT.lt u epsilon' →
                          Real.instLE.le u deltaU →
                            Real.instLE.le epsilon' deltaEpsilon →
                              Real.instLE.le (abs (remainder u epsilon'))
                                (instHMul.hMul C (instHMul.hMul u epsilon')))))))
```

### D029: `HighamBench.p15IsBigOSquareRelativeAtRun`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `842e7aff8a90410115cc9487af3e4e031ee31df2cc0899fa080713dcccd52c2d`

Type:

```lean
(Real → Real → Real) → (Real → Real → Real) → Real → Real → Prop
```

Fully explicit type:

```lean
(remainder scale : Real → Real → Real) → (unitRoundoff epsilon : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder scale unitRoundoff epsilon =>
  Exists fun C =>
    Exists fun deltaU =>
      Exists fun deltaEpsilon =>
        And (Real.instLE.le 0 C)
          (And (Real.instLT.lt 0 deltaU)
            (And (Real.instLT.lt 0 deltaEpsilon)
              (And (Real.instLE.le unitRoundoff deltaU)
                (And (Real.instLE.le epsilon deltaEpsilon)
                  (∀ (u epsilon' : Real),
                    Real.instLT.lt 0 u →
                      Real.instLT.lt 0 epsilon' →
                        Real.instLT.lt u epsilon' →
                          Real.instLE.le u deltaU →
                            Real.instLE.le epsilon' deltaEpsilon →
                              Real.instLE.le 0 (scale u epsilon') →
                                Real.instLE.le (abs (remainder u epsilon'))
                                  (instHMul.hMul (instHMul.hMul C (instHPow.hPow u 2)) (scale u epsilon')))))))
```

### D030: `HighamBench.p15MatVec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `46653426fb5f80e06b04a77772652321fa618edf797127f16a95ad856ba2a7a8`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → HighamBench.P15Vector n → HighamBench.P15Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P15Matrix n) → (x : HighamBench.P15Vector n) → HighamBench.P15Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D031: `HighamBench.p15VecNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a716c1fae04d4026c6643ec3b153abae96d0f93b8c6f72ce66bce27b4a46d6f9`

Type:

```lean
{n : Nat} → HighamBench.P15Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : HighamBench.P15Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D032: `HighamBench.P15BLRLinearSolveExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `5650b5a15c65644b15efefe773faa7a2831669a48c7ce64104c9ccf33839902a`

Type:

```lean
{b p r : Nat} →
  instLTNat.lt 0 b →
    instLTNat.lt 0 p →
      instLENat.le r b →
        (algorithm : HighamBench.P15BLRFactorizationAlgorithm) →
          (threshold : HighamBench.P15BLRThreshold) →
            (recompression : HighamBench.P15BLRRecompression) →
              (A Atilde L U : HighamBench.P15Matrix (instHMul.hMul p b)) →
                (v yHat xHat : HighamBench.P15Vector (instHMul.hMul p b)) →
                  (unitRoundoff epsilon : Real) →
                    HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) unitRoundoff epsilon →
                      HighamBench.p15IsNonsingular A →
                        HighamBench.p15BLRRepresents threshold epsilon A Atilde →
                          HighamBench.p15IsFactorBLRRank r L U →
                            HighamBench.P15CompletedBLRFactorization r algorithm threshold recompression unitRoundoff
                                epsilon A Atilde L U →
                              HighamBench.P15CompletedTriangularSolve r HighamBench.P15TriangularSolveDirection.lower
                                  unitRoundoff L v yHat →
                                HighamBench.P15CompletedTriangularSolve r HighamBench.P15TriangularSolveDirection.upper
                                    unitRoundoff U yHat xHat →
                                  HighamBench.P15BLRLinearSolveExecution b p r
```

Fully explicit type:

```lean
{b p r : Nat} →
  (block_size_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b) →
    (block_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p) →
      (rank_le_block_size : @LE.le.{0} Nat instLENat r b) →
        (algorithm : HighamBench.P15BLRFactorizationAlgorithm) →
          (threshold : HighamBench.P15BLRThreshold) →
            (recompression : HighamBench.P15BLRRecompression) →
              (A Atilde L U :
                  HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                (v yHat xHat :
                    HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                  (unitRoundoff epsilon : Real) →
                    (precision :
                        HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) unitRoundoff epsilon) →
                      (A_nonsingular :
                          @HighamBench.p15IsNonsingular
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) A) →
                        (represents : @HighamBench.p15BLRRepresents p b threshold epsilon A Atilde) →
                          (factor_rank : @HighamBench.p15IsFactorBLRRank p b r L U) →
                            (factorization_completed :
                                @HighamBench.P15CompletedBLRFactorization b p r algorithm threshold recompression
                                  unitRoundoff epsilon A Atilde L U) →
                              (lower_completed :
                                  @HighamBench.P15CompletedTriangularSolve p b r
                                    HighamBench.P15TriangularSolveDirection.lower unitRoundoff L v yHat) →
                                (upper_completed :
                                    @HighamBench.P15CompletedTriangularSolve p b r
                                      HighamBench.P15TriangularSolveDirection.upper unitRoundoff U yHat xHat) →
                                  HighamBench.P15BLRLinearSolveExecution b p r
```

### D033: `HighamBench.P15BLRRecompression`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `184eef312a57ab5d86ec09b3a62edb2f4fe92527de10cff181cdfc695e456116`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D034: `HighamBench.P15BLRThreshold`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e2bc11e18c7915802478e0c20e7eb676fc28067e8803e4c25ccd75efeb157e13`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D035: `HighamBench.P15FactorizationBackwardError.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c2e9cd3c2168280bfb57e9581608f5a3d4ae5e906874182754d43805c4ff70d7`

Type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (instHMul.hMul p b)} →
          (error : HighamBench.P15Matrix (instHMul.hMul p b)) →
            (remainder : Real → Real → Real) →
              HighamBench.p15IsBigOMixedAtRun remainder u epsilon →
                Eq (instHAdd.hAdd A error) (HighamBench.p15MatMul L U) →
                  Real.instLE.le (HighamBench.p15FrobNorm error)
                      (instHAdd.hAdd
                        (instHAdd.hAdd
                          (instHMul.hMul
                            (instHAdd.hAdd (instHMul.hMul (HighamBench.p15BLRXi p threshold recompression) epsilon)
                              (HighamBench.p15GammaReal p.cast u))
                            (HighamBench.p15FrobNorm A))
                          (instHMul.hMul
                            (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                              (HighamBench.p15FrobNorm L))
                            (HighamBench.p15FrobNorm U)))
                        (remainder u epsilon)) →
                    HighamBench.P15FactorizationBackwardError r threshold recompression u epsilon A L U
```

Fully explicit type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (error : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
            (remainder : Real → Real → Real) →
              (remainder_control : HighamBench.p15IsBigOMixedAtRun remainder u epsilon) →
                (factorization_eq :
                    @Eq.{1}
                      (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (@HAdd.hAdd.{0, 0, 0}
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@instHAdd.{0}
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@Matrix.add.{0, 0, 0}
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                            Real.instAdd))
                        A error)
                      (@HighamBench.p15MatMul (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) L
                        U)) →
                  (error_le :
                      @LE.le.{0} Real Real.instLE
                        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          error)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (HighamBench.p15BLRXi p threshold recompression) epsilon)
                                (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u))
                              (@HighamBench.p15FrobNorm
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) A))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                                (@HighamBench.p15FrobNorm
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) L))
                              (@HighamBench.p15FrobNorm
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) U)))
                          (remainder u epsilon))) →
                    @HighamBench.P15FactorizationBackwardError b p r threshold recompression u epsilon A L U
```

### D036: `HighamBench.P15TriangularSolveBackwardError.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `b2c0b8abb2f0558228f23b7697515a79b0b2ddd4dbe9de507c55850ac839a437`

Type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (instHMul.hMul p b)} →
        {rhs x : HighamBench.P15Vector (instHMul.hMul p b)} →
          (matrixError : HighamBench.P15Matrix (instHMul.hMul p b)) →
            (rhsError : HighamBench.P15Vector (instHMul.hMul p b)) →
              Eq (HighamBench.p15MatVec (instHAdd.hAdd T matrixError) x) (instHAdd.hAdd rhs rhsError) →
                Real.instLE.le (HighamBench.p15FrobNorm matrixError)
                    (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15BLRTriangularSolveCost b p r) u)
                      (HighamBench.p15FrobNorm T)) →
                  Real.instLE.le (HighamBench.p15VecNorm rhsError)
                      (instHMul.hMul (HighamBench.p15GammaReal p.cast u) (HighamBench.p15VecNorm rhs)) →
                    HighamBench.P15TriangularSolveBackwardError r direction u T rhs x
```

Fully explicit type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
        {rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (matrixError : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
            (rhsError : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
              (solve_eq :
                  @Eq.{1} (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                    (@HighamBench.p15MatVec (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                      (@HAdd.hAdd.{0, 0, 0}
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@instHAdd.{0}
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@Matrix.add.{0, 0, 0}
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                            Real.instAdd))
                        T matrixError)
                      x)
                    (@HAdd.hAdd.{0, 0, 0}
                      (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (@instHAdd.{0}
                        (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@Pi.instAdd.{0, 0} (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (fun (a : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) => Real)
                          fun (i : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                          Real.instAdd))
                      rhs rhsError)) →
                (matrix_error_le :
                    @LE.le.{0} Real Real.instLE
                      (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                        matrixError)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (HighamBench.p15GammaReal (HighamBench.p15BLRTriangularSolveCost b p r) u)
                        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          T))) →
                  (rhs_error_le :
                      @LE.le.{0} Real Real.instLE
                        (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          rhsError)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                          (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                            rhs))) →
                    @HighamBench.P15TriangularSolveBackwardError p b r direction u T rhs x
```

### D037: `HighamBench.P15TriangularSolveDirection`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `2739599cb5c208da8ba46dbb051853914b460ecd048eb3ce127ee1b183a6a5f3`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D038: `HighamBench.p15BLRSolveCost._proof_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `9d0e87eee49660c5b3c5b7631778db5647e4d28e6668a010375f571402b39ec4`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D039: `HighamBench.p15BLRXi._proof_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `bec3b366c0a588b14aa37dd233d61af7e47a2ba0a0eb0217d7909a24061d7a5c`

Type:

```lean
(instHAdd.hAdd 5 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D040: `HighamBench.p15BLRXi.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a1d7660b5a3e94f47fb136e11de89d815a1f6f99ba2238e3edc3a8d64723e165`

Type:

```lean
(motive : HighamBench.P15BLRRecompression → HighamBench.P15BLRThreshold → Sort u_1) →
  (recompression : HighamBench.P15BLRRecompression) →
    (threshold : HighamBench.P15BLRThreshold) →
      (Unit → motive HighamBench.P15BLRRecompression.without HighamBench.P15BLRThreshold.local) →
        (Unit → motive HighamBench.P15BLRRecompression.without HighamBench.P15BLRThreshold.global) →
          (Unit → motive HighamBench.P15BLRRecompression.with HighamBench.P15BLRThreshold.local) →
            (Unit → motive HighamBench.P15BLRRecompression.with HighamBench.P15BLRThreshold.global) →
              motive recompression threshold
```

Fully explicit type:

```lean
(motive : HighamBench.P15BLRRecompression → HighamBench.P15BLRThreshold → Sort u_1) →
  (recompression : HighamBench.P15BLRRecompression) →
    (threshold : HighamBench.P15BLRThreshold) →
      (h_1 : (a : Unit) → motive HighamBench.P15BLRRecompression.without HighamBench.P15BLRThreshold.local) →
        (h_2 : (a : Unit) → motive HighamBench.P15BLRRecompression.without HighamBench.P15BLRThreshold.global) →
          (h_3 : (a : Unit) → motive HighamBench.P15BLRRecompression.with HighamBench.P15BLRThreshold.local) →
            (h_4 : (a : Unit) → motive HighamBench.P15BLRRecompression.with HighamBench.P15BLRThreshold.global) →
              motive recompression threshold
```

Definition body (one-level semantic boundary):

```lean
fun motive recompression threshold h_1 h_2 h_3 h_4 =>
  HighamBench.P15BLRRecompression.casesOn recompression
    (HighamBench.P15BLRThreshold.casesOn threshold (h_1 Unit.unit) (h_2 Unit.unit))
    (HighamBench.P15BLRThreshold.casesOn threshold (h_3 Unit.unit) (h_4 Unit.unit))
```

### D041: `HighamBench.p15MatMul`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `82a32c03123a1b58cce8a2734d2ddfed6b499db78b5c4e68d56caf8636e3bb0e`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → HighamBench.P15Matrix n → HighamBench.P15Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P15Matrix n) → HighamBench.P15Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D042: `HighamBench.p15RectFrobNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f8df59150997c9c35d296b01efb6efe480f420d12b4d3873085fbf5fff732e33`

Type:

```lean
{m n : Nat} → HighamBench.P15RectMatrix m n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P15RectMatrix m n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D043: `HighamBench.P15BLRFactorizationAlgorithm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `55236782b6eb2958981cd7ade1aafafec01e8f1dcb72f732214d156bee39ecec`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D044: `HighamBench.P15BLRRecompression.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b81703bd43cb9741e32fc7ad503c8f369ffe55be40e8e7d6bc2374cf7a742b72`

Type:

```lean
{motive : HighamBench.P15BLRRecompression → Sort u} →
  (t : HighamBench.P15BLRRecompression) →
    motive HighamBench.P15BLRRecompression.without → motive HighamBench.P15BLRRecompression.with → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15BLRRecompression) → Sort u} →
  (t : HighamBench.P15BLRRecompression) →
    (without : motive HighamBench.P15BLRRecompression.without) →
      («with» : motive HighamBench.P15BLRRecompression.with) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t without «with» => HighamBench.P15BLRRecompression.rec without «with» t
```

### D045: `HighamBench.P15BLRRecompression.with`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `22d601e2e4bd74edece2b74479af68b0a4ddefed62faa92727c3d2b097562dab`

Type:

```lean
HighamBench.P15BLRRecompression
```

Fully explicit type:

```lean
HighamBench.P15BLRRecompression
```

### D046: `HighamBench.P15BLRRecompression.without`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e33ab8fec1f818f03ada0115fe3b390d0d6c11ef7ccaf47e4f7bac6edc637082`

Type:

```lean
HighamBench.P15BLRRecompression
```

Fully explicit type:

```lean
HighamBench.P15BLRRecompression
```

### D047: `HighamBench.P15BLRThreshold.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8eb410f5081e0717f83f45dda75ce2ed416bdd3f9c33ce8d8bd2d08aef99f7d8`

Type:

```lean
{motive : HighamBench.P15BLRThreshold → Sort u} →
  (t : HighamBench.P15BLRThreshold) →
    motive HighamBench.P15BLRThreshold.local → motive HighamBench.P15BLRThreshold.global → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15BLRThreshold) → Sort u} →
  (t : HighamBench.P15BLRThreshold) →
    («local» : motive HighamBench.P15BLRThreshold.local) →
      (global : motive HighamBench.P15BLRThreshold.global) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t «local» global => HighamBench.P15BLRThreshold.rec «local» global t
```

### D048: `HighamBench.P15BLRThreshold.global`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `5ae988e456ef025679682e499a244a52188744a737558e58b1d9d60f70b688b5`

Type:

```lean
HighamBench.P15BLRThreshold
```

Fully explicit type:

```lean
HighamBench.P15BLRThreshold
```

### D049: `HighamBench.P15BLRThreshold.local`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `b02c95e620ddc4f9263cabc12ce7e8d4dfbbb8dfced4a022d73b7aebfb67ad25`

Type:

```lean
HighamBench.P15BLRThreshold
```

Fully explicit type:

```lean
HighamBench.P15BLRThreshold
```

### D050: `HighamBench.P15CompletedBLRFactorization`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `606ea1115f3422f605f09ea64c5e3735c303ea85d1897cc1b7ea54fc3692857c`

Type:

```lean
{b p : Nat} →
  Nat →
    HighamBench.P15BLRFactorizationAlgorithm →
      HighamBench.P15BLRThreshold →
        HighamBench.P15BLRRecompression →
          Real →
            Real →
              HighamBench.P15Matrix (instHMul.hMul p b) →
                HighamBench.P15Matrix (instHMul.hMul p b) →
                  HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{b p : Nat} →
  (r : Nat) →
    (algorithm : HighamBench.P15BLRFactorizationAlgorithm) →
      (threshold : HighamBench.P15BLRThreshold) →
        (recompression : HighamBench.P15BLRRecompression) →
          (u epsilon : Real) →
            (A Atilde L U :
                HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
              Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b p} r algorithm threshold recompression u epsilon A Atilde L U =>
  And (HighamBench.P15CompletedBLRFactorizationTrace r algorithm threshold recompression u epsilon Atilde L U)
    (Nonempty (HighamBench.P15FactorizationLocalAnalysis r threshold recompression u epsilon A L U))
```

### D051: `HighamBench.P15CompletedTriangularSolve`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `61eb85d68dcb236655902d60decabc797871210a51a1ef2358bad8c1cbfd8656`

Type:

```lean
{p b : Nat} →
  Nat →
    HighamBench.P15TriangularSolveDirection →
      Real →
        HighamBench.P15Matrix (instHMul.hMul p b) →
          HighamBench.P15Vector (instHMul.hMul p b) → HighamBench.P15Vector (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (direction : HighamBench.P15TriangularSolveDirection) →
      (u : Real) →
        (T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
          (rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r direction u T rhs x =>
  And (Nonempty (HighamBench.P15CompletedTriangularSolveTrace r direction u T rhs x))
    (Nonempty (HighamBench.P15TriangularSolveLocalAnalysis r direction u T rhs x))
```

### D052: `HighamBench.P15RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8feb40d08c5292d10bb340b09678c4d176088c4c97bb1880d9f95a2c76fde9a2`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(m n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun m n => Matrix (Fin m) (Fin n) Real
```

### D053: `HighamBench.p15AdmissiblePrecision`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `163653545cc46da55ac53d48b395986d09e643293aa7fb4c106e6c742adbc4e3`

Type:

```lean
Real → Real → Real → Prop
```

Fully explicit type:

```lean
(c u epsilon : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun c u epsilon =>
  And (Real.instLT.lt 0 u)
    (And (Real.instLT.lt 0 epsilon)
      (And (Real.instLT.lt u epsilon) (Real.instLT.lt (instHMul.hMul (instHMul.hMul 3 c) u) 1)))
```

### D054: `HighamBench.p15BLRRepresents`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0bf4757bbc049d923d6621a1e589b4df23c1ba532f0802bb047cb4a19e019c19`

Type:

```lean
{p b : Nat} →
  HighamBench.P15BLRThreshold →
    Real → HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (threshold : HighamBench.P15BLRThreshold) →
    (epsilon : Real) →
      (A Atilde : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} threshold epsilon A Atilde =>
  And (∀ (i : Fin p), Eq (HighamBench.p15MatrixBlock Atilde i i) (HighamBench.p15MatrixBlock A i i))
    (∀ (i j : Fin p),
      Ne i j →
        Exists fun k =>
          And (HighamBench.p15BLRBlockApproximation threshold epsilon A i j k (HighamBench.p15MatrixBlock Atilde i j))
            (∀ (ell : Nat) (candidate : HighamBench.P15Matrix b),
              HighamBench.p15BLRBlockApproximation threshold epsilon A i j ell candidate → instLENat.le k ell))
```

### D055: `HighamBench.p15BLRTriangularSolveCost`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `43766147f49acd15be088fd137e9b18b67b31e32af7ca125bd5b4ee721e2bbe6`

Type:

```lean
Nat → Nat → Nat → Real
```

Fully explicit type:

```lean
(b p r : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r => instHAdd.hAdd (instHAdd.hAdd b.cast (instHMul.hMul r.cast r.cast.sqrt)) p.cast
```

### D056: `HighamBench.p15IsFactorBLRRank`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `caba8603744ec7aec3bfe43bb632fc5757c0af57502cc4f36e059c39b9313ef4`

Type:

```lean
{p b : Nat} → Nat → HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) → (L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r L U =>
  And (HighamBench.p15IsBLRMatrix r L)
    (And (HighamBench.p15IsBLRMatrix r U)
      (∀ (s : Nat), HighamBench.p15IsBLRMatrix s L → HighamBench.p15IsBLRMatrix s U → instLENat.le r s))
```

### D057: `HighamBench.p15IsNonsingular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `725bc01ee86ff95bcecf211671daa8a6a5dec9a47a1a481248902e115feeece2`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P15Matrix n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A =>
  Exists fun Ainv =>
    And (Eq (HighamBench.p15MatMul Ainv A) (HighamBench.p15Identity n))
      (Eq (HighamBench.p15MatMul A Ainv) (HighamBench.p15Identity n))
```

### D058: `HighamBench.P15BLRFactorizationAlgorithm.ucf`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `93a612d37f6c47859778cd40fd5fde9d5f37cd69a2f8fcff4bdda0f474f19c51`

Type:

```lean
HighamBench.P15BLRFactorizationAlgorithm
```

Fully explicit type:

```lean
HighamBench.P15BLRFactorizationAlgorithm
```

### D059: `HighamBench.P15BLRFactorizationAlgorithm.ufc`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `39d148233d14cc9057e6abeed9c5dfc41bf64932051a49ece31079eb79d2c097`

Type:

```lean
HighamBench.P15BLRFactorizationAlgorithm
```

Fully explicit type:

```lean
HighamBench.P15BLRFactorizationAlgorithm
```

### D060: `HighamBench.P15BLRRecompression.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `b3bd839df8a5575f92a8d277048ec72db51ad4d9c566c3a66067e793be53a850`

Type:

```lean
{motive : HighamBench.P15BLRRecompression → Sort u} →
  motive HighamBench.P15BLRRecompression.without →
    motive HighamBench.P15BLRRecompression.with → (t : HighamBench.P15BLRRecompression) → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15BLRRecompression) → Sort u} →
  (without : motive HighamBench.P15BLRRecompression.without) →
    («with» : motive HighamBench.P15BLRRecompression.with) → (t : HighamBench.P15BLRRecompression) → motive t
```

### D061: `HighamBench.P15BLRThreshold.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `09d8cf322bde803da325f034925cbbbdb74b5bd9f34fa7d51d83a97f077fdac6`

Type:

```lean
{motive : HighamBench.P15BLRThreshold → Sort u} →
  motive HighamBench.P15BLRThreshold.local →
    motive HighamBench.P15BLRThreshold.global → (t : HighamBench.P15BLRThreshold) → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15BLRThreshold) → Sort u} →
  («local» : motive HighamBench.P15BLRThreshold.local) →
    (global : motive HighamBench.P15BLRThreshold.global) → (t : HighamBench.P15BLRThreshold) → motive t
```

### D062: `HighamBench.P15CompletedBLRFactorizationTrace`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `29fc7283a5ce373d718ebc4a9f0655d0988b76ed59f5d7ee4462c13d65907f70`

Type:

```lean
{b p : Nat} →
  Nat →
    HighamBench.P15BLRFactorizationAlgorithm →
      HighamBench.P15BLRThreshold →
        HighamBench.P15BLRRecompression →
          Real →
            Real →
              HighamBench.P15Matrix (instHMul.hMul p b) →
                HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{b p : Nat} →
  (r : Nat) →
    (algorithm : HighamBench.P15BLRFactorizationAlgorithm) →
      (threshold : HighamBench.P15BLRThreshold) →
        (recompression : HighamBench.P15BLRRecompression) →
          (u epsilon : Real) →
            (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b p} r algorithm threshold recompression u epsilon A L U =>
  HighamBench.instReprP15BLRFactorizationAlgorithm.repr.match_1 (fun algorithm => Prop) algorithm
    (fun _ => Nonempty (HighamBench.P15CompletedUFCFactorization r threshold recompression u epsilon A L U)) fun _ =>
    Nonempty (HighamBench.P15CompletedUCFFactorization r threshold recompression u epsilon A L U)
```

### D063: `HighamBench.P15CompletedTriangularSolveTrace`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `b99d035982d428affb584c3593d4958a7bbc261bcd91ac64bb267c4f3deb3497`

Type:

```lean
{p b : Nat} →
  Nat →
    HighamBench.P15TriangularSolveDirection →
      Real →
        HighamBench.P15Matrix (instHMul.hMul p b) →
          HighamBench.P15Vector (instHMul.hMul p b) → HighamBench.P15Vector (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (direction : HighamBench.P15TriangularSolveDirection) →
      (u : Real) →
        (T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
          (rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D064: `HighamBench.P15FactorizationLocalAnalysis`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `9bee3ca2a98837ed84fed1492bf5675867247ef6d05c78bb200a788893de5a0b`

Type:

```lean
{b p : Nat} →
  Nat →
    HighamBench.P15BLRThreshold →
      HighamBench.P15BLRRecompression →
        Real →
          Real →
            HighamBench.P15Matrix (instHMul.hMul p b) →
              HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{b p : Nat} →
  (r : Nat) →
    (threshold : HighamBench.P15BLRThreshold) →
      (recompression : HighamBench.P15BLRRecompression) →
        (u epsilon : Real) →
          (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D065: `HighamBench.P15TriangularSolveLocalAnalysis`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `24d6dfa2706874589e40509d67962bb8be2db5e79716bcfa9f580d5204079879`

Type:

```lean
{p b : Nat} →
  Nat →
    HighamBench.P15TriangularSolveDirection →
      Real →
        HighamBench.P15Matrix (instHMul.hMul p b) →
          HighamBench.P15Vector (instHMul.hMul p b) → HighamBench.P15Vector (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (direction : HighamBench.P15TriangularSolveDirection) →
      (u : Real) →
        (T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
          (rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D066: `HighamBench.p15AdmissiblePrecision._proof_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `213bd1e73174b7595c41e7b42aa9993d17dae1408a69ea3f0097deeae64f2916`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D067: `HighamBench.p15BLRBlockApproximation`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `2ae3164d58c89c16825b3800d5cbffb555544425da7350adab053e7f6a8e4e19`

Type:

```lean
{p b : Nat} →
  HighamBench.P15BLRThreshold →
    Real → HighamBench.P15Matrix (instHMul.hMul p b) → Fin p → Fin p → Nat → HighamBench.P15Matrix b → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (threshold : HighamBench.P15BLRThreshold) →
    (epsilon : Real) →
      (A : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
        (i j : Fin p) → (k : Nat) → (candidate : HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} threshold epsilon A i j k candidate =>
  Exists fun X =>
    Exists fun Y =>
      And (HighamBench.p15OrthonormalColumns X)
        (And (Eq candidate (HighamBench.p15OrientedLowRankBlock i j X Y))
          (Real.instLE.le (HighamBench.p15FrobNorm (instHSub.hSub candidate (HighamBench.p15MatrixBlock A i j)))
            (instHMul.hMul epsilon
              (HighamBench.instReprP15BLRThreshold.repr.match_1 (fun threshold => Real) threshold
                (fun _ => HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock A i j)) fun _ =>
                HighamBench.p15FrobNorm A))))
```

### D068: `HighamBench.p15Identity`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b666a790818338446ad29c7622b631b68fff0b34eabf08253467b02fd032fa63`

Type:

```lean
(n : Nat) → HighamBench.P15Matrix n
```

Fully explicit type:

```lean
(n : Nat) → HighamBench.P15Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n i j => ite (Eq i j) 1 0
```

### D069: `HighamBench.p15IsBLRMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `23b2fd5405f6ba223eaef2d1cd61e62edd91a663b0bd801522dff0a705cea7db`

Type:

```lean
{p b : Nat} → Nat → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) → (A : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r A =>
  Exists fun X =>
    Exists fun Y =>
      ∀ (i j : Fin p), Ne i j → Eq (HighamBench.p15MatrixBlock A i j) (HighamBench.p15LowRankMatrix (X i j) (Y i j))
```

### D070: `HighamBench.p15MatrixBlock`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b6f6652f790cad96f7c671f939858824c8903bdc549b35ca6417e1dee14a7aaa`

Type:

```lean
{p b : Nat} → HighamBench.P15Matrix (instHMul.hMul p b) → Fin p → Fin p → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{p b : Nat} →
  (A : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
    (i j : Fin p) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun {p b} A i j row col => A (HighamBench.p15BlockIndex i row) (HighamBench.p15BlockIndex j col)
```

### D071: `HighamBench.P15CompletedTriangularSolveTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `b5dc6dfaf8dc0887875cbd41f6c0464d1f6a3551c18b837743ce172df4342e42`

Type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (instHMul.hMul p b)} →
        {rhs x : HighamBench.P15Vector (instHMul.hMul p b)} →
          (HighamBench.instReprP15TriangularSolveDirection.repr.match_1 (fun direction => Prop) direction
              (fun _ => HighamBench.p15IsBlockLowerTriangular T) fun _ => HighamBench.p15IsBlockUpperTriangular T) →
            (∀ (i : Fin p), HighamBench.p15IsNonsingular (HighamBench.p15MatrixBlock T i i)) →
              (productValue : Fin p → Fin p → HighamBench.P15Vector b) →
                (productError : Fin p → Fin p → HighamBench.P15Matrix b) →
                  (rhsRelativeError : Fin p → HighamBench.P15Vector b) →
                    (productRelativeError : Fin p → Fin p → HighamBench.P15Vector b) →
                      (diagonalError : Fin p → HighamBench.P15Matrix b) →
                        (∀ (i j : Fin p),
                            HighamBench.p15TriangularPrecedes direction i j →
                              Eq (productValue i j)
                                (HighamBench.p15MatVec
                                  (instHAdd.hAdd (HighamBench.p15MatrixBlock T i j) (productError i j))
                                  (HighamBench.p15VectorBlock x j))) →
                          (∀ (i j : Fin p),
                              HighamBench.p15TriangularPrecedes direction i j →
                                Real.instLE.le (HighamBench.p15FrobNorm (productError i j))
                                  (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15LowRankKernelCost b r) u)
                                    (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock T i j)))) →
                            (∀ (i : Fin p) (row : Fin b),
                                Real.instLE.le (abs (rhsRelativeError i row)) (HighamBench.p15GammaReal p.cast u)) →
                              (∀ (i j : Fin p) (row : Fin b),
                                  HighamBench.p15TriangularPrecedes direction i j →
                                    Real.instLE.le (abs (productRelativeError i j row))
                                      (HighamBench.p15GammaReal p.cast u)) →
                                (∀ (i : Fin p),
                                    Real.instLE.le (HighamBench.p15FrobNorm (diagonalError i))
                                      (instHMul.hMul (HighamBench.p15GammaReal b.cast u)
                                        (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock T i i)))) →
                                  (∀ (i : Fin p),
                                      Eq
                                        (HighamBench.p15MatVec
                                          (instHAdd.hAdd (HighamBench.p15MatrixBlock T i i) (diagonalError i))
                                          (HighamBench.p15VectorBlock x i))
                                        (instHSub.hSub
                                          (HighamBench.p15VecHadamard (HighamBench.p15VectorBlock rhs i)
                                            (instHAdd.hAdd (HighamBench.p15OnesVector b) (rhsRelativeError i)))
                                          ((HighamBench.p15TriangularPredecessors direction i).sum fun j =>
                                            HighamBench.p15VecHadamard (productValue i j)
                                              (instHAdd.hAdd (HighamBench.p15OnesVector b)
                                                (productRelativeError i j))))) →
                                    HighamBench.P15CompletedTriangularSolveTrace r direction u T rhs x
```

Fully explicit type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
        {rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (triangular :
              HighamBench.instReprP15TriangularSolveDirection.repr.match_1.{1}
                (fun (direction : HighamBench.P15TriangularSolveDirection) => Prop) direction
                (fun (_ : Unit) => @HighamBench.p15IsBlockLowerTriangular p b T) fun (_ : Unit) =>
                @HighamBench.p15IsBlockUpperTriangular p b T) →
            (diagonal_nonsingular :
                ∀ (i : Fin p), @HighamBench.p15IsNonsingular b (@HighamBench.p15MatrixBlock p b T i i)) →
              (productValue : Fin p → Fin p → HighamBench.P15Vector b) →
                (productError : Fin p → Fin p → HighamBench.P15Matrix b) →
                  (rhsRelativeError : Fin p → HighamBench.P15Vector b) →
                    (productRelativeError : Fin p → Fin p → HighamBench.P15Vector b) →
                      (diagonalError : Fin p → HighamBench.P15Matrix b) →
                        (product_eq :
                            ∀ (i j : Fin p),
                              @HighamBench.p15TriangularPrecedes direction p i j →
                                @Eq.{1} (HighamBench.P15Vector b) (productValue i j)
                                  (@HighamBench.p15MatVec b
                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
                                      (HighamBench.P15Matrix b)
                                      (@instHAdd.{0} (HighamBench.P15Matrix b)
                                        (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                                      (@HighamBench.p15MatrixBlock p b T i j) (productError i j))
                                    (@HighamBench.p15VectorBlock p b x j))) →
                          (product_error_le :
                              ∀ (i j : Fin p),
                                @HighamBench.p15TriangularPrecedes direction p i j →
                                  @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm b (productError i j))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (HighamBench.p15GammaReal (HighamBench.p15LowRankKernelCost b r) u)
                                      (@HighamBench.p15FrobNorm b (@HighamBench.p15MatrixBlock p b T i j)))) →
                            (rhs_relative_error_le :
                                ∀ (i : Fin p) (row : Fin b),
                                  @LE.le.{0} Real Real.instLE
                                    (@abs.{0} Real Real.lattice Real.instAddGroup (rhsRelativeError i row))
                                    (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)) →
                              (product_relative_error_le :
                                  ∀ (i j : Fin p) (row : Fin b),
                                    @HighamBench.p15TriangularPrecedes direction p i j →
                                      @LE.le.{0} Real Real.instLE
                                        (@abs.{0} Real Real.lattice Real.instAddGroup (productRelativeError i j row))
                                        (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)) →
                                (diagonal_error_le :
                                    ∀ (i : Fin p),
                                      @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm b (diagonalError i))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                          (@HighamBench.p15FrobNorm b (@HighamBench.p15MatrixBlock p b T i i)))) →
                                  (block_steps :
                                      ∀ (i : Fin p),
                                        @Eq.{1} (HighamBench.P15Vector b)
                                          (@HighamBench.p15MatVec b
                                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
                                              (HighamBench.P15Matrix b)
                                              (@instHAdd.{0} (HighamBench.P15Matrix b)
                                                (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                                              (@HighamBench.p15MatrixBlock p b T i i) (diagonalError i))
                                            (@HighamBench.p15VectorBlock p b x i))
                                          (@HSub.hSub.{0, 0, 0} (HighamBench.P15Vector b) (HighamBench.P15Vector b)
                                            (HighamBench.P15Vector b)
                                            (@instHSub.{0} (HighamBench.P15Vector b)
                                              (@Pi.instSub.{0, 0} (Fin b) (fun (a : Fin b) => Real) fun (i : Fin b) =>
                                                Real.instSub))
                                            (@HighamBench.p15VecHadamard b (@HighamBench.p15VectorBlock p b rhs i)
                                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Vector b) (HighamBench.P15Vector b)
                                                (HighamBench.P15Vector b)
                                                (@instHAdd.{0} (HighamBench.P15Vector b)
                                                  (@Pi.instAdd.{0, 0} (Fin b) (fun (a : Fin b) => Real)
                                                    fun (i : Fin b) => Real.instAdd))
                                                (HighamBench.p15OnesVector b) (rhsRelativeError i)))
                                            (@Finset.sum.{0, 0} (Fin p) (HighamBench.P15Vector b)
                                              (@Pi.addCommMonoid.{0, 0} (Fin b) (fun (a : Fin b) => Real)
                                                fun (i : Fin b) => Real.instAddCommMonoid)
                                              (@HighamBench.p15TriangularPredecessors direction p i) fun (j : Fin p) =>
                                              @HighamBench.p15VecHadamard b (productValue i j)
                                                (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Vector b)
                                                  (HighamBench.P15Vector b) (HighamBench.P15Vector b)
                                                  (@instHAdd.{0} (HighamBench.P15Vector b)
                                                    (@Pi.instAdd.{0, 0} (Fin b) (fun (a : Fin b) => Real)
                                                      fun (i : Fin b) => Real.instAdd))
                                                  (HighamBench.p15OnesVector b) (productRelativeError i j))))) →
                                    @HighamBench.P15CompletedTriangularSolveTrace p b r direction u T rhs x
```

### D072: `HighamBench.P15CompletedUCFFactorization`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `5b7298c0394e3cd6f32f441cc34400e000f95ed1f77f2fc5f891d06dd839dbfa`

Type:

```lean
{p b : Nat} →
  Nat →
    HighamBench.P15BLRThreshold →
      HighamBench.P15BLRRecompression →
        Real →
          Real →
            HighamBench.P15Matrix (instHMul.hMul p b) →
              HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (threshold : HighamBench.P15BLRThreshold) →
      (recompression : HighamBench.P15BLRRecompression) →
        (u epsilon : Real) →
          (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D073: `HighamBench.P15CompletedUFCFactorization`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `5aac7c45973a6b3b3d7d96251486d4c0f15d78aaea9cad06ee8ff209a59a03bd`

Type:

```lean
{p b : Nat} →
  Nat →
    HighamBench.P15BLRThreshold →
      HighamBench.P15BLRRecompression →
        Real →
          Real →
            HighamBench.P15Matrix (instHMul.hMul p b) →
              HighamBench.P15Matrix (instHMul.hMul p b) → HighamBench.P15Matrix (instHMul.hMul p b) → Type
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (threshold : HighamBench.P15BLRThreshold) →
      (recompression : HighamBench.P15BLRRecompression) →
        (u epsilon : Real) →
          (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D074: `HighamBench.P15FactorizationLocalAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `d184def78c6f9a11af22f6fe369e49625c0af080c72af1f12045c262b4ef9f99`

Type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (instHMul.hMul p b)} →
          (compressionError inputRoundoffError factorRoundoffError mixedError :
              HighamBench.P15Matrix (instHMul.hMul p b)) →
            (mixedRemainder : Real → Real → Real) →
              Eq
                  (instHAdd.hAdd A
                    (instHAdd.hAdd
                      (instHAdd.hAdd (instHAdd.hAdd compressionError inputRoundoffError) factorRoundoffError)
                      mixedError))
                  (HighamBench.p15MatMul L U) →
                Real.instLE.le (HighamBench.p15FrobNorm compressionError)
                    (instHMul.hMul (instHMul.hMul (HighamBench.p15BLRXi p threshold recompression) epsilon)
                      (HighamBench.p15FrobNorm A)) →
                  Real.instLE.le (HighamBench.p15FrobNorm inputRoundoffError)
                      (instHMul.hMul (HighamBench.p15GammaReal p.cast u) (HighamBench.p15FrobNorm A)) →
                    Real.instLE.le (HighamBench.p15FrobNorm factorRoundoffError)
                        (instHMul.hMul
                          (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                            (HighamBench.p15FrobNorm L))
                          (HighamBench.p15FrobNorm U)) →
                      Real.instLE.le (HighamBench.p15FrobNorm mixedError) (mixedRemainder u epsilon) →
                        HighamBench.p15IsBigOMixedAtRun mixedRemainder u epsilon →
                          HighamBench.P15FactorizationLocalAnalysis r threshold recompression u epsilon A L U
```

Fully explicit type:

```lean
{b p r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (compressionError inputRoundoffError factorRoundoffError mixedError :
              HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
            (mixedRemainder : Real → Real → Real) →
              (decomposition_eq :
                  @Eq.{1} (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                    (@HAdd.hAdd.{0, 0, 0}
                      (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (@instHAdd.{0}
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@Matrix.add.{0, 0, 0}
                          (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                          Real.instAdd))
                      A
                      (@HAdd.hAdd.{0, 0, 0}
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@instHAdd.{0}
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@Matrix.add.{0, 0, 0}
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                            Real.instAdd))
                        (@HAdd.hAdd.{0, 0, 0}
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@instHAdd.{0}
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (@Matrix.add.{0, 0, 0}
                              (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                              Real.instAdd))
                          (@HAdd.hAdd.{0, 0, 0}
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (@instHAdd.{0}
                              (HighamBench.P15Matrix
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (@Matrix.add.{0, 0, 0}
                                (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                                Real.instAdd))
                            compressionError inputRoundoffError)
                          factorRoundoffError)
                        mixedError))
                    (@HighamBench.p15MatMul (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) L
                      U)) →
                (compression_error_le :
                    @LE.le.{0} Real Real.instLE
                      (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                        compressionError)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (HighamBench.p15BLRXi p threshold recompression) epsilon)
                        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          A))) →
                  (input_roundoff_error_le :
                      @LE.le.{0} Real Real.instLE
                        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          inputRoundoffError)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                          (@HighamBench.p15FrobNorm
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) A))) →
                    (factor_roundoff_error_le :
                        @LE.le.{0} Real Real.instLE
                          (@HighamBench.p15FrobNorm
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) factorRoundoffError)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                              (@HighamBench.p15FrobNorm
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) L))
                            (@HighamBench.p15FrobNorm
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) U))) →
                      (mixed_error_le :
                          @LE.le.{0} Real Real.instLE
                            (@HighamBench.p15FrobNorm
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) mixedError)
                            (mixedRemainder u epsilon)) →
                        (mixed_remainder_control : HighamBench.p15IsBigOMixedAtRun mixedRemainder u epsilon) →
                          @HighamBench.P15FactorizationLocalAnalysis b p r threshold recompression u epsilon A L U
```

### D075: `HighamBench.P15TriangularSolveLocalAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `17c3cf4306c38df41aa5d961bc66738ef25b6e913c71a4255188bc7fc43815b7`

Type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (instHMul.hMul p b)} →
        {rhs x : HighamBench.P15Vector (instHMul.hMul p b)} →
          (kernelError summationError interactionError : HighamBench.P15Matrix (instHMul.hMul p b)) →
            (rhsError : HighamBench.P15Vector (instHMul.hMul p b)) →
              Eq
                  (HighamBench.p15MatVec
                    (instHAdd.hAdd T (instHAdd.hAdd (instHAdd.hAdd kernelError summationError) interactionError)) x)
                  (instHAdd.hAdd rhs rhsError) →
                Real.instLE.le (HighamBench.p15FrobNorm kernelError)
                    (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15LowRankKernelCost b r) u)
                      (HighamBench.p15FrobNorm T)) →
                  Real.instLE.le (HighamBench.p15FrobNorm summationError)
                      (instHMul.hMul (HighamBench.p15GammaReal p.cast u) (HighamBench.p15FrobNorm T)) →
                    Real.instLE.le (HighamBench.p15FrobNorm interactionError)
                        (instHMul.hMul
                          (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15LowRankKernelCost b r) u)
                            (HighamBench.p15GammaReal p.cast u))
                          (HighamBench.p15FrobNorm T)) →
                      Real.instLE.le (HighamBench.p15VecNorm rhsError)
                          (instHMul.hMul (HighamBench.p15GammaReal p.cast u) (HighamBench.p15VecNorm rhs)) →
                        HighamBench.P15TriangularSolveLocalAnalysis r direction u T rhs x
```

Fully explicit type:

```lean
{p b r : Nat} →
  {direction : HighamBench.P15TriangularSolveDirection} →
    {u : Real} →
      {T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
        {rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (kernelError summationError interactionError :
              HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
            (rhsError : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
              (gathered_eq :
                  @Eq.{1} (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                    (@HighamBench.p15MatVec (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                      (@HAdd.hAdd.{0, 0, 0}
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@instHAdd.{0}
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@Matrix.add.{0, 0, 0}
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                            Real.instAdd))
                        T
                        (@HAdd.hAdd.{0, 0, 0}
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@instHAdd.{0}
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (@Matrix.add.{0, 0, 0}
                              (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                              Real.instAdd))
                          (@HAdd.hAdd.{0, 0, 0}
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (HighamBench.P15Matrix
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (@instHAdd.{0}
                              (HighamBench.P15Matrix
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                              (@Matrix.add.{0, 0, 0}
                                (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                                Real.instAdd))
                            kernelError summationError)
                          interactionError))
                      x)
                    (@HAdd.hAdd.{0, 0, 0}
                      (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (@instHAdd.{0}
                        (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@Pi.instAdd.{0, 0} (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (fun (a : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) => Real)
                          fun (i : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                          Real.instAdd))
                      rhs rhsError)) →
                (kernel_error_le :
                    @LE.le.{0} Real Real.instLE
                      (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                        kernelError)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (HighamBench.p15GammaReal (HighamBench.p15LowRankKernelCost b r) u)
                        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          T))) →
                  (summation_error_le :
                      @LE.le.{0} Real Real.instLE
                        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                          summationError)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                          (@HighamBench.p15FrobNorm
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) T))) →
                    (interaction_error_le :
                        @LE.le.{0} Real Real.instLE
                          (@HighamBench.p15FrobNorm
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) interactionError)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (HighamBench.p15GammaReal (HighamBench.p15LowRankKernelCost b r) u)
                              (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u))
                            (@HighamBench.p15FrobNorm
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) T))) →
                      (rhs_error_le :
                          @LE.le.{0} Real Real.instLE
                            (@HighamBench.p15VecNorm
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) rhsError)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                              (@HighamBench.p15VecNorm
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) rhs))) →
                        @HighamBench.P15TriangularSolveLocalAnalysis p b r direction u T rhs x
```

### D076: `HighamBench.instReprP15BLRFactorizationAlgorithm.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `f170b62e1780181c35a46a156b1718c31e11fc5ad1de610936d81dc52775a2ff`

Type:

```lean
(motive : HighamBench.P15BLRFactorizationAlgorithm → Sort u_1) →
  (x : HighamBench.P15BLRFactorizationAlgorithm) →
    (Unit → motive HighamBench.P15BLRFactorizationAlgorithm.ufc) →
      (Unit → motive HighamBench.P15BLRFactorizationAlgorithm.ucf) → motive x
```

Fully explicit type:

```lean
(motive : HighamBench.P15BLRFactorizationAlgorithm → Sort u_1) →
  (x : HighamBench.P15BLRFactorizationAlgorithm) →
    (h_1 : (a : Unit) → motive HighamBench.P15BLRFactorizationAlgorithm.ufc) →
      (h_2 : (a : Unit) → motive HighamBench.P15BLRFactorizationAlgorithm.ucf) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => HighamBench.P15BLRFactorizationAlgorithm.casesOn x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D077: `HighamBench.instReprP15BLRThreshold.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a3fc79126a46d76de79c7b2dd592c4fa306fa0a77acfcfb7079a8a221fed499e`

Type:

```lean
(motive : HighamBench.P15BLRThreshold → Sort u_1) →
  (x : HighamBench.P15BLRThreshold) →
    (Unit → motive HighamBench.P15BLRThreshold.local) → (Unit → motive HighamBench.P15BLRThreshold.global) → motive x
```

Fully explicit type:

```lean
(motive : HighamBench.P15BLRThreshold → Sort u_1) →
  (x : HighamBench.P15BLRThreshold) →
    (h_1 : (a : Unit) → motive HighamBench.P15BLRThreshold.local) →
      (h_2 : (a : Unit) → motive HighamBench.P15BLRThreshold.global) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => HighamBench.P15BLRThreshold.casesOn x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D078: `HighamBench.p15BlockIndex`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `9e33142dfaa09274a463e2d14509613ff1e15a8f300a5da95769f5c50eb19602`

Type:

```lean
{p b : Nat} → Fin p → Fin b → Fin (instHMul.hMul p b)
```

Fully explicit type:

```lean
{p b : Nat} → (i : Fin p) → (row : Fin b) → Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun {p b} i row => ⟨instHAdd.hAdd (instHMul.hMul i.val b) row.val, ⋯⟩
```

### D079: `HighamBench.p15LowRankMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1842193034dc631c3f6c3edebfa469daf6e8b41c15a0037f9331a904ad932e6f`

Type:

```lean
{b r : Nat} → HighamBench.P15RectMatrix b r → HighamBench.P15RectMatrix b r → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{b r : Nat} → (X Y : HighamBench.P15RectMatrix b r) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X Y => HighamBench.p15RectMatMul X (HighamBench.p15RectTranspose Y)
```

### D080: `HighamBench.p15OrientedLowRankBlock`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ff9394e1a4396a66ba3b3a76d24697c53bbc8fd227a368f05d7863cba41863d5`

Type:

```lean
{p b k : Nat} → Fin p → Fin p → HighamBench.P15RectMatrix b k → HighamBench.P15RectMatrix b k → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{p b k : Nat} → (i j : Fin p) → (X Y : HighamBench.P15RectMatrix b k) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun {p b k} i j X Y => ite (instLTFin.lt j i) (HighamBench.p15LowRankMatrix X Y) (HighamBench.p15LowRankMatrix Y X)
```

### D081: `HighamBench.p15OrthonormalColumns`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `deb9d644f031d8e71a57f0238d55fc37a145cb41cbb82b90abe8a87780c03815`

Type:

```lean
{b r : Nat} → HighamBench.P15RectMatrix b r → Prop
```

Fully explicit type:

```lean
{b r : Nat} → (X : HighamBench.P15RectMatrix b r) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X => ∀ (j k : Fin r), Eq (Finset.univ.sum fun i => instHMul.hMul (X i j) (X i k)) (ite (Eq j k) 1 0)
```

### D082: `HighamBench.P15BLRFactorizationAlgorithm.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `30b5d6ce1343e00bc8154d85f4f1a4dcdd43c9c3d0e5e49eb85ea6cdf99eed21`

Type:

```lean
{motive : HighamBench.P15BLRFactorizationAlgorithm → Sort u} →
  (t : HighamBench.P15BLRFactorizationAlgorithm) →
    motive HighamBench.P15BLRFactorizationAlgorithm.ufc → motive HighamBench.P15BLRFactorizationAlgorithm.ucf → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15BLRFactorizationAlgorithm) → Sort u} →
  (t : HighamBench.P15BLRFactorizationAlgorithm) →
    (ufc : motive HighamBench.P15BLRFactorizationAlgorithm.ufc) →
      (ucf : motive HighamBench.P15BLRFactorizationAlgorithm.ucf) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t ufc ucf => HighamBench.P15BLRFactorizationAlgorithm.rec ufc ucf t
```

### D083: `HighamBench.P15CompletedUCFFactorization.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `6b5dfdcd453d3974f9d52bc7f02fe7870a0ebceb2af139612205c84e897482a7`

Type:

```lean
{p b r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (instHMul.hMul p b)} →
          (recompressionError : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) →
            HighamBench.p15RecompressionModel recompression threshold epsilon A recompressionError →
              (updatedColumn updatedRow compressedColumn compressedRow : Fin p → Fin p → HighamBench.P15Matrix b) →
                HighamBench.p15IsBlockLowerTriangular L →
                  HighamBench.p15IsBlockUpperTriangular U →
                    (∀ (k i : Fin p),
                        instLEFin.le k i →
                          HighamBench.p15ComputedBLRUpdate r u A L U recompressionError k i k (updatedColumn k i)) →
                      (∀ (k i : Fin p),
                          instLEFin.le k i →
                            HighamBench.p15ComputedBLRUpdate r u A L U recompressionError k k i (updatedRow k i)) →
                        (∀ (k : Fin p), Eq (updatedColumn k k) (updatedRow k k)) →
                          ((k i : Fin p) →
                              instLTFin.lt k i →
                                HighamBench.P15BlockCompression epsilon
                                  (HighamBench.p15BLRCompressionBase threshold A i k) (updatedColumn k i)
                                  (compressedColumn k i)) →
                            ((k i : Fin p) →
                                instLTFin.lt k i →
                                  HighamBench.P15BlockCompression epsilon
                                    (HighamBench.p15BLRCompressionBase threshold A k i) (updatedRow k i)
                                    (compressedRow k i)) →
                              (∀ (k : Fin p),
                                  HighamBench.p15ComputedDenseLU u (updatedColumn k k)
                                    (HighamBench.p15MatrixBlock L k k) (HighamBench.p15MatrixBlock U k k)) →
                                (∀ (k i : Fin p),
                                    instLTFin.lt k i →
                                      HighamBench.p15ComputedRightTriangularSolve u (compressedColumn k i)
                                        (HighamBench.p15MatrixBlock L i k) (HighamBench.p15MatrixBlock U k k)) →
                                  (∀ (k i : Fin p),
                                      instLTFin.lt k i →
                                        HighamBench.p15ComputedLeftTriangularSolve u (compressedRow k i)
                                          (HighamBench.p15MatrixBlock L k k) (HighamBench.p15MatrixBlock U k i)) →
                                    HighamBench.P15CompletedUCFFactorization r threshold recompression u epsilon A L U
```

Fully explicit type:

```lean
{p b r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (recompressionError : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) →
            (recompression_model :
                @HighamBench.p15RecompressionModel p b recompression threshold epsilon A recompressionError) →
              (updatedColumn updatedRow compressedColumn compressedRow : Fin p → Fin p → HighamBench.P15Matrix b) →
                (lower_triangular : @HighamBench.p15IsBlockLowerTriangular p b L) →
                  (upper_triangular : @HighamBench.p15IsBlockUpperTriangular p b U) →
                    (update_column :
                        ∀ (k i : Fin p),
                          @LE.le.{0} (Fin p) (@instLEFin p) k i →
                            @HighamBench.p15ComputedBLRUpdate p b r u A L U recompressionError k i k
                              (updatedColumn k i)) →
                      (update_row :
                          ∀ (k i : Fin p),
                            @LE.le.{0} (Fin p) (@instLEFin p) k i →
                              @HighamBench.p15ComputedBLRUpdate p b r u A L U recompressionError k k i
                                (updatedRow k i)) →
                        (diagonal_updates_agree :
                            ∀ (k : Fin p), @Eq.{1} (HighamBench.P15Matrix b) (updatedColumn k k) (updatedRow k k)) →
                          (lower_compression :
                              (k i : Fin p) →
                                @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                  @HighamBench.P15BlockCompression b epsilon
                                    (@HighamBench.p15BLRCompressionBase p b threshold A i k) (updatedColumn k i)
                                    (compressedColumn k i)) →
                            (upper_compression :
                                (k i : Fin p) →
                                  @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                    @HighamBench.P15BlockCompression b epsilon
                                      (@HighamBench.p15BLRCompressionBase p b threshold A k i) (updatedRow k i)
                                      (compressedRow k i)) →
                              (diagonal_factor :
                                  ∀ (k : Fin p),
                                    @HighamBench.p15ComputedDenseLU b u (updatedColumn k k)
                                      (@HighamBench.p15MatrixBlock p b L k k) (@HighamBench.p15MatrixBlock p b U k k)) →
                                (lower_solve :
                                    ∀ (k i : Fin p),
                                      @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                        @HighamBench.p15ComputedRightTriangularSolve b u (compressedColumn k i)
                                          (@HighamBench.p15MatrixBlock p b L i k)
                                          (@HighamBench.p15MatrixBlock p b U k k)) →
                                  (upper_solve :
                                      ∀ (k i : Fin p),
                                        @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                          @HighamBench.p15ComputedLeftTriangularSolve b u (compressedRow k i)
                                            (@HighamBench.p15MatrixBlock p b L k k)
                                            (@HighamBench.p15MatrixBlock p b U k i)) →
                                    @HighamBench.P15CompletedUCFFactorization p b r threshold recompression u epsilon A
                                      L U
```

### D084: `HighamBench.P15CompletedUFCFactorization.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `b17af843d0388ba5782f551a1bd7dde642747b94755d8f88b3a5861368e2604d`

Type:

```lean
{p b r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (instHMul.hMul p b)} →
          (recompressionError : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) →
            HighamBench.p15RecompressionModel recompression threshold epsilon A recompressionError →
              (updatedColumn updatedRow rawLower rawUpper : Fin p → Fin p → HighamBench.P15Matrix b) →
                HighamBench.p15IsBlockLowerTriangular L →
                  HighamBench.p15IsBlockUpperTriangular U →
                    (∀ (k i : Fin p),
                        instLEFin.le k i →
                          HighamBench.p15ComputedBLRUpdate r u A L U recompressionError k i k (updatedColumn k i)) →
                      (∀ (k i : Fin p),
                          instLEFin.le k i →
                            HighamBench.p15ComputedBLRUpdate r u A L U recompressionError k k i (updatedRow k i)) →
                        (∀ (k : Fin p), Eq (updatedColumn k k) (updatedRow k k)) →
                          (∀ (k : Fin p),
                              HighamBench.p15ComputedDenseLU u (updatedColumn k k) (HighamBench.p15MatrixBlock L k k)
                                (HighamBench.p15MatrixBlock U k k)) →
                            (∀ (k i : Fin p),
                                instLTFin.lt k i →
                                  HighamBench.p15ComputedRightTriangularSolve u (updatedColumn k i) (rawLower i k)
                                    (HighamBench.p15MatrixBlock U k k)) →
                              (∀ (k i : Fin p),
                                  instLTFin.lt k i →
                                    HighamBench.p15ComputedLeftTriangularSolve u (updatedRow k i)
                                      (HighamBench.p15MatrixBlock L k k) (rawUpper k i)) →
                                (∀ (k : Fin p),
                                    Real.instLT.lt 0 (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock U k k))) →
                                  (∀ (k : Fin p),
                                      Real.instLT.lt 0 (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock L k k))) →
                                    ((k i : Fin p) →
                                        instLTFin.lt k i →
                                          HighamBench.P15BlockCompression epsilon
                                            (instHDiv.hDiv (HighamBench.p15BLRCompressionBase threshold A i k)
                                              (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock U k k)))
                                            (rawLower i k) (HighamBench.p15MatrixBlock L i k)) →
                                      ((k i : Fin p) →
                                          instLTFin.lt k i →
                                            HighamBench.P15BlockCompression epsilon
                                              (instHDiv.hDiv (HighamBench.p15BLRCompressionBase threshold A k i)
                                                (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock L k k)))
                                              (rawUpper k i) (HighamBench.p15MatrixBlock U k i)) →
                                        HighamBench.P15CompletedUFCFactorization r threshold recompression u epsilon A L
                                          U
```

Fully explicit type:

```lean
{p b r : Nat} →
  {threshold : HighamBench.P15BLRThreshold} →
    {recompression : HighamBench.P15BLRRecompression} →
      {u epsilon : Real} →
        {A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)} →
          (recompressionError : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) →
            (recompression_model :
                @HighamBench.p15RecompressionModel p b recompression threshold epsilon A recompressionError) →
              (updatedColumn updatedRow rawLower rawUpper : Fin p → Fin p → HighamBench.P15Matrix b) →
                (lower_triangular : @HighamBench.p15IsBlockLowerTriangular p b L) →
                  (upper_triangular : @HighamBench.p15IsBlockUpperTriangular p b U) →
                    (update_column :
                        ∀ (k i : Fin p),
                          @LE.le.{0} (Fin p) (@instLEFin p) k i →
                            @HighamBench.p15ComputedBLRUpdate p b r u A L U recompressionError k i k
                              (updatedColumn k i)) →
                      (update_row :
                          ∀ (k i : Fin p),
                            @LE.le.{0} (Fin p) (@instLEFin p) k i →
                              @HighamBench.p15ComputedBLRUpdate p b r u A L U recompressionError k k i
                                (updatedRow k i)) →
                        (diagonal_updates_agree :
                            ∀ (k : Fin p), @Eq.{1} (HighamBench.P15Matrix b) (updatedColumn k k) (updatedRow k k)) →
                          (diagonal_factor :
                              ∀ (k : Fin p),
                                @HighamBench.p15ComputedDenseLU b u (updatedColumn k k)
                                  (@HighamBench.p15MatrixBlock p b L k k) (@HighamBench.p15MatrixBlock p b U k k)) →
                            (lower_solve :
                                ∀ (k i : Fin p),
                                  @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                    @HighamBench.p15ComputedRightTriangularSolve b u (updatedColumn k i) (rawLower i k)
                                      (@HighamBench.p15MatrixBlock p b U k k)) →
                              (upper_solve :
                                  ∀ (k i : Fin p),
                                    @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                      @HighamBench.p15ComputedLeftTriangularSolve b u (updatedRow k i)
                                        (@HighamBench.p15MatrixBlock p b L k k) (rawUpper k i)) →
                                (lower_diagonal_scale_pos :
                                    ∀ (k : Fin p),
                                      @LT.lt.{0} Real Real.instLT
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        (@HighamBench.p15FrobNorm b (@HighamBench.p15MatrixBlock p b U k k))) →
                                  (upper_diagonal_scale_pos :
                                      ∀ (k : Fin p),
                                        @LT.lt.{0} Real Real.instLT
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                          (@HighamBench.p15FrobNorm b (@HighamBench.p15MatrixBlock p b L k k))) →
                                    (lower_compression :
                                        (k i : Fin p) →
                                          @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                            @HighamBench.P15BlockCompression b epsilon
                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                (@instHDiv.{0} Real
                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                (@HighamBench.p15BLRCompressionBase p b threshold A i k)
                                                (@HighamBench.p15FrobNorm b (@HighamBench.p15MatrixBlock p b U k k)))
                                              (rawLower i k) (@HighamBench.p15MatrixBlock p b L i k)) →
                                      (upper_compression :
                                          (k i : Fin p) →
                                            @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                              @HighamBench.P15BlockCompression b epsilon
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@HighamBench.p15BLRCompressionBase p b threshold A k i)
                                                  (@HighamBench.p15FrobNorm b (@HighamBench.p15MatrixBlock p b L k k)))
                                                (rawUpper k i) (@HighamBench.p15MatrixBlock p b U k i)) →
                                        @HighamBench.P15CompletedUFCFactorization p b r threshold recompression u
                                          epsilon A L U
```

### D085: `HighamBench.instReprP15TriangularSolveDirection.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `7c7d96d802478fd0bf6d0acaa82fe608e40f41316be07d45c944532713344ed5`

Type:

```lean
(motive : HighamBench.P15TriangularSolveDirection → Sort u_1) →
  (x : HighamBench.P15TriangularSolveDirection) →
    (Unit → motive HighamBench.P15TriangularSolveDirection.lower) →
      (Unit → motive HighamBench.P15TriangularSolveDirection.upper) → motive x
```

Fully explicit type:

```lean
(motive : HighamBench.P15TriangularSolveDirection → Sort u_1) →
  (x : HighamBench.P15TriangularSolveDirection) →
    (h_1 : (a : Unit) → motive HighamBench.P15TriangularSolveDirection.lower) →
      (h_2 : (a : Unit) → motive HighamBench.P15TriangularSolveDirection.upper) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => HighamBench.P15TriangularSolveDirection.casesOn x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D086: `HighamBench.p15BlockIndex._proof_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `theorem`
- Distance from target type: `6`
- Semantic SHA-256: `50fbbd3fed5168541821a0be60abb75d0dedeeb6b80a1cefb693b952f00050fa`

Type:

```lean
∀ {p b : Nat} (i : Fin p) (row : Fin b),
  Nat.instPreorder.lt (instHAdd.hAdd (instHMul.hMul i.val b) row.val) (instHMul.hMul p b)
```

Fully explicit type:

```lean
∀ {p b : Nat} (i : Fin p) (row : Fin b),
  @LT.lt.{0} Nat (@Preorder.toLT.{0} Nat Nat.instPreorder)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fin.val p i) b) (@Fin.val b row))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

### D087: `HighamBench.p15IsBlockLowerTriangular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `99f5c8c5e48af6d2cd2fe5d29d204dd444168ee995c9045c1f7a0a9f365b9771`

Type:

```lean
{p b : Nat} → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} → (L : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} L => ∀ (i j : Fin p), instLTFin.lt i j → Eq (HighamBench.p15MatrixBlock L i j) 0
```

### D088: `HighamBench.p15IsBlockUpperTriangular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `23004871ada397d4f70a364b015f381aa517c6fff957fcb31e835bd648dc4259`

Type:

```lean
{p b : Nat} → HighamBench.P15Matrix (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} → (U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} U => ∀ (i j : Fin p), instLTFin.lt j i → Eq (HighamBench.p15MatrixBlock U i j) 0
```

### D089: `HighamBench.p15LowRankKernelCost`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `c2fe5f62aae01995df6fd00f4964b121fe67637620e558fead3ee0984d93d978`

Type:

```lean
Nat → Nat → Real
```

Fully explicit type:

```lean
(b r : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r => instHAdd.hAdd b.cast (instHMul.hMul r.cast r.cast.sqrt)
```

### D090: `HighamBench.p15OnesVector`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `a2203fd1a41fe8de353c91f3b392b65b3cfa4e77158ccb30e3d89a34e69d7f2d`

Type:

```lean
(n : Nat) → HighamBench.P15Vector n
```

Fully explicit type:

```lean
(n : Nat) → HighamBench.P15Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n x => 1
```

### D091: `HighamBench.p15RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `f6707f2e526a146358f007d2349847963679a3556d53c05f30fd242f90c18238`

Type:

```lean
{m n p : Nat} → HighamBench.P15RectMatrix m n → HighamBench.P15RectMatrix n p → HighamBench.P15RectMatrix m p
```

Fully explicit type:

```lean
{m n p : Nat} →
  (A : HighamBench.P15RectMatrix m n) → (B : HighamBench.P15RectMatrix n p) → HighamBench.P15RectMatrix m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D092: `HighamBench.p15RectTranspose`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `5d09057ba3a21630e320ba9e9e5153de687ba08c185951b20149ba794d3de258`

Type:

```lean
{m n : Nat} → HighamBench.P15RectMatrix m n → HighamBench.P15RectMatrix n m
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P15RectMatrix m n) → HighamBench.P15RectMatrix n m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A j i => A i j
```

### D093: `HighamBench.p15TriangularPrecedes`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `180e72ab7e2b83815485864c04f73550b3146d55b0ba0dc5aa53e5d5207e1fed`

Type:

```lean
HighamBench.P15TriangularSolveDirection → {p : Nat} → Fin p → Fin p → Prop
```

Fully explicit type:

```lean
(direction : HighamBench.P15TriangularSolveDirection) → {p : Nat} → (i j : Fin p) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun direction {p} i j =>
  HighamBench.instReprP15TriangularSolveDirection.repr.match_1 (fun direction => Prop) direction
    (fun _ => instLTFin.lt j i) fun _ => instLTFin.lt i j
```

### D094: `HighamBench.p15TriangularPredecessors`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `ff629d092bf564cb4f6878df7bea0122acebac8902cfe13e7d5a277656188c82`

Type:

```lean
HighamBench.P15TriangularSolveDirection → {p : Nat} → Fin p → Finset (Fin p)
```

Fully explicit type:

```lean
(direction : HighamBench.P15TriangularSolveDirection) → {p : Nat} → (i : Fin p) → Finset.{0} (Fin p)
```

Definition body (one-level semantic boundary):

```lean
fun direction {p} i => Finset.filter (HighamBench.p15TriangularPrecedes direction i) Finset.univ
```

### D095: `HighamBench.p15VecHadamard`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `250df853e8b2977888389f94c979b348c242386ad7e0d0083df6609f3c9f25a6`

Type:

```lean
{n : Nat} → HighamBench.P15Vector n → HighamBench.P15Vector n → HighamBench.P15Vector n
```

Fully explicit type:

```lean
{n : Nat} → (x y : HighamBench.P15Vector n) → HighamBench.P15Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y i => instHMul.hMul (x i) (y i)
```

### D096: `HighamBench.p15VectorBlock`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `2212ed50a2f881fa449f39357d3d2124523f7d4309cb3ab0be3d4562f59f558c`

Type:

```lean
{p b : Nat} → HighamBench.P15Vector (instHMul.hMul p b) → Fin p → HighamBench.P15Vector b
```

Fully explicit type:

```lean
{p b : Nat} →
  (x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
    (i : Fin p) → HighamBench.P15Vector b
```

Definition body (one-level semantic boundary):

```lean
fun {p b} x i row => x (HighamBench.p15BlockIndex i row)
```

### D097: `HighamBench.P15BLRFactorizationAlgorithm.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `7`
- Semantic SHA-256: `94a9924a5133c1ce47df1dd7e810851a7a8a8d7066f2219e3c3912e374eb2511`

Type:

```lean
{motive : HighamBench.P15BLRFactorizationAlgorithm → Sort u} →
  motive HighamBench.P15BLRFactorizationAlgorithm.ufc →
    motive HighamBench.P15BLRFactorizationAlgorithm.ucf → (t : HighamBench.P15BLRFactorizationAlgorithm) → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15BLRFactorizationAlgorithm) → Sort u} →
  (ufc : motive HighamBench.P15BLRFactorizationAlgorithm.ufc) →
    (ucf : motive HighamBench.P15BLRFactorizationAlgorithm.ucf) →
      (t : HighamBench.P15BLRFactorizationAlgorithm) → motive t
```

### D098: `HighamBench.P15BlockCompression`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `7`
- Semantic SHA-256: `b39765279d0e57ef423fc04ef4d68b38c574ecdd4718bb8c3ab7b3b12847a03e`

Type:

```lean
{b : Nat} → Real → Real → HighamBench.P15Matrix b → HighamBench.P15Matrix b → Type
```

Fully explicit type:

```lean
{b : Nat} → (epsilon beta : Real) → (exact compressed : HighamBench.P15Matrix b) → Type
```

### D099: `HighamBench.P15TriangularSolveDirection.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `2d73782930849562771ac303e47a3463fda2be38408f4f13e7e4caa7c754e04a`

Type:

```lean
{motive : HighamBench.P15TriangularSolveDirection → Sort u} →
  (t : HighamBench.P15TriangularSolveDirection) →
    motive HighamBench.P15TriangularSolveDirection.lower →
      motive HighamBench.P15TriangularSolveDirection.upper → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15TriangularSolveDirection) → Sort u} →
  (t : HighamBench.P15TriangularSolveDirection) →
    (lower : motive HighamBench.P15TriangularSolveDirection.lower) →
      (upper : motive HighamBench.P15TriangularSolveDirection.upper) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t lower upper => HighamBench.P15TriangularSolveDirection.rec lower upper t
```

### D100: `HighamBench.p15BLRCompressionBase`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `c05e8a18a9508d719f410fe9a4a323436748ea1d9b36c9a8a2461043fc4e82d8`

Type:

```lean
{p b : Nat} → HighamBench.P15BLRThreshold → HighamBench.P15Matrix (instHMul.hMul p b) → Fin p → Fin p → Real
```

Fully explicit type:

```lean
{p b : Nat} →
  (threshold : HighamBench.P15BLRThreshold) →
    (A : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
      (i k : Fin p) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {p b} threshold A i k =>
  HighamBench.instReprP15BLRThreshold.repr.match_1 (fun threshold => Real) threshold
    (fun _ => HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock A i k)) fun _ => HighamBench.p15FrobNorm A
```

### D101: `HighamBench.p15ComputedBLRUpdate`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `41cbac7cf652f6be4ebc733ab7b5211fe050f0bd81c8614698bd5f2e4aa6fcaa`

Type:

```lean
{p b : Nat} →
  Nat →
    Real →
      HighamBench.P15Matrix (instHMul.hMul p b) →
        HighamBench.P15Matrix (instHMul.hMul p b) →
          HighamBench.P15Matrix (instHMul.hMul p b) →
            (Fin p → Fin p → Fin p → HighamBench.P15Matrix b) → Fin p → Fin p → Fin p → HighamBench.P15Matrix b → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (r : Nat) →
    (u : Real) →
      (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
        (recompressionError : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) →
          (k row col : Fin p) → (rounded : HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r u A L U recompressionError k row col rounded =>
  Exists fun product =>
    Exists fun productError =>
      Exists fun inputRelativeError =>
        Exists fun productRelativeError =>
          And
            (∀ (j : Fin p),
              SetLike.instMembership.mem (HighamBench.p15EarlierBlocks k) j →
                Eq (product j)
                  (instHAdd.hAdd
                    (instHAdd.hAdd
                      (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L row j) (HighamBench.p15MatrixBlock U j col))
                      (recompressionError row col j))
                    (productError j)))
            (And
              (∀ (j : Fin p),
                SetLike.instMembership.mem (HighamBench.p15EarlierBlocks k) j →
                  Real.instLE.le (HighamBench.p15FrobNorm (productError j))
                    (instHMul.hMul
                      (instHMul.hMul (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                        (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock L row j)))
                      (HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock U j col))))
              (And
                (∀ (row col : Fin b),
                  Real.instLE.le (abs (inputRelativeError row col)) (HighamBench.p15GammaReal p.cast u))
                (And
                  (∀ (j : Fin p),
                    SetLike.instMembership.mem (HighamBench.p15EarlierBlocks k) j →
                      ∀ (row col : Fin b),
                        Real.instLE.le (abs (productRelativeError j row col)) (HighamBench.p15GammaReal p.cast u))
                  (Eq rounded
                    (instHSub.hSub
                      (HighamBench.p15MatrixHadamard (HighamBench.p15MatrixBlock A row col)
                        (instHAdd.hAdd (HighamBench.p15OnesMatrix b) inputRelativeError))
                      ((HighamBench.p15EarlierBlocks k).sum fun j =>
                        HighamBench.p15MatrixHadamard (product j)
                          (instHAdd.hAdd (HighamBench.p15OnesMatrix b) (productRelativeError j))))))))
```

### D102: `HighamBench.p15ComputedDenseLU`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `9489312d3d4916286e8e6f13421df89d3e022f8c7cfbc0882a39ab7f2e750b09`

Type:

```lean
{b : Nat} → Real → HighamBench.P15Matrix b → HighamBench.P15Matrix b → HighamBench.P15Matrix b → Prop
```

Fully explicit type:

```lean
{b : Nat} → (u : Real) → (input L U : HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} u input L U =>
  Exists fun error =>
    And (Eq (HighamBench.p15MatMul L U) (instHAdd.hAdd input error))
      (Real.instLE.le (HighamBench.p15FrobNorm error)
        (instHMul.hMul (instHMul.hMul (HighamBench.p15GammaReal b.cast u) (HighamBench.p15FrobNorm L))
          (HighamBench.p15FrobNorm U)))
```

### D103: `HighamBench.p15ComputedLeftTriangularSolve`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `88ccbda15dcc294ce674c2734d11cc472df25c806160d70e475ec3cc225b68a7`

Type:

```lean
{b : Nat} → Real → HighamBench.P15Matrix b → HighamBench.P15Matrix b → HighamBench.P15Matrix b → Prop
```

Fully explicit type:

```lean
{b : Nat} → (u : Real) → (rhs T X : HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} u rhs T X =>
  Exists fun residual =>
    And (Eq (HighamBench.p15MatMul T X) (instHAdd.hAdd rhs residual))
      (Real.instLE.le (HighamBench.p15FrobNorm residual)
        (instHMul.hMul (instHMul.hMul (HighamBench.p15GammaReal b.cast u) (HighamBench.p15FrobNorm T))
          (HighamBench.p15FrobNorm X)))
```

### D104: `HighamBench.p15ComputedRightTriangularSolve`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `e9f91e2c8bc64fe6ff15ea34032bafe34e2cdf81a248997169fd66c0cf56a2a0`

Type:

```lean
{b : Nat} → Real → HighamBench.P15Matrix b → HighamBench.P15Matrix b → HighamBench.P15Matrix b → Prop
```

Fully explicit type:

```lean
{b : Nat} → (u : Real) → (rhs X T : HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} u rhs X T =>
  Exists fun residual =>
    And (Eq (HighamBench.p15MatMul X T) (instHAdd.hAdd rhs residual))
      (Real.instLE.le (HighamBench.p15FrobNorm residual)
        (instHMul.hMul (instHMul.hMul (HighamBench.p15GammaReal b.cast u) (HighamBench.p15FrobNorm T))
          (HighamBench.p15FrobNorm X)))
```

### D105: `HighamBench.p15RecompressionModel`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `49760032c70e8094ed8f959a410b29722b18fb40433c9d8066afab8bdb11ac13`

Type:

```lean
{p b : Nat} →
  HighamBench.P15BLRRecompression →
    HighamBench.P15BLRThreshold →
      Real → HighamBench.P15Matrix (instHMul.hMul p b) → (Fin p → Fin p → Fin p → HighamBench.P15Matrix b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (choice : HighamBench.P15BLRRecompression) →
    (threshold : HighamBench.P15BLRThreshold) →
      (epsilon : Real) →
        (A : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
          (error : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} choice threshold epsilon A error =>
  HighamBench.instReprP15BLRRecompression.repr.match_1 (fun choice => Prop) choice
    (fun _ => ∀ (i k j : Fin p), Eq (error i k j) 0) fun _ =>
    ∀ (row col j : Fin p),
      instLTFin.lt j row →
        instLTFin.lt j col →
          Real.instLE.le (HighamBench.p15FrobNorm (error row col j))
            (instHMul.hMul epsilon (HighamBench.p15BLRCompressionBase threshold A row col))
```

### D106: `HighamBench.P15BlockCompression.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `8`
- Semantic SHA-256: `a2a4a99e8005463015186023badadb98756eadd332be0e3c7040c61243909ff9`

Type:

```lean
{b : Nat} →
  {epsilon beta : Real} →
    {exact compressed : HighamBench.P15Matrix b} →
      (rank : Nat) →
        HighamBench.p15LowRankApproximation epsilon beta exact rank compressed →
          (∀ (ell : Nat) (candidate : HighamBench.P15Matrix b),
              HighamBench.p15LowRankApproximation epsilon beta exact ell candidate → instLENat.le rank ell) →
            (error : HighamBench.P15Matrix b) →
              Eq compressed (instHAdd.hAdd exact error) →
                Real.instLE.le (HighamBench.p15FrobNorm error) (instHMul.hMul epsilon beta) →
                  HighamBench.P15BlockCompression epsilon beta exact compressed
```

Fully explicit type:

```lean
{b : Nat} →
  {epsilon beta : Real} →
    {exact compressed : HighamBench.P15Matrix b} →
      (rank : Nat) →
        (rank_spec : @HighamBench.p15LowRankApproximation b epsilon beta exact rank compressed) →
          (rank_minimal :
              ∀ (ell : Nat) (candidate : HighamBench.P15Matrix b),
                @HighamBench.p15LowRankApproximation b epsilon beta exact ell candidate →
                  @LE.le.{0} Nat instLENat rank ell) →
            (error : HighamBench.P15Matrix b) →
              (compressed_eq :
                  @Eq.{1} (HighamBench.P15Matrix b) compressed
                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
                      (@instHAdd.{0} (HighamBench.P15Matrix b)
                        (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                      exact error)) →
                (error_le :
                    @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm b error)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon beta)) →
                  @HighamBench.P15BlockCompression b epsilon beta exact compressed
```

### D107: `HighamBench.P15TriangularSolveDirection.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `8`
- Semantic SHA-256: `516c254977beabe762211da28071bc73eaf1954ee249231f915228fe589bf21c`

Type:

```lean
{motive : HighamBench.P15TriangularSolveDirection → Sort u} →
  motive HighamBench.P15TriangularSolveDirection.lower →
    motive HighamBench.P15TriangularSolveDirection.upper → (t : HighamBench.P15TriangularSolveDirection) → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P15TriangularSolveDirection) → Sort u} →
  (lower : motive HighamBench.P15TriangularSolveDirection.lower) →
    (upper : motive HighamBench.P15TriangularSolveDirection.upper) →
      (t : HighamBench.P15TriangularSolveDirection) → motive t
```

### D108: `HighamBench.instReprP15BLRRecompression.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `027a317f61f4983bed8f78d418a5a7d35c981ffb5d7c065bbec4e81a11d90c64`

Type:

```lean
(motive : HighamBench.P15BLRRecompression → Sort u_1) →
  (x : HighamBench.P15BLRRecompression) →
    (Unit → motive HighamBench.P15BLRRecompression.without) →
      (Unit → motive HighamBench.P15BLRRecompression.with) → motive x
```

Fully explicit type:

```lean
(motive : HighamBench.P15BLRRecompression → Sort u_1) →
  (x : HighamBench.P15BLRRecompression) →
    (h_1 : (a : Unit) → motive HighamBench.P15BLRRecompression.without) →
      (h_2 : (a : Unit) → motive HighamBench.P15BLRRecompression.with) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => HighamBench.P15BLRRecompression.casesOn x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D109: `HighamBench.p15EarlierBlocks`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `5e57755c58a51d81b8ab942a17d06c83af5b98a5f1b248418b1ddfb1a001d914`

Type:

```lean
{p : Nat} → Fin p → Finset (Fin p)
```

Fully explicit type:

```lean
{p : Nat} → (k : Fin p) → Finset.{0} (Fin p)
```

Definition body (one-level semantic boundary):

```lean
fun {p} k => Finset.filter (fun j => instLTFin.lt j k) Finset.univ
```

### D110: `HighamBench.p15MatrixHadamard`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `8452f0ebcbbeaec37575a22c258d1f411709419662e73d4f68cb0b26721fd425`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → HighamBench.P15Matrix n → HighamBench.P15Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P15Matrix n) → HighamBench.P15Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => instHMul.hMul (A i j) (B i j)
```

### D111: `HighamBench.p15OnesMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `a4de0098b36b1e3e1c1be5de8ec1382c5f509ef5b6ed18c3dd9a3177da897caa`

Type:

```lean
(n : Nat) → HighamBench.P15Matrix n
```

Fully explicit type:

```lean
(n : Nat) → HighamBench.P15Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n x x_1 => 1
```

### D112: `HighamBench.p15LowRankApproximation`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `be719c16f25cabc1d9e8f295d0e5cbde11d6d20b71aa9ebf9fffebd0b84ac62b`

Type:

```lean
{b : Nat} → Real → Real → HighamBench.P15Matrix b → Nat → HighamBench.P15Matrix b → Prop
```

Fully explicit type:

```lean
{b : Nat} →
  (epsilon beta : Real) → (exact : HighamBench.P15Matrix b) → (k : Nat) → (candidate : HighamBench.P15Matrix b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} epsilon beta exact k candidate =>
  Exists fun X =>
    Exists fun Y =>
      And (HighamBench.p15OrthonormalColumns X)
        (And (Eq candidate (HighamBench.p15LowRankMatrix X Y))
          (Real.instLE.le (HighamBench.p15FrobNorm (instHSub.hSub candidate exact)) (instHMul.hMul epsilon beta)))
```

### D113: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D114: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D115: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D116: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D117: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HAdd.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HAdd α β γ] => self.1
```

### D118: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HMul.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D119: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Fully explicit type:

```lean
{α : Type u} → [self : LE.{u} α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D120: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add.{v} α] → Add.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D121: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D122: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Fully explicit type:

```lean
{R : Type u} → [NatCast.{u} R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D123: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

Fully explicit type:

```lean
∀ (n : Nat) [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n],
  Nat.AtLeastTwo
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D124: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ {n : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D125: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Fully explicit type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat.{u} α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D126: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add.{u_5} (M i)] → Add.{max u_1 u_5} ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D127: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D128: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`

Type:

```lean
Add Real
```

Fully explicit type:

```lean
Add.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ add := Real.add✝ }
```

### D129: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Fully explicit type:

```lean
LE.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D130: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`

Type:

```lean
Mul Real
```

Fully explicit type:

```lean
Mul.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D131: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Fully explicit type:

```lean
NatCast.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D132: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`

Type:

```lean
{α : Type u_1} → [Add α] → HAdd α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Add.{u_1} α] → HAdd.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Add α] => { hAdd := fun a b => inst.add a b }
```

### D133: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Mul.{u_1} α] → HMul.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D134: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `15abc50804fa78aecc5a807f82f13a6b67bcdff9061558426471fc4b606841aa`

Type:

```lean
Mul Nat
```

Fully explicit type:

```lean
Mul.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul }
```

### D135: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Fully explicit type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast.{u_1} R] → [Nat.AtLeastTwo n] → OfNat.{u_1} R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D136: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Fully explicit type:

```lean
(n : Nat) → OfNat.{0} Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D137: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Fully explicit type:

```lean
{G : Type u} → [self : DivInvMonoid.{u} G] → Div.{u} G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D138: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Fully explicit type:

```lean
(n : Nat) → Fintype.{0} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D139: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid.{u_3} M] → (s : Finset.{u_1} ι) → (f : ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D140: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Fully explicit type:

```lean
{α : Type u_1} → [Fintype.{u_1} α] → Finset.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D141: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HDiv.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D142: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HPow.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D143: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSub.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D144: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Fully explicit type:

```lean
{α : Type u} → [self : LT.{u} α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D145: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Fully explicit type:

```lean
(m : Type u) → (n : Type u') → (α : Type v) → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D146: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Fully explicit type:

```lean
{M : Type u_2} → [Monoid.{u_2} M] → Pow.{u_2, 0} M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D147: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Fully explicit type:

```lean
{α : Type u_1} → [One.{u_1} α] → OfNat.{u_1} α (nat_lit 1)
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D148: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Fully explicit type:

```lean
AddCommMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D149: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Fully explicit type:

```lean
AddGroup.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D150: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`

Type:

```lean
DivInvMonoid Real
```

Fully explicit type:

```lean
DivInvMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toMonoid := Real.instMonoid, toInv := Real.instInv, div := DivInvMonoid.div',
  div_eq_mul_inv := Real.instDivInvMonoid._proof_1, zpow := zpowRec, zpow_zero' := Real.instDivInvMonoid._proof_2,
  zpow_succ' := Real.instDivInvMonoid._proof_3, zpow_neg' := Real.instDivInvMonoid._proof_4 }
```

### D151: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Fully explicit type:

```lean
LT.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D152: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Fully explicit type:

```lean
Monoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D153: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Fully explicit type:

```lean
One.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D154: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

Type:

```lean
Sub Real
```

Fully explicit type:

```lean
Sub.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D155: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Fully explicit type:

```lean
Zero.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D156: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Fully explicit type:

```lean
Lattice.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D157: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Fully explicit type:

```lean
(x : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D158: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D159: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Fully explicit type:

```lean
{α : Type u_1} → [Zero.{u_1} α] → OfNat.{u_1} α (nat_lit 0)
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D160: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`

Type:

```lean
{α : Type u_1} → [Lattice α] → [AddGroup α] → α → α
```

Fully explicit type:

```lean
{α : Type u_1} → [Lattice.{u_1} α] → [AddGroup.{u_1} α] → (a : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Lattice α] [AddGroup α] a =>
  SemilatticeSup.toMax.max a (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg a)
```

### D161: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Div.{u_1} α] → HDiv.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D162: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow.{u_1, u_2} α β] → HPow.{u_1, u_2, u_1} α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D163: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Sub.{u_1} α] → HSub.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D164: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

Fully explicit type:

```lean
(n : Nat) → Prop
```

### D165: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Fully explicit type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D166: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Fully explicit type:

```lean
Add.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D167: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Fully explicit type:

```lean
LE.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D168: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Fully explicit type:

```lean
LT.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D169: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (a b : α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```

### D170: `Nonempty`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `37c79de378d44cb9dc334502b161bb140da0544579086aded2cf83ff99c462c7`

Type:

```lean
Sort u → Prop
```

Fully explicit type:

```lean
(α : Sort u) → Prop
```

### D171: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f9a0c1f5b41c8d9a8658798c73b295495f6dfbf0bd7d081817aec4f598bbfc46`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub α] → Sub (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub.{v} α] → Sub.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Sub α] => Pi.instSub
```

### D172: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Fully explicit type:

```lean
(n : Nat) → DecidableEq.{1} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```

### D173: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t e : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D174: `Fin.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `24fa4b4b6252c6619c7be20c8f88b00ad65adc22900c2f8cef15ab1ce2247816`

Type:

```lean
{n : Nat} → (a b : Fin n) → Decidable (instLTFin.lt a b)
```

Fully explicit type:

```lean
{n : Nat} → (a b : Fin n) → Decidable (@LT.lt.{0} (Fin n) (@instLTFin n) a b)
```

Definition body (one-level semantic boundary):

```lean
fun {n} a b => a.val.decLt b.val
```

### D175: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D176: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Fully explicit type:

```lean
{n : Nat} → (self : Fin n) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D177: `Pi.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Pi.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `9b57724ac626ed82a5e3b9060068391fe112af839994c2304c9990493e8e9fbc`

Type:

```lean
{I : Type u} → {f : I → Type v₁} → [(i : I) → AddCommMonoid (f i)] → AddCommMonoid ((i : I) → f i)
```

Fully explicit type:

```lean
{I : Type u} → {f : I → Type v₁} → [(i : I) → AddCommMonoid.{v₁} (f i)] → AddCommMonoid.{max u v₁} ((i : I) → f i)
```

Definition body (one-level semantic boundary):

```lean
fun {I} {f} [(i : I) → AddCommMonoid (f i)] =>
  let __src := Pi.addMonoid;
  have __src_1 := Pi.addCommSemigroup;
  { toAddMonoid := __src, add_comm := ⋯ }
```

### D178: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `5deaec32b4deac749a5db5453affea1938386e569380df7daeec26aee3cfd7c2`

Type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub (G i)] → Sub ((i : ι) → G i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub.{u_4} (G i)] → Sub.{max u_1 u_4} ((i : ι) → G i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {G} [(i : ι) → Sub (G i)] => { sub := fun f g i => instHSub.hSub (f i) (g i) }
```

### D179: `instLTFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `8cd15fdbb565335569354b3a92dd84648b7f425b56b502181ab2df382268eb87`

Type:

```lean
{n : Nat} → LT (Fin n)
```

Fully explicit type:

```lean
{n : Nat} → LT.{0} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { lt := fun a b => instLTNat.lt a.val b.val }
```

### D180: `Classical.propDecidable`

- Role: `external-frontier`
- Owner module: `Init.Classical`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `823c02cb7dcdb8ce30edfb12a2496dda0849f0773c65f9e91e289fab27c36c46`

Type:

```lean
(a : Prop) → Decidable a
```

Fully explicit type:

```lean
(a : Prop) → Decidable a
```

Definition body (one-level semantic boundary):

```lean
fun a => Classical.choice ⋯
```

### D181: `Finset`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Defs`
- Declaration kind: `inductive`
- Distance from target type: `7`
- Semantic SHA-256: `56a880af39b5f8e2e55560abe97637994d5830a3a7ed0adaa46c44b8c3eaf831`

Type:

```lean
Type u_4 → Type u_4
```

Fully explicit type:

```lean
(α : Type u_4) → Type u_4
```

### D182: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `cc2bad5c5cc6aa2b196abe33b9083d127ab69155f1189766c3500bb83412c7df`

Type:

```lean
{α : Type u_1} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α
```

Fully explicit type:

```lean
{α : Type u_1} → (p : α → Prop) → [@DecidablePred.{u_1 + 1} α p] → (s : Finset.{u_1} α) → Finset.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p [DecidablePred p] s => { val := Multiset.filter p s.val, nodup := ⋯ }
```

### D183: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero.{v} α] → Zero.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D184: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `5ea89e9915200c8782bc933f9184e28eb38f4c9610b00cf1310cc6e6435642d8`

Type:

```lean
Preorder Nat
```

Fully explicit type:

```lean
Preorder.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D185: `Preorder.toLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `8fcf5a8f5a8899408a8cdc310bc44f6f7b84a21905a114103fbc65083f779a43`

Type:

```lean
{α : Type u_2} → [self : Preorder α] → LT α
```

Fully explicit type:

```lean
{α : Type u_2} → [self : Preorder.{u_2} α] → LT.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Preorder α] => self.2
```

### D186: `instLEFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `ebac56428fb1bdf0060f322d2454b52c141188f43ac10a1e1c3b3437e05db596`

Type:

```lean
{n : Nat} → LE (Fin n)
```

Fully explicit type:

```lean
{n : Nat} → LE.{0} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { le := fun a b => instLENat.le a.val b.val }
```

### D187: `Finset.instSetLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `f43bd57c8a5e05334ba371d3e354fb5f1cd42a3177ae342e6448d872bd6428b6`

Type:

```lean
{α : Type u_1} → SetLike (Finset α) α
```

Fully explicit type:

```lean
{α : Type u_1} → SetLike.{u_1, u_1} (Finset.{u_1} α) α
```

Definition body (one-level semantic boundary):

```lean
fun {α} => { coe := fun s => setOf fun a => Multiset.instMembership.mem s.val a, coe_injective' := ⋯ }
```

### D188: `Matrix.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `6b893d81bc298230772e16cd0c8ddf7d2638ac0d6127094b06a1290d88f8c3ae`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [AddCommMonoid α] → AddCommMonoid (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {α : Type v} → [AddCommMonoid.{v} α] → AddCommMonoid.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [AddCommMonoid α] => Pi.addCommMonoid
```

### D189: `Membership.mem`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `941ea3346e809f919727c21bfcdeea342714a6b83f1cf871d648aa2cb14d6e9e`

Type:

```lean
{α : outParam (Type u)} → {γ : Type v} → [self : Membership α γ] → γ → α → Prop
```

Fully explicit type:

```lean
{α : outParam.{u + 2} (Type u)} → {γ : Type v} → [self : Membership.{u, v} α γ] → γ → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} γ [self : Membership α γ] => self.1
```

### D190: `SetLike.instMembership`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.SetLike.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `47a75450bbb51c4e8fdd9e8881cc3fa741dfb5f1f186d952055686e285c081e4`

Type:

```lean
{A : Type u_1} → {B : Type u_2} → [i : SetLike A B] → Membership B A
```

Fully explicit type:

```lean
{A : Type u_1} → {B : Type u_2} → [i : SetLike.{u_1, u_2} A B] → Membership.{u_2, u_1} B A
```

Definition body (one-level semantic boundary):

```lean
fun {A} {B} [i : SetLike A B] => { mem := fun p x => Set.instMembership.mem (i.coe p) x }
```

## Complete local imported sources

### `HighamBench.Core`

Path: `paper_bencmark/highambench/shared/HighamBench/Core.lean`
SHA-256: `8c84e05c04f4245e067d3a971dafa45bcfe92f55bbc24f2305964a8e2b9bd55a`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# HighamBench common core

This file is deliberately independent of the evaluated library. It contains
only the floating-point model and notation used by more than one benchmark
paper.
-/

namespace HighamBench

open scoped BigOperators

/-- The part of the usual floating-point model needed for ordinary summation. -/
structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

/-- Higham's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- The denominator in `gamma u n` is positive. -/
def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- Left-to-right recursive summation, with a one-element sum kept exact. -/
noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

end HighamBench
```

### `HighamBench.P15Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P15Definitions.lean`
SHA-256: `7b4ebd231e83ae2fe5a8b4669aeb91bc861178d7434c068bc288485a7406431b`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P15 definitions

Paper-scoped finite matrix notation for Higham and Mary's analysis of block
low-rank LU factorization and triangular solves.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P15 model. -/
abbrev P15Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite rectangular real matrix in the P15 model. -/
abbrev P15RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- A finite real vector in the P15 model. -/
abbrev P15Vector (n : ℕ) := Fin n → ℝ

/-- Exact multiplication of compatible finite rectangular matrices. -/
noncomputable def p15RectMatMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    P15RectMatrix m p :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Exact finite matrix multiplication. -/
noncomputable def p15MatMul {n : ℕ} (A B : P15Matrix n) : P15Matrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p15MatVec {n : ℕ} (A : P15Matrix n)
    (x : P15Vector n) : P15Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The paper's unsquared, unnormalized Frobenius norm for a rectangular
matrix, written explicitly as `sqrt (sum_i sum_j A_ij^2)`. -/
noncomputable def p15RectFrobNorm {m n : ℕ}
    (A : P15RectMatrix m n) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Square specialization of the Frobenius norm used throughout P15. -/
noncomputable def p15FrobNorm {n : ℕ} (A : P15Matrix n) : ℝ :=
  p15RectFrobNorm A

/-- Exact transpose of a finite rectangular matrix. -/
def p15RectTranspose {m n : ℕ} (A : P15RectMatrix m n) :
    P15RectMatrix n m :=
  fun j i ↦ A i j

/-- Exact action of a finite rectangular matrix on a vector. -/
noncomputable def p15RectMatVec {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The low-rank matrix `Atilde = X Y^T` in Lemma 3.1. -/
noncomputable def p15LowRankMatrix {b r : ℕ}
    (X Y : P15RectMatrix b r) : P15Matrix b :=
  p15RectMatMul X (p15RectTranspose Y)

/-- Column orthonormality `X^T X = I` in the real finite model. -/
def p15OrthonormalColumns {b r : ℕ} (X : P15RectMatrix b r) : Prop :=
  ∀ j k, (∑ i : Fin b, X i j * X i k) = if j = k then 1 else 0

/-- The paper's real-index gamma function `gamma_k = ku/(1-ku)`. -/
noncomputable def p15GammaReal (k u : ℝ) : ℝ :=
  k * u / (1 - k * u)

/-- The operation-count index `c = b + r^(3/2)` from Lemma 3.1. For a
nonnegative integer rank, `r^(3/2) = r * sqrt r`. -/
noncomputable def p15LowRankKernelCost (b r : ℕ) : ℝ :=
  (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)

/-- A proof-carrying finite execution of the ordered computation
`wHat = fl(Y^T v)` followed by `zHat = fl(X wHat)` in Lemma 3.1. The stage
perturbation fields are the standard matrix-vector backward-error interface
recalled in Lemma 2.1; the aggregate perturbations in (3.1) and (3.2) are not
assumed here. -/
structure P15LowRankMatVecExecution (b r : ℕ) where
  A : P15Matrix b
  X : P15RectMatrix b r
  Y : P15RectMatrix b r
  v : P15Vector b
  epsilon : ℝ
  beta : ℝ
  unitRoundoff : ℝ
  epsilon_pos : 0 < epsilon
  beta_pos : 0 < beta
  unitRoundoff_pos : 0 < unitRoundoff
  unitRoundoff_lt_epsilon : unitRoundoff < epsilon
  gamma_valid :
    p15LowRankKernelCost b r * unitRoundoff < 1
  x_orthonormal : p15OrthonormalColumns X
  truncError : P15Matrix b
  approximation_eq : p15LowRankMatrix X Y = A + truncError
  truncError_le : p15FrobNorm truncError ≤ epsilon * beta
  wHat : P15Vector r
  zHat : P15Vector b
  deltaY : P15RectMatrix b r
  deltaX : P15RectMatrix b r
  first_stage_eq :
    wHat = p15RectMatVec (p15RectTranspose (Y + deltaY)) v
  first_stage_error_le :
    p15RectFrobNorm deltaY ≤
      p15GammaReal (b : ℝ) unitRoundoff * p15RectFrobNorm Y
  second_stage_eq :
    zHat = p15RectMatVec (X + deltaX) wHat
  second_stage_error_le :
    p15RectFrobNorm deltaX ≤
      p15GammaReal (r : ℝ) unitRoundoff * p15RectFrobNorm X

/-- The explicit low-rank floating-point perturbation obtained by expanding
`(X + deltaX)(Y + deltaY)^T`. -/
noncomputable def p15LowRankRoundingError {b r : ℕ}
    (run : P15LowRankMatVecExecution b r) : P15Matrix b :=
  p15RectMatMul run.X (p15RectTranspose run.deltaY) +
    p15RectMatMul run.deltaX (p15RectTranspose run.Y) +
    p15RectMatMul run.deltaX (p15RectTranspose run.deltaY)

/-- The equation (3.2) perturbation: low-rank truncation plus the equation
(3.1) floating-point perturbation. -/
noncomputable def p15LowRankTotalError {b r : ℕ}
    (run : P15LowRankMatVecExecution b r) : P15Matrix b :=
  run.truncError + p15LowRankRoundingError run

/-- Euclidean vector norm used for the right-hand-side estimate in Theorem 4.5. -/
noncomputable def p15VecNorm {n : ℕ} (x : P15Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- The two BLR LU factorization orders covered by Theorem 4.5. -/
inductive P15BLRFactorizationAlgorithm where
  | ufc
  | ucf
  deriving DecidableEq, Repr

/-- The local and global low-rank threshold choices in Table 1. -/
inductive P15BLRThreshold where
  | local
  | global
  deriving DecidableEq, Repr

/-- Whether the factorization performs the intermediate recompressions from
Section 4.1.3. -/
inductive P15BLRRecompression where
  | without
  | with
  deriving DecidableEq, Repr

/-- The four exact values of `xi_p` in Table 1. -/
noncomputable def p15BLRXi (p : ℕ) (threshold : P15BLRThreshold)
    (recompression : P15BLRRecompression) : ℝ :=
  match recompression, threshold with
  | .without, .local => 1
  | .without, .global => p
  | .with, .local => p
  | .with, .global => (p : ℝ) ^ 2 / Real.sqrt 6

/-- The common operation-count index `c = b + 2*r^(3/2) + p` in Theorem
4.5. -/
noncomputable def p15BLRSolveCost (b p r : ℕ) : ℝ :=
  (b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)

/-- The smaller operation-count index `c = b + r^(3/2) + p` in Theorem 4.4. -/
noncomputable def p15BLRTriangularSolveCost (b p r : ℕ) : ℝ :=
  (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)

/-- Flatten a block-row and within-block row into an index of a `p*b` matrix. -/
def p15BlockIndex {p b : ℕ} (i : Fin p) (row : Fin b) : Fin (p * b) :=
  ⟨i.1 * b + row.1, by
    have hi : i.1 + 1 ≤ p := Nat.succ_le_iff.mpr i.2
    have hblock : (i.1 + 1) * b ≤ p * b := Nat.mul_le_mul_right b hi
    have hrow : i.1 * b + row.1 < (i.1 + 1) * b := by
      simpa [Nat.add_mul] using Nat.add_lt_add_left row.2 (i.1 * b)
    exact lt_of_lt_of_le hrow hblock⟩

/-- Extract one `b`-by-`b` block from a matrix of order `p*b`. -/
def p15MatrixBlock {p b : ℕ} (A : P15Matrix (p * b))
    (i j : Fin p) : P15Matrix b :=
  fun row col => A (p15BlockIndex i row) (p15BlockIndex j col)

/-- A `p*b` matrix whose off-diagonal blocks have rank at most `r`, represented
by uniformly padded `b`-by-`r` factors. -/
def p15IsBLRMatrix {p b : ℕ} (r : ℕ) (A : P15Matrix (p * b)) : Prop :=
  ∃ X Y : Fin p → Fin p → P15RectMatrix b r,
    ∀ i j, i ≠ j →
      p15MatrixBlock A i j = p15LowRankMatrix (X i j) (Y i j)

/-- Block lower-triangular shape. -/
def p15IsBlockLowerTriangular {p b : ℕ} (L : P15Matrix (p * b)) : Prop :=
  ∀ i j : Fin p, i < j → p15MatrixBlock L i j = 0

/-- Block upper-triangular shape. -/
def p15IsBlockUpperTriangular {p b : ℕ} (U : P15Matrix (p * b)) : Prop :=
  ∀ i j : Fin p, j < i → p15MatrixBlock U i j = 0

/-- Exact identity matrix in the P15 finite model. -/
def p15Identity (n : ℕ) : P15Matrix n :=
  fun i j => if i = j then 1 else 0

/-- Two-sided nonsingularity certificate for the input matrix. -/
def p15IsNonsingular {n : ℕ} (A : P15Matrix n) : Prop :=
  ∃ Ainv : P15Matrix n,
    p15MatMul Ainv A = p15Identity n ∧
      p15MatMul A Ainv = p15Identity n

/-- One scalar operation in the standard relative-error model (2.5). -/
def p15StandardRound (u exact rounded : ℝ) : Prop :=
  ∃ delta : ℝ, |delta| ≤ u ∧ rounded = exact * (1 + delta)

/-- The positive-precision regime inherited by Theorem 4.5. -/
def p15AdmissiblePrecision (c u epsilon : ℝ) : Prop :=
  0 < u ∧ 0 < epsilon ∧ u < epsilon ∧ 3 * c * u < 1

/-- A two-parameter remainder is uniformly `O(u*epsilon)` on a positive
neighborhood that contains the precision pair of the completed execution.
Separate radii avoid imposing an artificial upper bound on `epsilon`. -/
def p15IsBigOMixedAtRun (remainder : ℝ → ℝ → ℝ)
    (unitRoundoff epsilon : ℝ) : Prop :=
  ∃ C deltaU deltaEpsilon : ℝ,
    0 ≤ C ∧ 0 < deltaU ∧ 0 < deltaEpsilon ∧
      unitRoundoff ≤ deltaU ∧ epsilon ≤ deltaEpsilon ∧
      ∀ u epsilon' : ℝ,
        0 < u → 0 < epsilon' → u < epsilon' →
        u ≤ deltaU → epsilon' ≤ deltaEpsilon →
        |remainder u epsilon'| ≤ C * (u * epsilon')

/-- An `O(u^2)` remainder relative to a displayed problem scale, certified on
a positive neighborhood containing the completed execution's precision. -/
def p15IsBigOSquareRelativeAtRun
    (remainder scale : ℝ → ℝ → ℝ)
    (unitRoundoff epsilon : ℝ) : Prop :=
  ∃ C deltaU deltaEpsilon : ℝ,
    0 ≤ C ∧ 0 < deltaU ∧ 0 < deltaEpsilon ∧
      unitRoundoff ≤ deltaU ∧ epsilon ≤ deltaEpsilon ∧
      ∀ u epsilon' : ℝ,
        0 < u → 0 < epsilon' → u < epsilon' →
        u ≤ deltaU → epsilon' ≤ deltaEpsilon →
        0 ≤ scale u epsilon' →
        |remainder u epsilon'| ≤ C * u ^ 2 * scale u epsilon'

/-- The orientation convention in equation (2.3): lower blocks are `X*Y^T`
and upper blocks are `Y*X^T`. -/
noncomputable def p15OrientedLowRankBlock {p b k : ℕ} (i j : Fin p)
    (X Y : P15RectMatrix b k) : P15Matrix b :=
  if j < i then p15LowRankMatrix X Y else p15LowRankMatrix Y X

/-- A rank-`k` candidate satisfying equations (2.3)--(2.4), including the
truncated-SVD orthonormal-column convention. -/
def p15BLRBlockApproximation {p b : ℕ} (threshold : P15BLRThreshold)
    (epsilon : ℝ) (A : P15Matrix (p * b)) (i j : Fin p) (k : ℕ)
    (candidate : P15Matrix b) : Prop :=
  ∃ X Y : P15RectMatrix b k,
    p15OrthonormalColumns X ∧
      candidate = p15OrientedLowRankBlock i j X Y ∧
      p15FrobNorm (candidate - p15MatrixBlock A i j) ≤
        epsilon *
          match threshold with
          | .local => p15FrobNorm (p15MatrixBlock A i j)
          | .global => p15FrobNorm A

/-- Section 2.1's relation between a dense matrix `A` and its BLR
representation `Atilde`. Off-diagonal ranks may differ by block and each is
the minimum rank satisfying the selected local or global threshold. -/
def p15BLRRepresents {p b : ℕ} (threshold : P15BLRThreshold)
    (epsilon : ℝ) (A Atilde : P15Matrix (p * b)) : Prop :=
  (∀ i : Fin p, p15MatrixBlock Atilde i i = p15MatrixBlock A i i) ∧
    ∀ i j : Fin p, i ≠ j →
      ∃ k : ℕ,
        p15BLRBlockApproximation threshold epsilon A i j k
          (p15MatrixBlock Atilde i j) ∧
        ∀ ell : ℕ, ∀ candidate : P15Matrix b,
          p15BLRBlockApproximation threshold epsilon A i j ell candidate →
            k ≤ ell

/-- `r` is the least common off-diagonal rank bound of the computed factors,
which formalizes Section 4's maximum factor-rank convention. -/
def p15IsFactorBLRRank {p b : ℕ} (r : ℕ)
    (L U : P15Matrix (p * b)) : Prop :=
  p15IsBLRMatrix r L ∧ p15IsBLRMatrix r U ∧
    ∀ s : ℕ, p15IsBLRMatrix s L → p15IsBLRMatrix s U → r ≤ s

/-- Entrywise use of the relative-error model with one accumulated gamma
coefficient. -/
def p15EntrywiseStandardRound {m n : ℕ} (gamma : ℝ)
    (exact rounded : P15RectMatrix m n) : Prop :=
  ∀ i j, p15StandardRound gamma (exact i j) (rounded i j)

/-- Entrywise matrix product used in the accumulated update model (4.3). -/
def p15MatrixHadamard {n : ℕ} (A B : P15Matrix n) : P15Matrix n :=
  fun i j => A i j * B i j

/-- The all-ones matrix denoted by `J` in equation (4.3). -/
def p15OnesMatrix (n : ℕ) : P15Matrix n := fun _ _ => 1

/-- A rank-`k` truncated-SVD candidate for Assumption 2.1. -/
def p15LowRankApproximation {b : ℕ} (epsilon beta : ℝ)
    (exact : P15Matrix b) (k : ℕ) (candidate : P15Matrix b) : Prop :=
  ∃ X Y : P15RectMatrix b k,
    p15OrthonormalColumns X ∧
      candidate = p15LowRankMatrix X Y ∧
      p15FrobNorm (candidate - exact) ≤ epsilon * beta

/-- One minimum-rank truncated-SVD compression in Assumption 2.1. -/
structure P15BlockCompression {b : ℕ} (epsilon beta : ℝ)
    (exact compressed : P15Matrix b) where
  rank : ℕ
  rank_spec : p15LowRankApproximation epsilon beta exact rank compressed
  rank_minimal : ∀ ell : ℕ, ∀ candidate : P15Matrix b,
    p15LowRankApproximation epsilon beta exact ell candidate → rank ≤ ell
  error : P15Matrix b
  compressed_eq : compressed = exact + error
  error_le : p15FrobNorm error ≤ epsilon * beta

/-- The local or global unscaled threshold base attached to block `(i,k)`. -/
noncomputable def p15BLRCompressionBase {p b : ℕ}
    (threshold : P15BLRThreshold) (A : P15Matrix (p * b))
    (i k : Fin p) : ℝ :=
  match threshold with
  | .local => p15FrobNorm (p15MatrixBlock A i k)
  | .global => p15FrobNorm A

/-- The exact target-block update at factorization step `k` in lines 4 and 6
of Algorithms 1 and 2, including the optional intermediate-recompression
terms from Section 4.1.3. Every target block uses only factors from steps
strictly before `k`. -/
noncomputable def p15BLRUpdatedBlock {p b : ℕ}
    (A L U : P15Matrix (p * b))
    (recompressionError : Fin p → Fin p → Fin p → P15Matrix b)
    (k row col : Fin p) : P15Matrix b :=
  p15MatrixBlock A row col -
    ∑ j ∈ Finset.univ.filter (fun j : Fin p => j < k),
      (p15MatMul (p15MatrixBlock L row j) (p15MatrixBlock U j col) +
        recompressionError row col j)

/-- The recompression errors are absent in the `without` case and satisfy the
Section 4.1.3 threshold bound in the `with` case. A product can occur in the
update of target block `(row, col)` only when its factor index precedes both
target indices. -/
def p15RecompressionModel {p b : ℕ}
    (choice : P15BLRRecompression) (threshold : P15BLRThreshold)
    (epsilon : ℝ) (A : P15Matrix (p * b))
    (error : Fin p → Fin p → Fin p → P15Matrix b) : Prop :=
  match choice with
  | .without => ∀ i k j, error i k j = 0
  | .with => ∀ row col j, j < row → j < col →
      p15FrobNorm (error row col j) ≤
        epsilon * p15BLRCompressionBase threshold A row col

/-- Earlier factor blocks participating in iteration `k`. -/
noncomputable def p15EarlierBlocks {p : ℕ} (k : Fin p) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter (fun j => j < k)

/-- The cancellation-safe update relation (4.2)--(4.3). The input block and
each already-computed product receive separate componentwise perturbations;
the product computation has its own normwise error. -/
def p15ComputedBLRUpdate {p b : ℕ} (r : ℕ) (u : ℝ)
    (A L U : P15Matrix (p * b))
    (recompressionError : Fin p → Fin p → Fin p → P15Matrix b)
    (k row col : Fin p) (rounded : P15Matrix b) : Prop :=
  ∃ product : Fin p → P15Matrix b,
    ∃ productError : Fin p → P15Matrix b,
      ∃ inputRelativeError : P15Matrix b,
        ∃ productRelativeError : Fin p → P15Matrix b,
          (∀ j ∈ p15EarlierBlocks k,
            product j =
              p15MatMul (p15MatrixBlock L row j)
                  (p15MatrixBlock U j col) +
                recompressionError row col j + productError j) ∧
          (∀ j ∈ p15EarlierBlocks k,
            p15FrobNorm (productError j) ≤
              p15GammaReal (p15BLRSolveCost b p r) u *
                p15FrobNorm (p15MatrixBlock L row j) *
                p15FrobNorm (p15MatrixBlock U j col)) ∧
          (∀ row col,
            |inputRelativeError row col| ≤ p15GammaReal (p : ℝ) u) ∧
          (∀ j ∈ p15EarlierBlocks k, ∀ row col,
            |productRelativeError j row col| ≤ p15GammaReal (p : ℝ) u) ∧
          rounded =
            p15MatrixHadamard (p15MatrixBlock A row col)
                (p15OnesMatrix b + inputRelativeError) -
              ∑ j ∈ p15EarlierBlocks k,
                p15MatrixHadamard (product j)
                  (p15OnesMatrix b + productRelativeError j)

/-- Backward-error interface of Lemma 2.3 for one computed dense diagonal LU
factorization. -/
def p15ComputedDenseLU {b : ℕ} (u : ℝ)
    (input L U : P15Matrix b) : Prop :=
  ∃ error : P15Matrix b,
    p15MatMul L U = input + error ∧
      p15FrobNorm error ≤
        p15GammaReal (b : ℝ) u * p15FrobNorm L * p15FrobNorm U

/-- Residual interface of Lemma 2.2, equation (2.9), for a computed right
triangular solve `X*T = rhs`. -/
def p15ComputedRightTriangularSolve {b : ℕ} (u : ℝ)
    (rhs X T : P15Matrix b) : Prop :=
  ∃ residual : P15Matrix b,
    p15MatMul X T = rhs + residual ∧
      p15FrobNorm residual ≤
        p15GammaReal (b : ℝ) u * p15FrobNorm T * p15FrobNorm X

/-- Residual interface of Lemma 2.2, equation (2.9), for a computed left
triangular solve `T*X = rhs`. -/
def p15ComputedLeftTriangularSolve {b : ℕ} (u : ℝ)
    (rhs T X : P15Matrix b) : Prop :=
  ∃ residual : P15Matrix b,
    p15MatMul T X = rhs + residual ∧
      p15FrobNorm residual ≤
        p15GammaReal (b : ℝ) u * p15FrobNorm T * p15FrobNorm X

/-- A source-level execution of Algorithm 1. The exact update formulas feed
the factor step, and the off-diagonal factor blocks are compressed only after
they have been solved for. -/
structure P15CompletedUFCFactorization {p b : ℕ} (r : ℕ)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) where
  recompressionError : Fin p → Fin p → Fin p → P15Matrix b
  recompression_model :
    p15RecompressionModel recompression threshold epsilon A
      recompressionError
  updatedColumn : Fin p → Fin p → P15Matrix b
  updatedRow : Fin p → Fin p → P15Matrix b
  rawLower : Fin p → Fin p → P15Matrix b
  rawUpper : Fin p → Fin p → P15Matrix b
  lower_triangular : p15IsBlockLowerTriangular L
  upper_triangular : p15IsBlockUpperTriangular U
  update_column : ∀ k i, k ≤ i →
    p15ComputedBLRUpdate r u A L U recompressionError k i k
      (updatedColumn k i)
  update_row : ∀ k i, k ≤ i →
    p15ComputedBLRUpdate r u A L U recompressionError k k i
      (updatedRow k i)
  diagonal_updates_agree : ∀ k, updatedColumn k k = updatedRow k k
  diagonal_factor : ∀ k,
    p15ComputedDenseLU u (updatedColumn k k)
      (p15MatrixBlock L k k) (p15MatrixBlock U k k)
  lower_solve : ∀ k i, k < i →
    p15ComputedRightTriangularSolve u (updatedColumn k i)
      (rawLower i k) (p15MatrixBlock U k k)
  upper_solve : ∀ k i, k < i →
    p15ComputedLeftTriangularSolve u (updatedRow k i)
      (p15MatrixBlock L k k) (rawUpper k i)
  lower_diagonal_scale_pos : ∀ k, 0 < p15FrobNorm (p15MatrixBlock U k k)
  upper_diagonal_scale_pos : ∀ k, 0 < p15FrobNorm (p15MatrixBlock L k k)
  lower_compression : ∀ k i, k < i →
    P15BlockCompression epsilon
      (p15BLRCompressionBase threshold A i k /
        p15FrobNorm (p15MatrixBlock U k k))
      (rawLower i k) (p15MatrixBlock L i k)
  upper_compression : ∀ k i, k < i →
    P15BlockCompression epsilon
      (p15BLRCompressionBase threshold A k i /
        p15FrobNorm (p15MatrixBlock L k k))
      (rawUpper k i) (p15MatrixBlock U k i)

/-- A source-level execution of Algorithm 2. Updated off-diagonal blocks are
compressed before the factor solves, so the stored outputs come directly from
the factor step. -/
structure P15CompletedUCFFactorization {p b : ℕ} (r : ℕ)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) where
  recompressionError : Fin p → Fin p → Fin p → P15Matrix b
  recompression_model :
    p15RecompressionModel recompression threshold epsilon A
      recompressionError
  updatedColumn : Fin p → Fin p → P15Matrix b
  updatedRow : Fin p → Fin p → P15Matrix b
  compressedColumn : Fin p → Fin p → P15Matrix b
  compressedRow : Fin p → Fin p → P15Matrix b
  lower_triangular : p15IsBlockLowerTriangular L
  upper_triangular : p15IsBlockUpperTriangular U
  update_column : ∀ k i, k ≤ i →
    p15ComputedBLRUpdate r u A L U recompressionError k i k
      (updatedColumn k i)
  update_row : ∀ k i, k ≤ i →
    p15ComputedBLRUpdate r u A L U recompressionError k k i
      (updatedRow k i)
  diagonal_updates_agree : ∀ k, updatedColumn k k = updatedRow k k
  lower_compression : ∀ k i, k < i →
    P15BlockCompression epsilon (p15BLRCompressionBase threshold A i k)
      (updatedColumn k i) (compressedColumn k i)
  upper_compression : ∀ k i, k < i →
    P15BlockCompression epsilon (p15BLRCompressionBase threshold A k i)
      (updatedRow k i) (compressedRow k i)
  diagonal_factor : ∀ k,
    p15ComputedDenseLU u (updatedColumn k k)
      (p15MatrixBlock L k k) (p15MatrixBlock U k k)
  lower_solve : ∀ k i, k < i →
    p15ComputedRightTriangularSolve u (compressedColumn k i)
      (p15MatrixBlock L i k) (p15MatrixBlock U k k)
  upper_solve : ∀ k i, k < i →
    p15ComputedLeftTriangularSolve u (compressedRow k i)
      (p15MatrixBlock L k k) (p15MatrixBlock U k i)

/-- The raw completion trace of exactly one of the two factorization algorithms
named in Theorem 4.5. -/
def P15CompletedBLRFactorizationTrace {b p : ℕ}
    (r : ℕ)
    (algorithm : P15BLRFactorizationAlgorithm)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) : Prop :=
  match algorithm with
  | .ufc => Nonempty
      (P15CompletedUFCFactorization r threshold recompression u epsilon A L U)
  | .ucf => Nonempty
      (P15CompletedUCFFactorization r threshold recompression u epsilon A L U)

/-- The four source-level error contributions accumulated in the proofs of
Theorems 4.1--4.3. Their sum, rather than the final factorization perturbation,
is recorded: compression, rounded input, factor arithmetic, and the mixed
`u*epsilon` contribution remain distinct. -/
structure P15FactorizationLocalAnalysis {b p : ℕ} (r : ℕ)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) where
  compressionError : P15Matrix (p * b)
  inputRoundoffError : P15Matrix (p * b)
  factorRoundoffError : P15Matrix (p * b)
  mixedError : P15Matrix (p * b)
  mixedRemainder : ℝ → ℝ → ℝ
  decomposition_eq :
    A + (compressionError + inputRoundoffError + factorRoundoffError +
      mixedError) = p15MatMul L U
  compression_error_le :
    p15FrobNorm compressionError ≤
      p15BLRXi p threshold recompression * epsilon * p15FrobNorm A
  input_roundoff_error_le :
    p15FrobNorm inputRoundoffError ≤
      p15GammaReal (p : ℝ) u * p15FrobNorm A
  factor_roundoff_error_le :
    p15FrobNorm factorRoundoffError ≤
      p15GammaReal (p15BLRSolveCost b p r) u *
        p15FrobNorm L * p15FrobNorm U
  mixed_error_le : p15FrobNorm mixedError ≤ mixedRemainder u epsilon
  mixed_remainder_control :
    p15IsBigOMixedAtRun mixedRemainder u epsilon

/-- A completed factorization consists of an algorithm trace on the represented
BLR input and the separate error contributions derived in Theorems 4.1--4.3
relative to the dense matrix represented by that input. -/
def P15CompletedBLRFactorization {b p : ℕ}
    (r : ℕ)
    (algorithm : P15BLRFactorizationAlgorithm)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A Atilde L U : P15Matrix (p * b)) : Prop :=
  P15CompletedBLRFactorizationTrace r algorithm threshold recompression
      u epsilon Atilde L U ∧
    Nonempty
      (P15FactorizationLocalAnalysis r threshold recompression
        u epsilon A L U)

/-- The factorization perturbation established by Theorem 4.2 or 4.3 from a
completed factorization and its source-level error decomposition. -/
structure P15FactorizationBackwardError {b p : ℕ} (r : ℕ)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) where
  error : P15Matrix (p * b)
  remainder : ℝ → ℝ → ℝ
  remainder_control : p15IsBigOMixedAtRun remainder u epsilon
  factorization_eq : A + error = p15MatMul L U
  error_le :
    p15FrobNorm error ≤
      (p15BLRXi p threshold recompression * epsilon +
          p15GammaReal (p : ℝ) u) * p15FrobNorm A +
        p15GammaReal (p15BLRSolveCost b p r) u *
          p15FrobNorm L * p15FrobNorm U + remainder u epsilon

private theorem p15FrobNorm_eq_norm_internal {n : ℕ}
    (A : P15Matrix n) : p15FrobNorm A = ‖A‖ := by
  rw [p15FrobNorm, p15RectFrobNorm, Matrix.frobenius_norm_def]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]

private theorem p15FrobNorm_add_le_internal {n : ℕ}
    (A B : P15Matrix n) :
    p15FrobNorm (A + B) ≤ p15FrobNorm A + p15FrobNorm B := by
  simpa only [p15FrobNorm_eq_norm_internal] using norm_add_le A B

private theorem p15FrobNorm_add_four_le_internal {n : ℕ}
    (A B C D : P15Matrix n) :
    p15FrobNorm (A + B + C + D) ≤
      p15FrobNorm A + p15FrobNorm B + p15FrobNorm C + p15FrobNorm D := by
  calc
    p15FrobNorm (A + B + C + D) ≤
        p15FrobNorm (A + B + C) + p15FrobNorm D :=
      p15FrobNorm_add_le_internal _ _
    _ ≤ (p15FrobNorm (A + B) + p15FrobNorm C) + p15FrobNorm D := by
      gcongr
      exact p15FrobNorm_add_le_internal _ _
    _ ≤ ((p15FrobNorm A + p15FrobNorm B) + p15FrobNorm C) +
        p15FrobNorm D := by
      gcongr
      exact p15FrobNorm_add_le_internal _ _

/-- Theorems 4.2 and 4.3 as an actual consequence of a completed algorithm's
four-way error decomposition, rather than as fields of the final solve. -/
theorem p15CompletedBLRFactorization_backwardError {b p : ℕ} {r : ℕ}
    {algorithm : P15BLRFactorizationAlgorithm}
    {threshold : P15BLRThreshold} {recompression : P15BLRRecompression}
    {u epsilon : ℝ} {A Atilde L U : P15Matrix (p * b)}
    (completed : P15CompletedBLRFactorization r algorithm threshold
      recompression u epsilon A Atilde L U) :
    Nonempty
      (P15FactorizationBackwardError r threshold recompression
        u epsilon A L U) := by
  rcases completed.2 with ⟨analysis⟩
  let error : P15Matrix (p * b) :=
    analysis.compressionError + analysis.inputRoundoffError +
      analysis.factorRoundoffError + analysis.mixedError
  refine ⟨{
    error := error
    remainder := analysis.mixedRemainder
    remainder_control := analysis.mixed_remainder_control
    factorization_eq := by simpa [error] using analysis.decomposition_eq
    error_le := ?_
  }⟩
  have htriangle := p15FrobNorm_add_four_le_internal
    analysis.compressionError analysis.inputRoundoffError
    analysis.factorRoundoffError analysis.mixedError
  calc
    p15FrobNorm error ≤
        p15FrobNorm analysis.compressionError +
          p15FrobNorm analysis.inputRoundoffError +
          p15FrobNorm analysis.factorRoundoffError +
          p15FrobNorm analysis.mixedError := by
            simpa [error] using htriangle
    _ ≤ p15BLRXi p threshold recompression * epsilon * p15FrobNorm A +
          p15GammaReal (p : ℝ) u * p15FrobNorm A +
          (p15GammaReal (p15BLRSolveCost b p r) u *
            p15FrobNorm L * p15FrobNorm U) +
          analysis.mixedRemainder u epsilon := by
            exact add_le_add
              (add_le_add
                (add_le_add analysis.compression_error_le
                  analysis.input_roundoff_error_le)
                analysis.factor_roundoff_error_le)
              analysis.mixed_error_le
    _ = (p15BLRXi p threshold recompression * epsilon +
            p15GammaReal (p : ℝ) u) * p15FrobNorm A +
          p15GammaReal (p15BLRSolveCost b p r) u *
            p15FrobNorm L * p15FrobNorm U +
          analysis.mixedRemainder u epsilon := by ring

/-- Forward or backward block-substitution order. -/
inductive P15TriangularSolveDirection where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The exact right-hand side of one diagonal block solve after the already
computed block components have been subtracted. -/
noncomputable def p15TriangularResidual {p b : ℕ}
    (direction : P15TriangularSolveDirection)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b))
    (i : Fin p) (row : Fin b) : ℝ :=
  match direction with
  | .lower =>
      rhs (p15BlockIndex i row) -
        ∑ j ∈ Finset.univ.filter (fun j : Fin p => j < i),
          ∑ col : Fin b,
            p15MatrixBlock T i j row col * x (p15BlockIndex j col)
  | .upper =>
      rhs (p15BlockIndex i row) -
        ∑ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
          ∑ col : Fin b,
            p15MatrixBlock T i j row col * x (p15BlockIndex j col)

/-- Whether block `j` has already been computed when solving block `i`. -/
def p15TriangularPrecedes (direction : P15TriangularSolveDirection)
    {p : ℕ} (i j : Fin p) : Prop :=
  match direction with
  | .lower => j < i
  | .upper => i < j

/-- The block indices already available at one substitution step. -/
noncomputable def p15TriangularPredecessors
    (direction : P15TriangularSolveDirection) {p : ℕ}
    (i : Fin p) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter (p15TriangularPrecedes direction i)

/-- Extract one block from a vector of length `p*b`. -/
def p15VectorBlock {p b : ℕ} (x : P15Vector (p * b))
    (i : Fin p) : P15Vector b :=
  fun row => x (p15BlockIndex i row)

/-- Entrywise vector product used in equation (4.22). -/
def p15VecHadamard {n : ℕ} (x y : P15Vector n) : P15Vector n :=
  fun i => x i * y i

/-- The all-ones vector denoted by `e` in the proof of Theorem 4.4. -/
def p15OnesVector (n : ℕ) : P15Vector n := fun _ => 1

/-- A completed block triangular solve trace in the source order. It records
the separate low-rank product, summation, and diagonal-solve perturbations in
equation (4.22); it does not collapse a cancellation-prone residual into one
relative perturbation. -/
structure P15CompletedTriangularSolveTrace {p b : ℕ} (r : ℕ)
    (direction : P15TriangularSolveDirection) (u : ℝ)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b)) where
  triangular :
    match direction with
    | .lower => p15IsBlockLowerTriangular T
    | .upper => p15IsBlockUpperTriangular T
  diagonal_nonsingular : ∀ i, p15IsNonsingular (p15MatrixBlock T i i)
  productValue : Fin p → Fin p → P15Vector b
  productError : Fin p → Fin p → P15Matrix b
  rhsRelativeError : Fin p → P15Vector b
  productRelativeError : Fin p → Fin p → P15Vector b
  diagonalError : Fin p → P15Matrix b
  product_eq : ∀ i j, p15TriangularPrecedes direction i j →
    productValue i j =
      p15MatVec (p15MatrixBlock T i j + productError i j)
        (p15VectorBlock x j)
  product_error_le : ∀ i j, p15TriangularPrecedes direction i j →
    p15FrobNorm (productError i j) ≤
      p15GammaReal (p15LowRankKernelCost b r) u *
        p15FrobNorm (p15MatrixBlock T i j)
  rhs_relative_error_le : ∀ i row,
    |rhsRelativeError i row| ≤ p15GammaReal (p : ℝ) u
  product_relative_error_le : ∀ i j row,
    p15TriangularPrecedes direction i j →
      |productRelativeError i j row| ≤ p15GammaReal (p : ℝ) u
  diagonal_error_le : ∀ i,
    p15FrobNorm (diagonalError i) ≤
      p15GammaReal (b : ℝ) u * p15FrobNorm (p15MatrixBlock T i i)
  block_steps : ∀ i : Fin p,
    p15MatVec (p15MatrixBlock T i i + diagonalError i)
        (p15VectorBlock x i) =
      p15VecHadamard (p15VectorBlock rhs i)
          (p15OnesVector b + rhsRelativeError i) -
        ∑ j ∈ p15TriangularPredecessors direction i,
          p15VecHadamard (productValue i j)
            (p15OnesVector b + productRelativeError i j)

/-- The three distinct matrix-error contributions obtained by gathering
equation (4.22): low-rank/diagonal kernels, block summation, and their mixed
interaction. Their separate bounds are the inputs to the final gamma
composition in Theorem 4.4. -/
structure P15TriangularSolveLocalAnalysis {p b : ℕ} (r : ℕ)
    (direction : P15TriangularSolveDirection) (u : ℝ)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b)) where
  kernelError : P15Matrix (p * b)
  summationError : P15Matrix (p * b)
  interactionError : P15Matrix (p * b)
  rhsError : P15Vector (p * b)
  gathered_eq :
    p15MatVec (T + (kernelError + summationError + interactionError)) x =
      rhs + rhsError
  kernel_error_le :
    p15FrobNorm kernelError ≤
      p15GammaReal (p15LowRankKernelCost b r) u * p15FrobNorm T
  summation_error_le :
    p15FrobNorm summationError ≤
      p15GammaReal (p : ℝ) u * p15FrobNorm T
  interaction_error_le :
    p15FrobNorm interactionError ≤
      p15GammaReal (p15LowRankKernelCost b r) u *
        p15GammaReal (p : ℝ) u * p15FrobNorm T
  rhs_error_le :
    p15VecNorm rhsError ≤ p15GammaReal (p : ℝ) u * p15VecNorm rhs

/-- A completed triangular solve includes both its operation-level trace and
the three-way gathered form of equation (4.22). The aggregate equation-(4.21)
perturbation and its `gamma_c` bound are derived below. -/
def P15CompletedTriangularSolve {p b : ℕ} (r : ℕ)
    (direction : P15TriangularSolveDirection) (u : ℝ)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b)) : Prop :=
  Nonempty (P15CompletedTriangularSolveTrace r direction u T rhs x) ∧
    Nonempty (P15TriangularSolveLocalAnalysis r direction u T rhs x)

/-- The aggregate perturbations and bounds of Theorem 4.4. -/
structure P15TriangularSolveBackwardError {p b : ℕ} (r : ℕ)
    (direction : P15TriangularSolveDirection) (u : ℝ)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b)) where
  matrixError : P15Matrix (p * b)
  rhsError : P15Vector (p * b)
  solve_eq : p15MatVec (T + matrixError) x = rhs + rhsError
  matrix_error_le :
    p15FrobNorm matrixError ≤
      p15GammaReal (p15BLRTriangularSolveCost b p r) u * p15FrobNorm T
  rhs_error_le :
    p15VecNorm rhsError ≤ p15GammaReal (p : ℝ) u * p15VecNorm rhs

private theorem p15FrobNorm_add_three_le_internal {n : ℕ}
    (A B C : P15Matrix n) :
    p15FrobNorm (A + B + C) ≤
      p15FrobNorm A + p15FrobNorm B + p15FrobNorm C := by
  calc
    p15FrobNorm (A + B + C) ≤ p15FrobNorm (A + B) + p15FrobNorm C :=
      p15FrobNorm_add_le_internal _ _
    _ ≤ (p15FrobNorm A + p15FrobNorm B) + p15FrobNorm C := by
      gcongr
      exact p15FrobNorm_add_le_internal _ _

private theorem p15Gamma_add_le_internal {a d u : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hsum : (a + d) * u < 1) :
    p15GammaReal a u + p15GammaReal d u +
        p15GammaReal a u * p15GammaReal d u ≤
      p15GammaReal (a + d) u := by
  have hau : a * u < 1 := by
    nlinarith [mul_nonneg hd hu]
  have hdu : d * u < 1 := by
    nlinarith [mul_nonneg ha hu]
  have hau_pos : 0 < 1 - a * u := sub_pos.mpr hau
  have hdu_pos : 0 < 1 - d * u := sub_pos.mpr hdu
  have hsum_pos : 0 < 1 - (a + d) * u := sub_pos.mpr hsum
  rw [← sub_nonneg]
  have hidentity :
      p15GammaReal (a + d) u -
          (p15GammaReal a u + p15GammaReal d u +
            p15GammaReal a u * p15GammaReal d u) =
        (a * u) * (d * u) /
          ((1 - (a + d) * u) * (1 - a * u) * (1 - d * u)) := by
    unfold p15GammaReal
    field_simp [ne_of_gt hau_pos, ne_of_gt hdu_pos, ne_of_gt hsum_pos]
    ring
  rw [hidentity]
  exact div_nonneg
    (mul_nonneg (mul_nonneg ha hu) (mul_nonneg hd hu))
    (mul_nonneg (mul_pos hsum_pos hau_pos).le hdu_pos.le)

/-- Theorem 4.4 derived from the gathered equation-(4.22) contributions. -/
theorem p15CompletedTriangularSolve_backwardError {p b : ℕ} {r : ℕ}
    {direction : P15TriangularSolveDirection} {u : ℝ}
    {T : P15Matrix (p * b)} {rhs x : P15Vector (p * b)}
    (completed : P15CompletedTriangularSolve r direction u T rhs x)
    (hu : 0 ≤ u)
    (hvalid : p15BLRTriangularSolveCost b p r * u < 1) :
    Nonempty (P15TriangularSolveBackwardError r direction u T rhs x) := by
  rcases completed.2 with ⟨analysis⟩
  let matrixError : P15Matrix (p * b) :=
    analysis.kernelError + analysis.summationError + analysis.interactionError
  have hd_nonneg : 0 ≤ p15LowRankKernelCost b r := by
    unfold p15LowRankKernelCost
    positivity
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  have hcost :
      p15LowRankKernelCost b r + (p : ℝ) =
        p15BLRTriangularSolveCost b p r := by
    unfold p15LowRankKernelCost p15BLRTriangularSolveCost
    ring
  have hgamma :
      p15GammaReal (p15LowRankKernelCost b r) u +
          p15GammaReal (p : ℝ) u +
          p15GammaReal (p15LowRankKernelCost b r) u *
            p15GammaReal (p : ℝ) u ≤
        p15GammaReal (p15BLRTriangularSolveCost b p r) u := by
    rw [← hcost]
    exact p15Gamma_add_le_internal hd_nonneg hp_nonneg hu
      (by simpa [hcost] using hvalid)
  refine ⟨{
    matrixError := matrixError
    rhsError := analysis.rhsError
    solve_eq := by simpa [matrixError] using analysis.gathered_eq
    matrix_error_le := ?_
    rhs_error_le := analysis.rhs_error_le
  }⟩
  have hT_nonneg : 0 ≤ p15FrobNorm T := Real.sqrt_nonneg _
  calc
    p15FrobNorm matrixError ≤
        p15FrobNorm analysis.kernelError +
          p15FrobNorm analysis.summationError +
          p15FrobNorm analysis.interactionError := by
            simpa [matrixError] using p15FrobNorm_add_three_le_internal
              analysis.kernelError analysis.summationError
              analysis.interactionError
    _ ≤ (p15GammaReal (p15LowRankKernelCost b r) u +
            p15GammaReal (p : ℝ) u +
            p15GammaReal (p15LowRankKernelCost b r) u *
              p15GammaReal (p : ℝ) u) * p15FrobNorm T := by
          calc
            _ ≤ p15GammaReal (p15LowRankKernelCost b r) u *
                  p15FrobNorm T +
                p15GammaReal (p : ℝ) u * p15FrobNorm T +
                (p15GammaReal (p15LowRankKernelCost b r) u *
                  p15GammaReal (p : ℝ) u) * p15FrobNorm T := by
                    exact add_le_add
                      (add_le_add analysis.kernel_error_le
                        analysis.summation_error_le)
                      analysis.interaction_error_le
            _ = _ := by ring
    _ ≤ p15GammaReal (p15BLRTriangularSolveCost b p r) u *
        p15FrobNorm T := mul_le_mul_of_nonneg_right hgamma hT_nonneg

/-- One completed computation from Theorem 4.5. It contains only the
factorization and solve traces plus their source-level decompositions. The
aggregate Theorems 4.2--4.4 interfaces and the final system perturbations are
derived declarations, not fields of this record. -/
structure P15BLRLinearSolveExecution (b p r : ℕ) where
  block_size_pos : 0 < b
  block_count_pos : 0 < p
  rank_le_block_size : r ≤ b
  algorithm : P15BLRFactorizationAlgorithm
  threshold : P15BLRThreshold
  recompression : P15BLRRecompression
  A : P15Matrix (p * b)
  Atilde : P15Matrix (p * b)
  L : P15Matrix (p * b)
  U : P15Matrix (p * b)
  v : P15Vector (p * b)
  yHat : P15Vector (p * b)
  xHat : P15Vector (p * b)
  unitRoundoff : ℝ
  epsilon : ℝ
  precision : p15AdmissiblePrecision
    (p15BLRSolveCost b p r) unitRoundoff epsilon
  A_nonsingular : p15IsNonsingular A
  represents : p15BLRRepresents threshold epsilon A Atilde
  factor_rank : p15IsFactorBLRRank r L U
  factorization_completed :
    P15CompletedBLRFactorization r algorithm threshold recompression
      unitRoundoff epsilon A Atilde L U
  lower_completed :
    P15CompletedTriangularSolve r .lower unitRoundoff L v yHat
  upper_completed :
    P15CompletedTriangularSolve r .upper unitRoundoff U yHat xHat

/-- Exact matrix perturbation obtained by composing a perturbed factorization
with perturbed forward and backward substitutions. -/
noncomputable def p15ComposedMatrixError {n : ℕ}
    (factorError lowerError upperError L U : P15Matrix n) : P15Matrix n :=
  factorError + p15MatMul lowerError U +
    p15MatMul L upperError + p15MatMul lowerError upperError

/-- Exact right-hand-side perturbation obtained by composing the two
triangular solves. -/
noncomputable def p15ComposedRhsError {n : ℕ}
    (rhsLower rhsUpper : P15Vector n)
    (L lowerError : P15Matrix n) : P15Vector n :=
  rhsLower + p15MatVec L rhsUpper + p15MatVec lowerError rhsUpper

end HighamBench
```
