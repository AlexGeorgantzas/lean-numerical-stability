# Declaration dossier for P15-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
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
      rhsHigherOrderCoefficient ≤ 16 * c ^ 2 * run.unitRoundoff ^ 2
```

## Elaborated target type

```lean
∀ {b p r : Nat} (run : HighamBench.P15BLRLinearSolveExecution b p r),
  have c := HighamBench.p15BLRSolveCost b p r;
  have gammaP := HighamBench.p15GammaReal p.cast run.unitRoundoff;
  have gammaC := HighamBench.p15GammaReal c run.unitRoundoff;
  have gamma3C := HighamBench.p15GammaReal (instHMul.hMul 3 c) run.unitRoundoff;
  have xi := HighamBench.p15BLRXi p run.threshold run.recompression;
  have matrixError := HighamBench.p15ComposedMatrixError run.factorError run.lowerError run.upperError run.L run.U;
  have rhsError := HighamBench.p15ComposedRhsError run.lowerRhsError run.upperRhsError run.L run.lowerError;
  have solveScale :=
    instHMul.hMul (instHMul.hMul (HighamBench.p15FrobNorm run.L) (HighamBench.p15FrobNorm run.U))
      (HighamBench.p15VecNorm run.xHat);
  have rhsFiniteCoefficient :=
    instHDiv.hDiv (instHMul.hMul gammaP (instHPow.hPow (instHAdd.hAdd 1 gammaC) 2)) (instHSub.hSub 1 gammaP);
  have rhsHigherOrderCoefficient := instHSub.hSub rhsFiniteCoefficient gammaP;
  And (Eq (HighamBench.p15MatVec (instHAdd.hAdd run.A matrixError) run.xHat) (instHAdd.hAdd run.v rhsError))
    (And
      (Real.instLE.le (HighamBench.p15FrobNorm matrixError)
        (instHAdd.hAdd
          (instHAdd.hAdd
            (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi run.epsilon) gammaP) (HighamBench.p15FrobNorm run.A))
            (instHMul.hMul
              (instHMul.hMul (instHAdd.hAdd (instHMul.hMul 3 gammaC) (instHPow.hPow gammaC 2))
                (HighamBench.p15FrobNorm run.L))
              (HighamBench.p15FrobNorm run.U)))
          (instHMul.hMul (instHMul.hMul run.factorMixedConstant run.unitRoundoff) run.epsilon)))
      (And
        (Real.instLE.le (HighamBench.p15FrobNorm matrixError)
          (instHAdd.hAdd
            (instHAdd.hAdd
              (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi run.epsilon) gammaP) (HighamBench.p15FrobNorm run.A))
              (instHMul.hMul (instHMul.hMul gamma3C (HighamBench.p15FrobNorm run.L)) (HighamBench.p15FrobNorm run.U)))
            (instHMul.hMul (instHMul.hMul run.factorMixedConstant run.unitRoundoff) run.epsilon)))
        (And
          (Real.instLE.le (HighamBench.p15VecNorm rhsError)
            (instHAdd.hAdd (instHMul.hMul gammaP (HighamBench.p15VecNorm run.v))
              (instHMul.hMul rhsFiniteCoefficient solveScale)))
          (And
            (Real.instLE.le (HighamBench.p15VecNorm rhsError)
              (instHAdd.hAdd (instHMul.hMul gammaP (instHAdd.hAdd (HighamBench.p15VecNorm run.v) solveScale))
                (instHMul.hMul rhsHigherOrderCoefficient solveScale)))
            (And
              (Real.instLE.le (HighamBench.p15VecNorm rhsError)
                (instHAdd.hAdd (instHMul.hMul gammaP (instHAdd.hAdd (HighamBench.p15VecNorm run.v) solveScale))
                  (instHMul.hMul
                    (instHMul.hMul (instHMul.hMul 16 (instHPow.hPow c 2)) (instHPow.hPow run.unitRoundoff 2))
                    solveScale)))
              (And (Real.instLE.le 0 rhsHigherOrderCoefficient)
                (Real.instLE.le rhsHigherOrderCoefficient
                  (instHMul.hMul (instHMul.hMul 16 (instHPow.hPow c 2)) (instHPow.hPow run.unitRoundoff 2)))))))))
```

## Fully explicit elaborated target type

```lean
∀ {b p r : Nat} (run : HighamBench.P15BLRLinearSolveExecution b p r),
  have c : Real := HighamBench.p15BLRSolveCost b p r;
  have gammaP : Real :=
    HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p)
      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run);
  have gammaC : Real := HighamBench.p15GammaReal c (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run);
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
  have matrixError : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) :=
    @HighamBench.p15ComposedMatrixError (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
      (@HighamBench.P15BLRLinearSolveExecution.factorError b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.lowerError b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.upperError b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.L b p r run) (@HighamBench.P15BLRLinearSolveExecution.U b p r run);
  have rhsError : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) :=
    @HighamBench.p15ComposedRhsError (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
      (@HighamBench.P15BLRLinearSolveExecution.lowerRhsError b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.upperRhsError b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.L b p r run)
      (@HighamBench.P15BLRLinearSolveExecution.lowerError b p r run);
  have solveScale : Real :=
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@HighamBench.P15BLRLinearSolveExecution.L b p r run))
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@HighamBench.P15BLRLinearSolveExecution.U b p r run)))
      (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
        (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run));
  have rhsFiniteCoefficient : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaC)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaP);
  have rhsHigherOrderCoefficient : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) rhsFiniteCoefficient gammaP;
  And
    (@Eq.{1} (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
      (@HighamBench.p15MatVec (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
        (@HAdd.hAdd.{0, 0, 0}
          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
          (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
          (@instHAdd.{0} (HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
            (@Matrix.add.{0, 0, 0} (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
              (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real Real.instAdd))
          (@HighamBench.P15BLRLinearSolveExecution.A b p r run) matrixError)
        (@HighamBench.P15BLRLinearSolveExecution.xHat b p r run))
      (@HAdd.hAdd.{0, 0, 0}
        (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
        (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
        (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
        (@instHAdd.{0} (HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
          (@Pi.instAdd.{0, 0} (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
            (fun (a : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) => Real)
            fun (i : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) => Real.instAdd))
        (@HighamBench.P15BLRLinearSolveExecution.v b p r run) rhsError))
    (And
      (@LE.le.{0} Real Real.instLE
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) matrixError)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi
                  (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))
                gammaP)
              (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                (@HighamBench.P15BLRLinearSolveExecution.A b p r run)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 3)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    gammaC)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) gammaC
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                  (@HighamBench.P15BLRLinearSolveExecution.L b p r run)))
              (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                (@HighamBench.P15BLRLinearSolveExecution.U b p r run))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HighamBench.P15BLRLinearSolveExecution.factorMixedConstant b p r run)
              (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run))
            (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))))
      (And
        (@LE.le.{0} Real Real.instLE
          (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) matrixError)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi
                    (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))
                  gammaP)
                (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                  (@HighamBench.P15BLRLinearSolveExecution.A b p r run)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gamma3C
                  (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                    (@HighamBench.P15BLRLinearSolveExecution.L b p r run)))
                (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                  (@HighamBench.P15BLRLinearSolveExecution.U b p r run))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P15BLRLinearSolveExecution.factorMixedConstant b p r run)
                (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run))
              (@HighamBench.P15BLRLinearSolveExecution.epsilon b p r run))))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) rhsError)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                  (@HighamBench.P15BLRLinearSolveExecution.v b p r run)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) rhsFiniteCoefficient solveScale)))
          (And
            (@LE.le.{0} Real Real.instLE
              (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) rhsError)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                      (@HighamBench.P15BLRLinearSolveExecution.v b p r run))
                    solveScale))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) rhsHigherOrderCoefficient
                  solveScale)))
            (And
              (@LE.le.{0} Real Real.instLE
                (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) rhsError)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                        (@HighamBench.P15BLRLinearSolveExecution.v b p r run))
                      solveScale))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 16)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) c
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                        (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    solveScale)))
              (And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  rhsHigherOrderCoefficient)
                (@LE.le.{0} Real Real.instLE rhsHigherOrderCoefficient
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 16)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) c
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@HighamBench.P15BLRLinearSolveExecution.unitRoundoff b p r run)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))
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
- Semantic SHA-256: `8889e0f8a4669ed0cd57424126092fafa3c83a7d2b0c972e4299393236b4ca1b`

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
fun b p r self => self.8
```

### D004: `HighamBench.P15BLRLinearSolveExecution.U`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `72e2edc1824ede58b16dd9801f8e55d0fd4b2c7fa99fc377ac8a0e4db3f4c44d`

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

### D005: `HighamBench.P15BLRLinearSolveExecution.epsilon`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ba64bbf93196173b879bc33d039257541b18e5278f4cc61d39aba78715bbd81d`

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
fun b p r self => self.17
```

### D006: `HighamBench.P15BLRLinearSolveExecution.factorError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `69fd9afe85e8f4f847e578829e2163b2c3a8a7c9a4104ed5a804f8cf4276d474`

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
fun b p r self => self.25
```

### D007: `HighamBench.P15BLRLinearSolveExecution.factorMixedConstant`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `be03b321346e6ca9fa3b788a043d7ae06c9ad3ea91bb811ba400ec518cd8a730`

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
fun b p r self => self.29
```

### D008: `HighamBench.P15BLRLinearSolveExecution.lowerError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `755cb9bcd64e045b0860743ffb776cbdda4fae5b3fab965c3ce40e12cd4e3e1b`

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
fun b p r self => self.34
```

### D009: `HighamBench.P15BLRLinearSolveExecution.lowerRhsError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9f263326cb486bcc103e14eea6f46a0d28e2fc8163bd608743cc69836f350759`

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
fun b p r self => self.36
```

### D010: `HighamBench.P15BLRLinearSolveExecution.recompression`

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

### D011: `HighamBench.P15BLRLinearSolveExecution.threshold`

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

### D012: `HighamBench.P15BLRLinearSolveExecution.unitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2c4a32d527ecfec9fd79698c850e4bd8d61697a28950160e92cfa84647449784`

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
fun b p r self => self.18
```

### D013: `HighamBench.P15BLRLinearSolveExecution.upperError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fa63048819c1bf122c725c45133e24f5fbad8e0c641e60791cd920bb4eca3f9d`

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
fun b p r self => self.35
```

### D014: `HighamBench.P15BLRLinearSolveExecution.upperRhsError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bfec0bb5d7d739d90681a615f1bf650246ccdb6e010436b947c41d42a91eb3b8`

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
fun b p r self => self.37
```

### D015: `HighamBench.P15BLRLinearSolveExecution.v`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b7fb4b07451f50e579deaae76c1d3d5b5c2d0629650c12989942383a0abfce32`

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
fun b p r self => self.10
```

### D016: `HighamBench.P15BLRLinearSolveExecution.xHat`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `68c9b7c280de86b713e92a27bd7822eb9c5d41b70688dd1b35a973f9a68ee9e0`

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
fun b p r self => self.33
```

### D017: `HighamBench.P15Matrix`

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

### D018: `HighamBench.P15Vector`

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

### D019: `HighamBench.p15BLRSolveCost`

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

### D020: `HighamBench.p15BLRXi`

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

### D021: `HighamBench.p15ComposedMatrixError`

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

### D022: `HighamBench.p15ComposedRhsError`

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

### D023: `HighamBench.p15FrobNorm`

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

### D024: `HighamBench.p15GammaReal`

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

### D025: `HighamBench.p15MatVec`

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

### D026: `HighamBench.p15VecNorm`

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

### D027: `HighamBench.P15BLRLinearSolveExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `d9b199879bd01bae09459356e8214724cd607c8d132c0732aff8f4d2ee88a028`

Type:

```lean
{b p r : Nat} →
  instLTNat.lt 0 b →
    instLTNat.lt 0 p →
      instLENat.le r b →
        HighamBench.P15BLRFactorizationAlgorithm →
          (threshold : HighamBench.P15BLRThreshold) →
            (recompression : HighamBench.P15BLRRecompression) →
              (A L U : HighamBench.P15Matrix (instHMul.hMul p b)) →
                (v : HighamBench.P15Vector (instHMul.hMul p b)) →
                  HighamBench.p15IsNonsingular A →
                    HighamBench.p15IsBLRMatrix r A →
                      HighamBench.p15IsBLRMatrix r L →
                        HighamBench.p15IsBLRMatrix r U →
                          HighamBench.p15IsBlockLowerTriangular L →
                            HighamBench.p15IsBlockUpperTriangular U →
                              (epsilon unitRoundoff : Real) →
                                Real.instLT.lt 0 epsilon →
                                  Real.instLT.lt 0 unitRoundoff →
                                    Real.instLT.lt unitRoundoff epsilon →
                                      Real.instLT.lt
                                          (instHMul.hMul (instHMul.hMul 3 (HighamBench.p15BLRSolveCost b p r))
                                            unitRoundoff)
                                          1 →
                                        (factorCoreError factorMixedError factorError :
                                            HighamBench.P15Matrix (instHMul.hMul p b)) →
                                          Eq factorError (instHAdd.hAdd factorCoreError factorMixedError) →
                                            Eq (HighamBench.p15MatMul L U) (instHAdd.hAdd A factorError) →
                                              Real.instLE.le (HighamBench.p15FrobNorm factorCoreError)
                                                  (instHAdd.hAdd
                                                    (instHMul.hMul
                                                      (instHAdd.hAdd
                                                        (instHMul.hMul (HighamBench.p15BLRXi p threshold recompression)
                                                          epsilon)
                                                        (HighamBench.p15GammaReal p.cast unitRoundoff))
                                                      (HighamBench.p15FrobNorm A))
                                                    (instHMul.hMul
                                                      (instHMul.hMul
                                                        (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r)
                                                          unitRoundoff)
                                                        (HighamBench.p15FrobNorm L))
                                                      (HighamBench.p15FrobNorm U))) →
                                                (factorMixedConstant : Real) →
                                                  Real.instLE.le 0 factorMixedConstant →
                                                    Real.instLE.le (HighamBench.p15FrobNorm factorMixedError)
                                                        (instHMul.hMul (instHMul.hMul factorMixedConstant unitRoundoff)
                                                          epsilon) →
                                                      (yHat xHat : HighamBench.P15Vector (instHMul.hMul p b)) →
                                                        (lowerError upperError :
                                                            HighamBench.P15Matrix (instHMul.hMul p b)) →
                                                          (lowerRhsError upperRhsError :
                                                              HighamBench.P15Vector (instHMul.hMul p b)) →
                                                            Eq (HighamBench.p15MatVec (instHAdd.hAdd L lowerError) yHat)
                                                                (instHAdd.hAdd v lowerRhsError) →
                                                              Eq
                                                                  (HighamBench.p15MatVec (instHAdd.hAdd U upperError)
                                                                    xHat)
                                                                  (instHAdd.hAdd yHat upperRhsError) →
                                                                Real.instLE.le (HighamBench.p15FrobNorm lowerError)
                                                                    (instHMul.hMul
                                                                      (HighamBench.p15GammaReal
                                                                        (HighamBench.p15BLRSolveCost b p r)
                                                                        unitRoundoff)
                                                                      (HighamBench.p15FrobNorm L)) →
                                                                  Real.instLE.le (HighamBench.p15FrobNorm upperError)
                                                                      (instHMul.hMul
                                                                        (HighamBench.p15GammaReal
                                                                          (HighamBench.p15BLRSolveCost b p r)
                                                                          unitRoundoff)
                                                                        (HighamBench.p15FrobNorm U)) →
                                                                    Real.instLE.le
                                                                        (HighamBench.p15VecNorm lowerRhsError)
                                                                        (instHMul.hMul
                                                                          (HighamBench.p15GammaReal p.cast unitRoundoff)
                                                                          (HighamBench.p15VecNorm v)) →
                                                                      Real.instLE.le
                                                                          (HighamBench.p15VecNorm upperRhsError)
                                                                          (instHMul.hMul
                                                                            (HighamBench.p15GammaReal p.cast
                                                                              unitRoundoff)
                                                                            (HighamBench.p15VecNorm yHat)) →
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
              (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                (v : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                  (A_nonsingular :
                      @HighamBench.p15IsNonsingular
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) A) →
                    (A_is_blr : @HighamBench.p15IsBLRMatrix p b r A) →
                      (L_is_blr : @HighamBench.p15IsBLRMatrix p b r L) →
                        (U_is_blr : @HighamBench.p15IsBLRMatrix p b r U) →
                          (L_lower_triangular : @HighamBench.p15IsBlockLowerTriangular p b L) →
                            (U_upper_triangular : @HighamBench.p15IsBlockUpperTriangular p b U) →
                              (epsilon unitRoundoff : Real) →
                                (epsilon_pos :
                                    @LT.lt.{0} Real Real.instLT
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      epsilon) →
                                  (unitRoundoff_pos :
                                      @LT.lt.{0} Real Real.instLT
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        unitRoundoff) →
                                    (unitRoundoff_lt_epsilon : @LT.lt.{0} Real Real.instLT unitRoundoff epsilon) →
                                      (gamma_valid :
                                          @LT.lt.{0} Real Real.instLT
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@OfNat.ofNat.{0} Real (nat_lit 3)
                                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                                    (@Nat.instAtLeastTwoHAddOfNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      (@Nat.instNeZeroSucc
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1)))))))
                                                (HighamBench.p15BLRSolveCost b p r))
                                              unitRoundoff)
                                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                                        (factorCoreError factorMixedError factorError :
                                            HighamBench.P15Matrix
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                                          (factorError_eq :
                                              @Eq.{1}
                                                (HighamBench.P15Matrix
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                                factorError
                                                (@HAdd.hAdd.{0, 0, 0}
                                                  (HighamBench.P15Matrix
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                      b))
                                                  (HighamBench.P15Matrix
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                      b))
                                                  (HighamBench.P15Matrix
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                      b))
                                                  (@instHAdd.{0}
                                                    (HighamBench.P15Matrix
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b))
                                                    (@Matrix.add.{0, 0, 0}
                                                      (Fin
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p b))
                                                      (Fin
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p b))
                                                      Real Real.instAdd))
                                                  factorCoreError factorMixedError)) →
                                            (factorization_eq :
                                                @Eq.{1}
                                                  (HighamBench.P15Matrix
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                      b))
                                                  (@HighamBench.p15MatMul
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                      b)
                                                    L U)
                                                  (@HAdd.hAdd.{0, 0, 0}
                                                    (HighamBench.P15Matrix
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b))
                                                    (HighamBench.P15Matrix
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b))
                                                    (HighamBench.P15Matrix
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b))
                                                    (@instHAdd.{0}
                                                      (HighamBench.P15Matrix
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p b))
                                                      (@Matrix.add.{0, 0, 0}
                                                        (Fin
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                        (Fin
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                        Real Real.instAdd))
                                                    A factorError)) →
                                              (factorCoreError_le :
                                                  @LE.le.{0} Real Real.instLE
                                                    (@HighamBench.p15FrobNorm
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b)
                                                      factorCoreError)
                                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                      (@instHAdd.{0} Real Real.instAdd)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (HighamBench.p15BLRXi p threshold recompression) epsilon)
                                                          (HighamBench.p15GammaReal
                                                            (@Nat.cast.{0} Real Real.instNatCast p) unitRoundoff))
                                                        (@HighamBench.p15FrobNorm
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                          A))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r)
                                                            unitRoundoff)
                                                          (@HighamBench.p15FrobNorm
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat) p b)
                                                            L))
                                                        (@HighamBench.p15FrobNorm
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                          U)))) →
                                                (factorMixedConstant : Real) →
                                                  (factorMixedConstant_nonneg :
                                                      @LE.le.{0} Real Real.instLE
                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                          (@Zero.toOfNat0.{0} Real Real.instZero))
                                                        factorMixedConstant) →
                                                    (factorMixedError_le :
                                                        @LE.le.{0} Real Real.instLE
                                                          (@HighamBench.p15FrobNorm
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat) p b)
                                                            factorMixedError)
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul) factorMixedConstant
                                                              unitRoundoff)
                                                            epsilon)) →
                                                      (yHat xHat :
                                                          HighamBench.P15Vector
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat) p b)) →
                                                        (lowerError upperError :
                                                            HighamBench.P15Matrix
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat) p b)) →
                                                          (lowerRhsError upperRhsError :
                                                              HighamBench.P15Vector
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat) p b)) →
                                                            (lowerSolve_eq :
                                                                @Eq.{1}
                                                                  (HighamBench.P15Vector
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) p b))
                                                                  (@HighamBench.p15MatVec
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) p b)
                                                                    (@HAdd.hAdd.{0, 0, 0}
                                                                      (HighamBench.P15Matrix
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (HighamBench.P15Matrix
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (HighamBench.P15Matrix
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (@instHAdd.{0}
                                                                        (HighamBench.P15Matrix
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                                        (@Matrix.add.{0, 0, 0}
                                                                          (Fin
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b))
                                                                          (Fin
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b))
                                                                          Real Real.instAdd))
                                                                      L lowerError)
                                                                    yHat)
                                                                  (@HAdd.hAdd.{0, 0, 0}
                                                                    (HighamBench.P15Vector
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b))
                                                                    (HighamBench.P15Vector
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b))
                                                                    (HighamBench.P15Vector
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b))
                                                                    (@instHAdd.{0}
                                                                      (HighamBench.P15Vector
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (@Pi.instAdd.{0, 0}
                                                                        (Fin
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                                        (fun
                                                                            (a :
                                                                              Fin
                                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHMul.{0} Nat instMulNat) p
                                                                                  b)) =>
                                                                          Real)
                                                                        fun
                                                                          (i :
                                                                            Fin
                                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                (@instHMul.{0} Nat instMulNat) p b)) =>
                                                                        Real.instAdd))
                                                                    v lowerRhsError)) →
                                                              (upperSolve_eq :
                                                                  @Eq.{1}
                                                                    (HighamBench.P15Vector
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b))
                                                                    (@HighamBench.p15MatVec
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b)
                                                                      (@HAdd.hAdd.{0, 0, 0}
                                                                        (HighamBench.P15Matrix
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                                        (HighamBench.P15Matrix
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                                        (HighamBench.P15Matrix
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                                        (@instHAdd.{0}
                                                                          (HighamBench.P15Matrix
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b))
                                                                          (@Matrix.add.{0, 0, 0}
                                                                            (Fin
                                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                (@instHMul.{0} Nat instMulNat) p b))
                                                                            (Fin
                                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                (@instHMul.{0} Nat instMulNat) p b))
                                                                            Real Real.instAdd))
                                                                        U upperError)
                                                                      xHat)
                                                                    (@HAdd.hAdd.{0, 0, 0}
                                                                      (HighamBench.P15Vector
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (HighamBench.P15Vector
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (HighamBench.P15Vector
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b))
                                                                      (@instHAdd.{0}
                                                                        (HighamBench.P15Vector
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b))
                                                                        (@Pi.instAdd.{0, 0}
                                                                          (Fin
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b))
                                                                          (fun
                                                                              (a :
                                                                                Fin
                                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHMul.{0} Nat instMulNat) p
                                                                                    b)) =>
                                                                            Real)
                                                                          fun
                                                                            (i :
                                                                              Fin
                                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHMul.{0} Nat instMulNat) p
                                                                                  b)) =>
                                                                          Real.instAdd))
                                                                      yHat upperRhsError)) →
                                                                (lowerError_le :
                                                                    @LE.le.{0} Real Real.instLE
                                                                      (@HighamBench.p15FrobNorm
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b)
                                                                        lowerError)
                                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                        (@instHMul.{0} Real Real.instMul)
                                                                        (HighamBench.p15GammaReal
                                                                          (HighamBench.p15BLRSolveCost b p r)
                                                                          unitRoundoff)
                                                                        (@HighamBench.p15FrobNorm
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                                          L))) →
                                                                  (upperError_le :
                                                                      @LE.le.{0} Real Real.instLE
                                                                        (@HighamBench.p15FrobNorm
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                                          upperError)
                                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                          (@instHMul.{0} Real Real.instMul)
                                                                          (HighamBench.p15GammaReal
                                                                            (HighamBench.p15BLRSolveCost b p r)
                                                                            unitRoundoff)
                                                                          (@HighamBench.p15FrobNorm
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b)
                                                                            U))) →
                                                                    (lowerRhsError_le :
                                                                        @LE.le.{0} Real Real.instLE
                                                                          (@HighamBench.p15VecNorm
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b)
                                                                            lowerRhsError)
                                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                            (@instHMul.{0} Real Real.instMul)
                                                                            (HighamBench.p15GammaReal
                                                                              (@Nat.cast.{0} Real Real.instNatCast p)
                                                                              unitRoundoff)
                                                                            (@HighamBench.p15VecNorm
                                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                (@instHMul.{0} Nat instMulNat) p b)
                                                                              v))) →
                                                                      (upperRhsError_le :
                                                                          @LE.le.{0} Real Real.instLE
                                                                            (@HighamBench.p15VecNorm
                                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                (@instHMul.{0} Nat instMulNat) p b)
                                                                              upperRhsError)
                                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                              (@instHMul.{0} Real Real.instMul)
                                                                              (HighamBench.p15GammaReal
                                                                                (@Nat.cast.{0} Real Real.instNatCast p)
                                                                                unitRoundoff)
                                                                              (@HighamBench.p15VecNorm
                                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHMul.{0} Nat instMulNat) p b)
                                                                                yHat))) →
                                                                        HighamBench.P15BLRLinearSolveExecution b p r
```

### D028: `HighamBench.P15BLRRecompression`

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

### D029: `HighamBench.P15BLRThreshold`

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

### D030: `HighamBench.p15BLRSolveCost._proof_1`

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

### D031: `HighamBench.p15BLRXi._proof_1`

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

### D032: `HighamBench.p15BLRXi.match_1`

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

### D033: `HighamBench.p15MatMul`

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

### D034: `HighamBench.p15RectFrobNorm`

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

### D035: `HighamBench.P15BLRFactorizationAlgorithm`

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

### D036: `HighamBench.P15BLRRecompression.casesOn`

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

### D037: `HighamBench.P15BLRRecompression.with`

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

### D038: `HighamBench.P15BLRRecompression.without`

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

### D039: `HighamBench.P15BLRThreshold.casesOn`

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

### D040: `HighamBench.P15BLRThreshold.global`

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

### D041: `HighamBench.P15BLRThreshold.local`

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

### D042: `HighamBench.P15RectMatrix`

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

### D043: `HighamBench.p15IsBLRMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D044: `HighamBench.p15IsBlockLowerTriangular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D045: `HighamBench.p15IsBlockUpperTriangular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D046: `HighamBench.p15IsNonsingular`

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

### D047: `HighamBench.P15BLRFactorizationAlgorithm.ucf`

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

### D048: `HighamBench.P15BLRFactorizationAlgorithm.ufc`

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

### D049: `HighamBench.P15BLRRecompression.rec`

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

### D050: `HighamBench.P15BLRThreshold.rec`

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

### D051: `HighamBench.p15Identity`

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

### D052: `HighamBench.p15LowRankMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D053: `HighamBench.p15MatrixBlock`

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

### D054: `HighamBench.p15BlockIndex`

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

### D055: `HighamBench.p15RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D056: `HighamBench.p15RectTranspose`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D057: `HighamBench.p15BlockIndex._proof_1`

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

### D058: `And`

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

### D059: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D060: `Eq`

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

### D061: `Fin`

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

### D062: `HAdd.hAdd`

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

### D063: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D064: `HMul.hMul`

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

### D065: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D066: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D067: `LE.le`

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

### D068: `Matrix.add`

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

### D069: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D070: `Nat`

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

### D071: `Nat.cast`

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

### D072: `Nat.instAtLeastTwoHAddOfNat`

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

### D073: `Nat.instNeZeroSucc`

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

### D074: `OfNat.ofNat`

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

### D075: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D076: `Pi.instAdd`

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

### D077: `Real`

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

### D078: `Real.instAdd`

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

### D079: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D080: `Real.instLE`

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

### D081: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D082: `Real.instMul`

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

### D083: `Real.instNatCast`

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

### D084: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D085: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D086: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D087: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D088: `instHAdd`

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

### D089: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D090: `instHMul`

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

### D091: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D092: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D093: `instMulNat`

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

### D094: `instOfNatAtLeastTwo`

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

### D095: `instOfNatNat`

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

### D096: `Fin.fintype`

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

### D097: `Finset.sum`

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

### D098: `Finset.univ`

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

### D099: `Matrix`

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

### D100: `Real.instAddCommMonoid`

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

### D101: `Real.sqrt`

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

### D102: `Unit`

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

### D103: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D104: `Nat.AtLeastTwo`

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

### D105: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D106: `Unit.unit`

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

### D107: `instAddNat`

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

### D108: `instLENat`

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

### D109: `instLTNat`

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

### D110: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D111: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D112: `Ne`

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

### D113: `instLTFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D114: `instDecidableEqFin`

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

### D115: `ite`

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

### D116: `Fin.mk`

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

### D117: `Fin.val`

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

### D118: `Nat.instPreorder`

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

### D119: `Preorder.toLT`

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
