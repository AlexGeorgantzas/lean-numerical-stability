# Declaration dossier for P15-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
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
                  rhsRemainder u epsilon
```

## Elaborated target type

```lean
∀ {b p r : Nat} (run : HighamBench.P15BLRLinearSolveFamily b p r),
  have c := HighamBench.p15BLRSolveCost b p r;
  have xi := HighamBench.p15BLRXi p run.threshold run.recompression;
  have solveScale := fun u epsilon =>
    instHMul.hMul
      (instHMul.hMul (HighamBench.p15FrobNorm (run.L u epsilon)) (HighamBench.p15FrobNorm (run.U u epsilon)))
      (HighamBench.p15VecNorm (run.xHat u epsilon));
  Exists fun matrixError =>
    Exists fun rhsError =>
      Exists fun rhsRemainder =>
        And
          (Eq matrixError fun u epsilon =>
            HighamBench.p15ComposedMatrixError (run.factorError u epsilon) (run.lowerError u epsilon)
              (run.upperError u epsilon) (run.L u epsilon) (run.U u epsilon))
          (And
            (Eq rhsError fun u epsilon =>
              HighamBench.p15ComposedRhsError (run.lowerRhsError u epsilon) (run.upperRhsError u epsilon)
                (run.L u epsilon) (run.lowerError u epsilon))
            (And (HighamBench.p15IsBigOMixedAtZero run.factorRemainder)
              (And (HighamBench.p15IsBigOSquareRelativeAtZero rhsRemainder solveScale)
                (∀ (u epsilon : Real),
                  HighamBench.p15AdmissiblePrecision c u epsilon →
                    have gammaP := HighamBench.p15GammaReal p.cast u;
                    have gamma3C := HighamBench.p15GammaReal (instHMul.hMul 3 c) u;
                    And (Real.instLE.le 0 (run.factorRemainder u epsilon))
                      (And (Real.instLE.le 0 (rhsRemainder u epsilon))
                        (And
                          (Eq (HighamBench.p15MatVec (instHAdd.hAdd run.A (matrixError u epsilon)) (run.xHat u epsilon))
                            (instHAdd.hAdd run.v (rhsError u epsilon)))
                          (And
                            (Real.instLE.le (HighamBench.p15FrobNorm (matrixError u epsilon))
                              (instHAdd.hAdd
                                (instHAdd.hAdd
                                  (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi epsilon) gammaP)
                                    (HighamBench.p15FrobNorm run.A))
                                  (instHMul.hMul (instHMul.hMul gamma3C (HighamBench.p15FrobNorm (run.L u epsilon)))
                                    (HighamBench.p15FrobNorm (run.U u epsilon))))
                                (run.factorRemainder u epsilon)))
                            (Real.instLE.le (HighamBench.p15VecNorm (rhsError u epsilon))
                              (instHAdd.hAdd
                                (instHMul.hMul gammaP
                                  (instHAdd.hAdd (HighamBench.p15VecNorm run.v) (solveScale u epsilon)))
                                (rhsRemainder u epsilon))))))))))
```

## Fully explicit elaborated target type

```lean
∀ {b p r : Nat} (run : HighamBench.P15BLRLinearSolveFamily b p r),
  have c : Real := HighamBench.p15BLRSolveCost b p r;
  have xi : Real :=
    HighamBench.p15BLRXi p (@HighamBench.P15BLRLinearSolveFamily.threshold b p r run)
      (@HighamBench.P15BLRLinearSolveFamily.recompression b p r run);
  have solveScale : (u epsilon : Real) → Real := fun (u epsilon : Real) =>
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@HighamBench.P15BLRLinearSolveFamily.L b p r run u epsilon))
        (@HighamBench.p15FrobNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@HighamBench.P15BLRLinearSolveFamily.U b p r run u epsilon)))
      (@HighamBench.p15VecNorm (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
        (@HighamBench.P15BLRLinearSolveFamily.xHat b p r run u epsilon));
  @Exists.{1}
    (Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
    fun
      (matrixError :
        Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
    @Exists.{1}
      (Real → Real → HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
      fun
        (rhsError :
          Real → Real → HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
      @Exists.{1} (Real → Real → Real) fun (rhsRemainder : Real → Real → Real) =>
        And
          (@Eq.{1}
            (Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
            matrixError fun (u epsilon : Real) =>
            @HighamBench.p15ComposedMatrixError (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
              (@HighamBench.P15BLRLinearSolveFamily.factorError b p r run u epsilon)
              (@HighamBench.P15BLRLinearSolveFamily.lowerError b p r run u epsilon)
              (@HighamBench.P15BLRLinearSolveFamily.upperError b p r run u epsilon)
              (@HighamBench.P15BLRLinearSolveFamily.L b p r run u epsilon)
              (@HighamBench.P15BLRLinearSolveFamily.U b p r run u epsilon))
          (And
            (@Eq.{1}
              (Real →
                Real → HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
              rhsError fun (u epsilon : Real) =>
              @HighamBench.p15ComposedRhsError (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                (@HighamBench.P15BLRLinearSolveFamily.lowerRhsError b p r run u epsilon)
                (@HighamBench.P15BLRLinearSolveFamily.upperRhsError b p r run u epsilon)
                (@HighamBench.P15BLRLinearSolveFamily.L b p r run u epsilon)
                (@HighamBench.P15BLRLinearSolveFamily.lowerError b p r run u epsilon))
            (And (HighamBench.p15IsBigOMixedAtZero (@HighamBench.P15BLRLinearSolveFamily.factorRemainder b p r run))
              (And (HighamBench.p15IsBigOSquareRelativeAtZero rhsRemainder solveScale)
                (∀ (u epsilon : Real),
                  HighamBench.p15AdmissiblePrecision c u epsilon →
                    have gammaP : Real := HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u;
                    have gamma3C : Real :=
                      HighamBench.p15GammaReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          c)
                        u;
                    And
                      (@LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@HighamBench.P15BLRLinearSolveFamily.factorRemainder b p r run u epsilon))
                      (And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (rhsRemainder u epsilon))
                        (And
                          (@Eq.{1}
                            (HighamBench.P15Vector
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (@HighamBench.p15MatVec
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
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
                                (@HighamBench.P15BLRLinearSolveFamily.A b p r run) (matrixError u epsilon))
                              (@HighamBench.P15BLRLinearSolveFamily.xHat b p r run u epsilon))
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
                                  (fun
                                      (a : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                                    Real)
                                  fun (i : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                                  Real.instAdd))
                              (@HighamBench.P15BLRLinearSolveFamily.v b p r run) (rhsError u epsilon)))
                          (And
                            (@LE.le.{0} Real Real.instLE
                              (@HighamBench.p15FrobNorm
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                (matrixError u epsilon))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi epsilon)
                                      gammaP)
                                    (@HighamBench.p15FrobNorm
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                      (@HighamBench.P15BLRLinearSolveFamily.A b p r run)))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gamma3C
                                      (@HighamBench.p15FrobNorm
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                        (@HighamBench.P15BLRLinearSolveFamily.L b p r run u epsilon)))
                                    (@HighamBench.p15FrobNorm
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                      (@HighamBench.P15BLRLinearSolveFamily.U b p r run u epsilon))))
                                (@HighamBench.P15BLRLinearSolveFamily.factorRemainder b p r run u epsilon)))
                            (@LE.le.{0} Real Real.instLE
                              (@HighamBench.p15VecNorm
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                (rhsError u epsilon))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HighamBench.p15VecNorm
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                      (@HighamBench.P15BLRLinearSolveFamily.v b p r run))
                                    (solveScale u epsilon)))
                                (rhsRemainder u epsilon))))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P15Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P15Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P15BLRLinearSolveFamily`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `bdad2ad79a4b07c4dfd5e3b8289dc22459ce666d10c5b41416d70336cfa530db`

Type:

```lean
Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(b p r : Nat) → Type
```

### D002: `HighamBench.P15BLRLinearSolveFamily.A`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e42ef5968c875637f2720762a61ba72183c472378a81cf0db8d8587f93dfdec9`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.7
```

### D003: `HighamBench.P15BLRLinearSolveFamily.L`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a51f1c363b09f0278224ac8203cad654197be450f6e55fdfb98f159ade6c6f5d`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.11
```

### D004: `HighamBench.P15BLRLinearSolveFamily.U`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1b7eb7152fa076add3c083057a9637813c149d3d2cdf1b3b51a2504ac5883790`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.12
```

### D005: `HighamBench.P15BLRLinearSolveFamily.factorError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `59ade090ae9fc6e30e57f0aa1d053e79900f870ebbc9ac1ee2399ca83038a5d7`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.18
```

### D006: `HighamBench.P15BLRLinearSolveFamily.factorRemainder`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8847fb1bce92200c39027c7c3eb97d0114768721b3642226e8a9811fc4a9bca8`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → Real
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveFamily b p r) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.19
```

### D007: `HighamBench.P15BLRLinearSolveFamily.lowerError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `69cdb7e8b57049ed0cf0a9e1afae23f365f4aa442981d1f8f2c9099a22aed297`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.24
```

### D008: `HighamBench.P15BLRLinearSolveFamily.lowerRhsError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `42344efe638dd29b5ac574e2fadff9ae36e91c96050d47b186ac3a99e27201b9`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.26
```

### D009: `HighamBench.P15BLRLinearSolveFamily.recompression`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `09d97a8db292a261d7f16ed29f5e427297ccaec60dd388a5c28885dd1aafd813`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → HighamBench.P15BLRRecompression
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveFamily b p r) → HighamBench.P15BLRRecompression
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.6
```

### D010: `HighamBench.P15BLRLinearSolveFamily.threshold`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `02dd28659ecf0780924b6b1e323da729e2d83c351013e1f500a1ad63ce2d3c46`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → HighamBench.P15BLRThreshold
```

Fully explicit type:

```lean
{b p r : Nat} → (self : HighamBench.P15BLRLinearSolveFamily b p r) → HighamBench.P15BLRThreshold
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.5
```

### D011: `HighamBench.P15BLRLinearSolveFamily.upperError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a61b82e4b8b47ddaf6daac296bd45dc440e8a1ddde352118a120347694078112`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.25
```

### D012: `HighamBench.P15BLRLinearSolveFamily.upperRhsError`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `93f3ac24cbbaaabb26942bdeb674c05005d1fd9449e8379d6e0e95f46c0b5f27`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.27
```

### D013: `HighamBench.P15BLRLinearSolveFamily.v`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6d1e8f192fac4a0f282218705f8e1dbfa80bdb9d0f8e349c8a2b1b3a052b8215`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.8
```

### D014: `HighamBench.P15BLRLinearSolveFamily.xHat`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a4c48fd6023bfa84c79cf2721fe545e2072946e01bde85bd9e328df7a6587d26`

Type:

```lean
{b p r : Nat} → HighamBench.P15BLRLinearSolveFamily b p r → Real → Real → HighamBench.P15Vector (instHMul.hMul p b)
```

Fully explicit type:

```lean
{b p r : Nat} →
  (self : HighamBench.P15BLRLinearSolveFamily b p r) →
    Real → Real → HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.14
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

### D016: `HighamBench.P15Vector`

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

### D017: `HighamBench.p15AdmissiblePrecision`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D018: `HighamBench.p15BLRSolveCost`

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

### D019: `HighamBench.p15BLRXi`

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

### D020: `HighamBench.p15ComposedMatrixError`

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

### D021: `HighamBench.p15ComposedRhsError`

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

### D022: `HighamBench.p15FrobNorm`

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

### D023: `HighamBench.p15GammaReal`

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

### D024: `HighamBench.p15IsBigOMixedAtZero`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `94d1db16fdbc23e161b75cfb8bf2cd9e73cf3680a0bc8abf9e03e9af4a05db77`

Type:

```lean
(Real → Real → Real) → Prop
```

Fully explicit type:

```lean
(remainder : Real → Real → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder =>
  Exists fun C =>
    Exists fun delta =>
      And (Real.instLE.le 0 C)
        (And (Real.instLT.lt 0 delta)
          (∀ (u epsilon : Real),
            Real.instLT.lt 0 u →
              Real.instLT.lt 0 epsilon →
                Real.instLT.lt u epsilon →
                  Real.instLE.le u delta →
                    Real.instLE.le epsilon delta →
                      Real.instLE.le (abs (remainder u epsilon)) (instHMul.hMul C (instHMul.hMul u epsilon))))
```

### D025: `HighamBench.p15IsBigOSquareRelativeAtZero`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4acca8fab08b6cee29aa63aadee09af3b0d679224a9c92cffe5b8d3bd5add815`

Type:

```lean
(Real → Real → Real) → (Real → Real → Real) → Prop
```

Fully explicit type:

```lean
(remainder scale : Real → Real → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder scale =>
  Exists fun C =>
    Exists fun delta =>
      And (Real.instLE.le 0 C)
        (And (Real.instLT.lt 0 delta)
          (∀ (u epsilon : Real),
            Real.instLT.lt 0 u →
              Real.instLT.lt 0 epsilon →
                Real.instLT.lt u epsilon →
                  Real.instLE.le u delta →
                    Real.instLE.le epsilon delta →
                      Real.instLE.le 0 (scale u epsilon) →
                        Real.instLE.le (abs (remainder u epsilon))
                          (instHMul.hMul (instHMul.hMul C (instHPow.hPow u 2)) (scale u epsilon))))
```

### D026: `HighamBench.p15MatVec`

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

### D027: `HighamBench.p15VecNorm`

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

### D028: `HighamBench.P15BLRLinearSolveFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `56298837b8c0d13e8bb755ae2ebcf360fbd2ddd3e9578770455444c71f3e63b8`

Type:

```lean
{b p r : Nat} →
  instLTNat.lt 0 b →
    instLTNat.lt 0 p →
      instLENat.le r b →
        (algorithm : HighamBench.P15BLRFactorizationAlgorithm) →
          (threshold : HighamBench.P15BLRThreshold) →
            (recompression : HighamBench.P15BLRRecompression) →
              (A : HighamBench.P15Matrix (instHMul.hMul p b)) →
                (v : HighamBench.P15Vector (instHMul.hMul p b)) →
                  HighamBench.p15IsNonsingular A →
                    (Atilde : Real → HighamBench.P15Matrix (instHMul.hMul p b)) →
                      (L U : Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)) →
                        (yHat xHat : Real → Real → HighamBench.P15Vector (instHMul.hMul p b)) →
                          (∀ (u epsilon : Real),
                              HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                HighamBench.p15BLRRepresents threshold epsilon A (Atilde epsilon)) →
                            (∀ (u epsilon : Real),
                                HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                  HighamBench.p15IsFactorBLRRank r (L u epsilon) (U u epsilon)) →
                              (∀ (u epsilon : Real),
                                  HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                    HighamBench.P15CompletedBLRFactorization algorithm threshold recompression u epsilon
                                      (Atilde epsilon) (L u epsilon) (U u epsilon)) →
                                (factorError : Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)) →
                                  (factorRemainder : Real → Real → Real) →
                                    (∀ (u epsilon : Real),
                                        HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u
                                            epsilon →
                                          Eq (instHAdd.hAdd A (factorError u epsilon))
                                            (HighamBench.p15MatMul (L u epsilon) (U u epsilon))) →
                                      (∀ (u epsilon : Real),
                                          HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u
                                              epsilon →
                                            Real.instLE.le (HighamBench.p15FrobNorm (factorError u epsilon))
                                              (instHAdd.hAdd
                                                (instHAdd.hAdd
                                                  (instHMul.hMul
                                                    (instHAdd.hAdd
                                                      (instHMul.hMul (HighamBench.p15BLRXi p threshold recompression)
                                                        epsilon)
                                                      (HighamBench.p15GammaReal p.cast u))
                                                    (HighamBench.p15FrobNorm A))
                                                  (instHMul.hMul
                                                    (instHMul.hMul
                                                      (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                                                      (HighamBench.p15FrobNorm (L u epsilon)))
                                                    (HighamBench.p15FrobNorm (U u epsilon))))
                                                (factorRemainder u epsilon))) →
                                        (∀ (u epsilon : Real),
                                            HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u
                                                epsilon →
                                              Real.instLE.le 0 (factorRemainder u epsilon)) →
                                          HighamBench.p15IsBigOMixedAtZero factorRemainder →
                                            (lowerError upperError :
                                                Real → Real → HighamBench.P15Matrix (instHMul.hMul p b)) →
                                              (lowerRhsError upperRhsError :
                                                  Real → Real → HighamBench.P15Vector (instHMul.hMul p b)) →
                                                (∀ (u epsilon : Real),
                                                    HighamBench.p15AdmissiblePrecision
                                                        (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                      HighamBench.P15CompletedTriangularSolve
                                                        HighamBench.P15TriangularSolveDirection.lower u (L u epsilon) v
                                                        (yHat u epsilon)) →
                                                  (∀ (u epsilon : Real),
                                                      HighamBench.p15AdmissiblePrecision
                                                          (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                        HighamBench.P15CompletedTriangularSolve
                                                          HighamBench.P15TriangularSolveDirection.upper u (U u epsilon)
                                                          (yHat u epsilon) (xHat u epsilon)) →
                                                    (∀ (u epsilon : Real),
                                                        HighamBench.p15AdmissiblePrecision
                                                            (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                          Eq
                                                            (HighamBench.p15MatVec
                                                              (instHAdd.hAdd (L u epsilon) (lowerError u epsilon))
                                                              (yHat u epsilon))
                                                            (instHAdd.hAdd v (lowerRhsError u epsilon))) →
                                                      (∀ (u epsilon : Real),
                                                          HighamBench.p15AdmissiblePrecision
                                                              (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                            Eq
                                                              (HighamBench.p15MatVec
                                                                (instHAdd.hAdd (U u epsilon) (upperError u epsilon))
                                                                (xHat u epsilon))
                                                              (instHAdd.hAdd (yHat u epsilon)
                                                                (upperRhsError u epsilon))) →
                                                        (∀ (u epsilon : Real),
                                                            HighamBench.p15AdmissiblePrecision
                                                                (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                              Real.instLE.le
                                                                (HighamBench.p15FrobNorm (lowerError u epsilon))
                                                                (instHMul.hMul
                                                                  (HighamBench.p15GammaReal
                                                                    (HighamBench.p15BLRSolveCost b p r) u)
                                                                  (HighamBench.p15FrobNorm (L u epsilon)))) →
                                                          (∀ (u epsilon : Real),
                                                              HighamBench.p15AdmissiblePrecision
                                                                  (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                Real.instLE.le
                                                                  (HighamBench.p15FrobNorm (upperError u epsilon))
                                                                  (instHMul.hMul
                                                                    (HighamBench.p15GammaReal
                                                                      (HighamBench.p15BLRSolveCost b p r) u)
                                                                    (HighamBench.p15FrobNorm (U u epsilon)))) →
                                                            (∀ (u epsilon : Real),
                                                                HighamBench.p15AdmissiblePrecision
                                                                    (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                  Real.instLE.le
                                                                    (HighamBench.p15VecNorm (lowerRhsError u epsilon))
                                                                    (instHMul.hMul (HighamBench.p15GammaReal p.cast u)
                                                                      (HighamBench.p15VecNorm v))) →
                                                              (∀ (u epsilon : Real),
                                                                  HighamBench.p15AdmissiblePrecision
                                                                      (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                    Real.instLE.le
                                                                      (HighamBench.p15VecNorm (upperRhsError u epsilon))
                                                                      (instHMul.hMul (HighamBench.p15GammaReal p.cast u)
                                                                        (HighamBench.p15VecNorm (yHat u epsilon)))) →
                                                                HighamBench.P15BLRLinearSolveFamily b p r
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
              (A : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                (v : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                  (A_nonsingular :
                      @HighamBench.p15IsNonsingular
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b) A) →
                    (Atilde :
                        Real →
                          HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                      (L U :
                          Real →
                            Real →
                              HighamBench.P15Matrix
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                        (yHat xHat :
                            Real →
                              Real →
                                HighamBench.P15Vector
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                          (represents :
                              ∀ (u epsilon : Real),
                                HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                  @HighamBench.p15BLRRepresents p b threshold epsilon A (Atilde epsilon)) →
                            (factor_rank :
                                ∀ (u epsilon : Real),
                                  HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                    @HighamBench.p15IsFactorBLRRank p b r (L u epsilon) (U u epsilon)) →
                              (factorization_completed :
                                  ∀ (u epsilon : Real),
                                    HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                      @HighamBench.P15CompletedBLRFactorization b p algorithm threshold recompression u
                                        epsilon (Atilde epsilon) (L u epsilon) (U u epsilon)) →
                                (factorError :
                                    Real →
                                      Real →
                                        HighamBench.P15Matrix
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
                                  (factorRemainder : Real → Real → Real) →
                                    (factorization_eq :
                                        ∀ (u epsilon : Real),
                                          HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u
                                              epsilon →
                                            @Eq.{1}
                                              (HighamBench.P15Matrix
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                              (@HAdd.hAdd.{0, 0, 0}
                                                (HighamBench.P15Matrix
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                                (HighamBench.P15Matrix
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                                (HighamBench.P15Matrix
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                                                (@instHAdd.{0}
                                                  (HighamBench.P15Matrix
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                      b))
                                                  (@Matrix.add.{0, 0, 0}
                                                    (Fin
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b))
                                                    (Fin
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b))
                                                    Real Real.instAdd))
                                                A (factorError u epsilon))
                                              (@HighamBench.p15MatMul
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                                (L u epsilon) (U u epsilon))) →
                                      (factorError_le :
                                          ∀ (u epsilon : Real),
                                            HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u
                                                epsilon →
                                              @LE.le.{0} Real Real.instLE
                                                (@HighamBench.p15FrobNorm
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                                  (factorError u epsilon))
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                        (@instHAdd.{0} Real Real.instAdd)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (HighamBench.p15BLRXi p threshold recompression) epsilon)
                                                        (HighamBench.p15GammaReal
                                                          (@Nat.cast.{0} Real Real.instNatCast p) u))
                                                      (@HighamBench.p15FrobNorm
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p b)
                                                        A))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (HighamBench.p15GammaReal (HighamBench.p15BLRSolveCost b p r) u)
                                                        (@HighamBench.p15FrobNorm
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                          (L u epsilon)))
                                                      (@HighamBench.p15FrobNorm
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p b)
                                                        (U u epsilon))))
                                                  (factorRemainder u epsilon))) →
                                        (factorRemainder_nonneg :
                                            ∀ (u epsilon : Real),
                                              HighamBench.p15AdmissiblePrecision (HighamBench.p15BLRSolveCost b p r) u
                                                  epsilon →
                                                @LE.le.{0} Real Real.instLE
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                  (factorRemainder u epsilon)) →
                                          (factorRemainder_bigO : HighamBench.p15IsBigOMixedAtZero factorRemainder) →
                                            (lowerError upperError :
                                                Real →
                                                  Real →
                                                    HighamBench.P15Matrix
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p
                                                        b)) →
                                              (lowerRhsError upperRhsError :
                                                  Real →
                                                    Real →
                                                      HighamBench.P15Vector
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          p b)) →
                                                (lower_completed :
                                                    ∀ (u epsilon : Real),
                                                      HighamBench.p15AdmissiblePrecision
                                                          (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                        @HighamBench.P15CompletedTriangularSolve p b
                                                          HighamBench.P15TriangularSolveDirection.lower u (L u epsilon)
                                                          v (yHat u epsilon)) →
                                                  (upper_completed :
                                                      ∀ (u epsilon : Real),
                                                        HighamBench.p15AdmissiblePrecision
                                                            (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                          @HighamBench.P15CompletedTriangularSolve p b
                                                            HighamBench.P15TriangularSolveDirection.upper u
                                                            (U u epsilon) (yHat u epsilon) (xHat u epsilon)) →
                                                    (lowerSolve_eq :
                                                        ∀ (u epsilon : Real),
                                                          HighamBench.p15AdmissiblePrecision
                                                              (HighamBench.p15BLRSolveCost b p r) u epsilon →
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
                                                                  (L u epsilon) (lowerError u epsilon))
                                                                (yHat u epsilon))
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
                                                                              (@instHMul.{0} Nat instMulNat) p b)) =>
                                                                      Real)
                                                                    fun
                                                                      (i :
                                                                        Fin
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b)) =>
                                                                    Real.instAdd))
                                                                v (lowerRhsError u epsilon))) →
                                                      (upperSolve_eq :
                                                          ∀ (u epsilon : Real),
                                                            HighamBench.p15AdmissiblePrecision
                                                                (HighamBench.p15BLRSolveCost b p r) u epsilon →
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
                                                                    (U u epsilon) (upperError u epsilon))
                                                                  (xHat u epsilon))
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
                                                                                (@instHMul.{0} Nat instMulNat) p b)) =>
                                                                        Real)
                                                                      fun
                                                                        (i :
                                                                          Fin
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b)) =>
                                                                      Real.instAdd))
                                                                  (yHat u epsilon) (upperRhsError u epsilon))) →
                                                        (lowerError_le :
                                                            ∀ (u epsilon : Real),
                                                              HighamBench.p15AdmissiblePrecision
                                                                  (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@HighamBench.p15FrobNorm
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat) p b)
                                                                    (lowerError u epsilon))
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul)
                                                                    (HighamBench.p15GammaReal
                                                                      (HighamBench.p15BLRSolveCost b p r) u)
                                                                    (@HighamBench.p15FrobNorm
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b)
                                                                      (L u epsilon)))) →
                                                          (upperError_le :
                                                              ∀ (u epsilon : Real),
                                                                HighamBench.p15AdmissiblePrecision
                                                                    (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                  @LE.le.{0} Real Real.instLE
                                                                    (@HighamBench.p15FrobNorm
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat) p b)
                                                                      (upperError u epsilon))
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul)
                                                                      (HighamBench.p15GammaReal
                                                                        (HighamBench.p15BLRSolveCost b p r) u)
                                                                      (@HighamBench.p15FrobNorm
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b)
                                                                        (U u epsilon)))) →
                                                            (lowerRhsError_le :
                                                                ∀ (u epsilon : Real),
                                                                  HighamBench.p15AdmissiblePrecision
                                                                      (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                    @LE.le.{0} Real Real.instLE
                                                                      (@HighamBench.p15VecNorm
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat) p b)
                                                                        (lowerRhsError u epsilon))
                                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                        (@instHMul.{0} Real Real.instMul)
                                                                        (HighamBench.p15GammaReal
                                                                          (@Nat.cast.{0} Real Real.instNatCast p) u)
                                                                        (@HighamBench.p15VecNorm
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                                          v))) →
                                                              (upperRhsError_le :
                                                                  ∀ (u epsilon : Real),
                                                                    HighamBench.p15AdmissiblePrecision
                                                                        (HighamBench.p15BLRSolveCost b p r) u epsilon →
                                                                      @LE.le.{0} Real Real.instLE
                                                                        (@HighamBench.p15VecNorm
                                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                            (@instHMul.{0} Nat instMulNat) p b)
                                                                          (upperRhsError u epsilon))
                                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                          (@instHMul.{0} Real Real.instMul)
                                                                          (HighamBench.p15GammaReal
                                                                            (@Nat.cast.{0} Real Real.instNatCast p) u)
                                                                          (@HighamBench.p15VecNorm
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat) p b)
                                                                            (yHat u epsilon)))) →
                                                                HighamBench.P15BLRLinearSolveFamily b p r
```

### D029: `HighamBench.P15BLRRecompression`

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

### D030: `HighamBench.P15BLRThreshold`

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

### D031: `HighamBench.p15AdmissiblePrecision._proof_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
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

### D032: `HighamBench.p15BLRSolveCost._proof_1`

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

### D033: `HighamBench.p15BLRXi._proof_1`

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

### D034: `HighamBench.p15BLRXi.match_1`

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

### D035: `HighamBench.p15MatMul`

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

### D036: `HighamBench.p15RectFrobNorm`

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

### D037: `HighamBench.P15BLRFactorizationAlgorithm`

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

### D038: `HighamBench.P15BLRRecompression.casesOn`

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

### D039: `HighamBench.P15BLRRecompression.with`

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

### D040: `HighamBench.P15BLRRecompression.without`

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

### D041: `HighamBench.P15BLRThreshold.casesOn`

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

### D042: `HighamBench.P15BLRThreshold.global`

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

### D043: `HighamBench.P15BLRThreshold.local`

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

### D044: `HighamBench.P15CompletedBLRFactorization`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `bbd93bd9c00f450a60dd82870705598b54e9055b1d7a89a67bb715b0b3d7e24d`

Type:

```lean
{b p : Nat} →
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
  (algorithm : HighamBench.P15BLRFactorizationAlgorithm) →
    (threshold : HighamBench.P15BLRThreshold) →
      (recompression : HighamBench.P15BLRRecompression) →
        (u epsilon : Real) →
          (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b p} algorithm threshold recompression u epsilon A L U =>
  HighamBench.instReprP15BLRFactorizationAlgorithm.repr.match_1 (fun algorithm => Prop) algorithm
    (fun _ => Nonempty (HighamBench.P15CompletedUFCFactorization threshold recompression u epsilon A L U)) fun _ =>
    Nonempty (HighamBench.P15CompletedUCFFactorization threshold recompression u epsilon A L U)
```

### D045: `HighamBench.P15CompletedTriangularSolve`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `a263bccfe3bd816977d2dc7732f0280b9a573814ac81336cd82b64588768423f`

Type:

```lean
{p b : Nat} →
  HighamBench.P15TriangularSolveDirection →
    Real →
      HighamBench.P15Matrix (instHMul.hMul p b) →
        HighamBench.P15Vector (instHMul.hMul p b) → HighamBench.P15Vector (instHMul.hMul p b) → Prop
```

Fully explicit type:

```lean
{p b : Nat} →
  (direction : HighamBench.P15TriangularSolveDirection) →
    (u : Real) →
      (T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
        (rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Prop
```

### D046: `HighamBench.P15RectMatrix`

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

### D047: `HighamBench.P15TriangularSolveDirection.lower`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `ed7c8315fcb03c4458bf042d8e255dbdd43a81b2256e12ed8cedcaa4b4901e2b`

Type:

```lean
HighamBench.P15TriangularSolveDirection
```

Fully explicit type:

```lean
HighamBench.P15TriangularSolveDirection
```

### D048: `HighamBench.P15TriangularSolveDirection.upper`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e6d13e0fa0da3a432d462199fc5932439303d796406010f67483ae2716235cb0`

Type:

```lean
HighamBench.P15TriangularSolveDirection
```

Fully explicit type:

```lean
HighamBench.P15TriangularSolveDirection
```

### D049: `HighamBench.p15BLRRepresents`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b6eaf06795169f5cec450735849d59c7c3aa3bb417d756a95f7908d2505a9b76`

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
          Exists fun X =>
            Exists fun Y =>
              And (Eq (HighamBench.p15MatrixBlock Atilde i j) (HighamBench.p15LowRankMatrix X Y))
                (Real.instLE.le
                  (HighamBench.p15FrobNorm
                    (instHSub.hSub (HighamBench.p15MatrixBlock Atilde i j) (HighamBench.p15MatrixBlock A i j)))
                  (instHMul.hMul epsilon
                    (HighamBench.instReprP15BLRThreshold.repr.match_1 (fun threshold => Real) threshold
                      (fun _ => HighamBench.p15FrobNorm (HighamBench.p15MatrixBlock A i j)) fun _ =>
                      HighamBench.p15FrobNorm A))))
```

### D050: `HighamBench.p15IsFactorBLRRank`

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

### D051: `HighamBench.p15IsNonsingular`

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

### D052: `HighamBench.P15BLRFactorizationAlgorithm.ucf`

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

### D053: `HighamBench.P15BLRFactorizationAlgorithm.ufc`

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

### D054: `HighamBench.P15BLRRecompression.rec`

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

### D055: `HighamBench.P15BLRThreshold.rec`

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

### D056: `HighamBench.P15CompletedTriangularSolve.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e3d669d72200dadaa141c2deecb7d621b3c0d119c181e96943efee9eb3951198`

Type:

```lean
∀ {p b : Nat} {direction : HighamBench.P15TriangularSolveDirection} {u : Real}
  {T : HighamBench.P15Matrix (instHMul.hMul p b)} {rhs x : HighamBench.P15Vector (instHMul.hMul p b)},
  (HighamBench.instReprP15TriangularSolveDirection.repr.match_1 (fun direction => Prop) direction
      (fun _ => HighamBench.p15IsBlockLowerTriangular T) fun _ => HighamBench.p15IsBlockUpperTriangular T) →
    (∀ (i : Fin p) (row : Fin b),
        HighamBench.p15StandardRound (HighamBench.p15GammaReal p.cast u)
          (HighamBench.p15TriangularResidual direction T rhs x i row)
          (HighamBench.p15MatVec (HighamBench.p15MatrixBlock T i i) (fun col => x (HighamBench.p15BlockIndex i col))
            row)) →
      HighamBench.P15CompletedTriangularSolve direction u T rhs x
```

Fully explicit type:

```lean
∀ {p b : Nat} {direction : HighamBench.P15TriangularSolveDirection} {u : Real}
  {T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)}
  {rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)}
  (triangular :
    HighamBench.instReprP15TriangularSolveDirection.repr.match_1.{1}
      (fun (direction : HighamBench.P15TriangularSolveDirection) => Prop) direction
      (fun (_ : Unit) => @HighamBench.p15IsBlockLowerTriangular p b T) fun (_ : Unit) =>
      @HighamBench.p15IsBlockUpperTriangular p b T)
  (block_steps :
    ∀ (i : Fin p) (row : Fin b),
      HighamBench.p15StandardRound (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
        (@HighamBench.p15TriangularResidual p b direction T rhs x i row)
        (@HighamBench.p15MatVec b (@HighamBench.p15MatrixBlock p b T i i)
          (fun (col : Fin b) => x (@HighamBench.p15BlockIndex p b i col)) row)),
  @HighamBench.P15CompletedTriangularSolve p b direction u T rhs x
```

### D057: `HighamBench.P15CompletedUCFFactorization`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `26f820e359a283edd91174628f45697fc95de0f8951c428716c44de57b42bd74`

Type:

```lean
{p b : Nat} →
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
  (threshold : HighamBench.P15BLRThreshold) →
    (recompression : HighamBench.P15BLRRecompression) →
      (u epsilon : Real) →
        (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D058: `HighamBench.P15CompletedUFCFactorization`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `8cbdaf53d163bca56f81746e57a82ca0d060050f1c7bcd0283bf45fc7fb62623`

Type:

```lean
{p b : Nat} →
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
  (threshold : HighamBench.P15BLRThreshold) →
    (recompression : HighamBench.P15BLRRecompression) →
      (u epsilon : Real) →
        (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) → Type
```

### D059: `HighamBench.P15TriangularSolveDirection`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `2739599cb5c208da8ba46dbb051853914b460ecd048eb3ce127ee1b183a6a5f3`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D060: `HighamBench.instReprP15BLRFactorizationAlgorithm.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D061: `HighamBench.instReprP15BLRThreshold.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D062: `HighamBench.p15Identity`

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

### D063: `HighamBench.p15IsBLRMatrix`

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

### D064: `HighamBench.p15LowRankMatrix`

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

### D065: `HighamBench.p15MatrixBlock`

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

### D066: `HighamBench.P15BLRFactorizationAlgorithm.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D067: `HighamBench.P15CompletedUCFFactorization.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `4ea9f5820f78e411ed784ec9eabd2f63994c14b2327947759ea4e95b0da96ad3`

Type:

```lean
{p b : Nat} →
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
                          HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal p.cast u)
                            (HighamBench.p15BLRUpdatedBlock A L U recompressionError i k) (updatedColumn k i)) →
                      (∀ (k i : Fin p),
                          instLEFin.le k i →
                            HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal p.cast u)
                              (HighamBench.p15BLRUpdatedBlock A L U recompressionError k i) (updatedRow k i)) →
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
                                  HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal b.cast u)
                                    (updatedColumn k k)
                                    (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L k k)
                                      (HighamBench.p15MatrixBlock U k k))) →
                                (∀ (k i : Fin p),
                                    instLTFin.lt k i →
                                      HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal b.cast u)
                                        (compressedColumn k i)
                                        (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L i k)
                                          (HighamBench.p15MatrixBlock U k k))) →
                                  (∀ (k i : Fin p),
                                      instLTFin.lt k i →
                                        HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal b.cast u)
                                          (compressedRow k i)
                                          (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L k k)
                                            (HighamBench.p15MatrixBlock U k i))) →
                                    HighamBench.P15CompletedUCFFactorization threshold recompression u epsilon A L U
```

Fully explicit type:

```lean
{p b : Nat} →
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
                            @HighamBench.p15EntrywiseStandardRound b b
                              (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                              (@HighamBench.p15BLRUpdatedBlock p b A L U recompressionError i k) (updatedColumn k i)) →
                      (update_row :
                          ∀ (k i : Fin p),
                            @LE.le.{0} (Fin p) (@instLEFin p) k i →
                              @HighamBench.p15EntrywiseStandardRound b b
                                (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                                (@HighamBench.p15BLRUpdatedBlock p b A L U recompressionError k i) (updatedRow k i)) →
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
                                    @HighamBench.p15EntrywiseStandardRound b b
                                      (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                      (updatedColumn k k)
                                      (@HighamBench.p15MatMul b (@HighamBench.p15MatrixBlock p b L k k)
                                        (@HighamBench.p15MatrixBlock p b U k k))) →
                                (lower_solve :
                                    ∀ (k i : Fin p),
                                      @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                        @HighamBench.p15EntrywiseStandardRound b b
                                          (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                          (compressedColumn k i)
                                          (@HighamBench.p15MatMul b (@HighamBench.p15MatrixBlock p b L i k)
                                            (@HighamBench.p15MatrixBlock p b U k k))) →
                                  (upper_solve :
                                      ∀ (k i : Fin p),
                                        @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                          @HighamBench.p15EntrywiseStandardRound b b
                                            (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                            (compressedRow k i)
                                            (@HighamBench.p15MatMul b (@HighamBench.p15MatrixBlock p b L k k)
                                              (@HighamBench.p15MatrixBlock p b U k i))) →
                                    @HighamBench.P15CompletedUCFFactorization p b threshold recompression u epsilon A L
                                      U
```

### D068: `HighamBench.P15CompletedUFCFactorization.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `e7fc6866afef1e1cf69f247695f5876f964dd6e846ef23fe6bea8fc5fc6a99d8`

Type:

```lean
{p b : Nat} →
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
                          HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal p.cast u)
                            (HighamBench.p15BLRUpdatedBlock A L U recompressionError i k) (updatedColumn k i)) →
                      (∀ (k i : Fin p),
                          instLEFin.le k i →
                            HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal p.cast u)
                              (HighamBench.p15BLRUpdatedBlock A L U recompressionError k i) (updatedRow k i)) →
                        (∀ (k : Fin p), Eq (updatedColumn k k) (updatedRow k k)) →
                          (∀ (k : Fin p),
                              HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal b.cast u)
                                (updatedColumn k k)
                                (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L k k)
                                  (HighamBench.p15MatrixBlock U k k))) →
                            (∀ (k i : Fin p),
                                instLTFin.lt k i →
                                  HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal b.cast u)
                                    (updatedColumn k i)
                                    (HighamBench.p15MatMul (rawLower i k) (HighamBench.p15MatrixBlock U k k))) →
                              (∀ (k i : Fin p),
                                  instLTFin.lt k i →
                                    HighamBench.p15EntrywiseStandardRound (HighamBench.p15GammaReal b.cast u)
                                      (updatedRow k i)
                                      (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L k k) (rawUpper k i))) →
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
                                        HighamBench.P15CompletedUFCFactorization threshold recompression u epsilon A L U
```

Fully explicit type:

```lean
{p b : Nat} →
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
                            @HighamBench.p15EntrywiseStandardRound b b
                              (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                              (@HighamBench.p15BLRUpdatedBlock p b A L U recompressionError i k) (updatedColumn k i)) →
                      (update_row :
                          ∀ (k i : Fin p),
                            @LE.le.{0} (Fin p) (@instLEFin p) k i →
                              @HighamBench.p15EntrywiseStandardRound b b
                                (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast p) u)
                                (@HighamBench.p15BLRUpdatedBlock p b A L U recompressionError k i) (updatedRow k i)) →
                        (diagonal_updates_agree :
                            ∀ (k : Fin p), @Eq.{1} (HighamBench.P15Matrix b) (updatedColumn k k) (updatedRow k k)) →
                          (diagonal_factor :
                              ∀ (k : Fin p),
                                @HighamBench.p15EntrywiseStandardRound b b
                                  (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                  (updatedColumn k k)
                                  (@HighamBench.p15MatMul b (@HighamBench.p15MatrixBlock p b L k k)
                                    (@HighamBench.p15MatrixBlock p b U k k))) →
                            (lower_solve :
                                ∀ (k i : Fin p),
                                  @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                    @HighamBench.p15EntrywiseStandardRound b b
                                      (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                      (updatedColumn k i)
                                      (@HighamBench.p15MatMul b (rawLower i k)
                                        (@HighamBench.p15MatrixBlock p b U k k))) →
                              (upper_solve :
                                  ∀ (k i : Fin p),
                                    @LT.lt.{0} (Fin p) (@instLTFin p) k i →
                                      @HighamBench.p15EntrywiseStandardRound b b
                                        (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast b) u)
                                        (updatedRow k i)
                                        (@HighamBench.p15MatMul b (@HighamBench.p15MatrixBlock p b L k k)
                                          (rawUpper k i))) →
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
                                        @HighamBench.P15CompletedUFCFactorization p b threshold recompression u epsilon
                                          A L U
```

### D069: `HighamBench.instReprP15TriangularSolveDirection.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D070: `HighamBench.p15BlockIndex`

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

### D071: `HighamBench.p15IsBlockLowerTriangular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D072: `HighamBench.p15IsBlockUpperTriangular`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D073: `HighamBench.p15RectMatMul`

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

### D074: `HighamBench.p15RectTranspose`

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

### D075: `HighamBench.p15StandardRound`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d87d181abde5a21f970c35af78a037a15d2e329fb4c3b877500ef72d1dd7610b`

Type:

```lean
Real → Real → Real → Prop
```

Fully explicit type:

```lean
(u exact rounded : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun u exact rounded =>
  Exists fun delta => And (Real.instLE.le (abs delta) u) (Eq rounded (instHMul.hMul exact (instHAdd.hAdd 1 delta)))
```

### D076: `HighamBench.p15TriangularResidual`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `4308fd636a4751187dafe8cdf404219c807748c8ec1833be974064a6f12a08a4`

Type:

```lean
{p b : Nat} →
  HighamBench.P15TriangularSolveDirection →
    HighamBench.P15Matrix (instHMul.hMul p b) →
      HighamBench.P15Vector (instHMul.hMul p b) → HighamBench.P15Vector (instHMul.hMul p b) → Fin p → Fin b → Real
```

Fully explicit type:

```lean
{p b : Nat} →
  (direction : HighamBench.P15TriangularSolveDirection) →
    (T : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
      (rhs x : HighamBench.P15Vector (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
        (i : Fin p) → (row : Fin b) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {p b} direction T rhs x i row =>
  HighamBench.instReprP15TriangularSolveDirection.repr.match_1 (fun direction => Real) direction
    (fun _ =>
      instHSub.hSub (rhs (HighamBench.p15BlockIndex i row))
        ((Finset.filter (fun j => instLTFin.lt j i) Finset.univ).sum fun j =>
          Finset.univ.sum fun col =>
            instHMul.hMul (HighamBench.p15MatrixBlock T i j row col) (x (HighamBench.p15BlockIndex j col))))
    fun _ =>
    instHSub.hSub (rhs (HighamBench.p15BlockIndex i row))
      ((Finset.filter (fun j => instLTFin.lt i j) Finset.univ).sum fun j =>
        Finset.univ.sum fun col =>
          instHMul.hMul (HighamBench.p15MatrixBlock T i j row col) (x (HighamBench.p15BlockIndex j col)))
```

### D077: `HighamBench.P15BLRFactorizationAlgorithm.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `6`
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

### D078: `HighamBench.P15BlockCompression`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `b39765279d0e57ef423fc04ef4d68b38c574ecdd4718bb8c3ab7b3b12847a03e`

Type:

```lean
{b : Nat} → Real → Real → HighamBench.P15Matrix b → HighamBench.P15Matrix b → Type
```

Fully explicit type:

```lean
{b : Nat} → (epsilon beta : Real) → (exact compressed : HighamBench.P15Matrix b) → Type
```

### D079: `HighamBench.P15TriangularSolveDirection.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D080: `HighamBench.p15BLRCompressionBase`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D081: `HighamBench.p15BLRUpdatedBlock`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `da2dbfdc9c3d3ed9bd2319d9ee07e109832c596d9d4d743b8b5a04382b85edae`

Type:

```lean
{p b : Nat} →
  HighamBench.P15Matrix (instHMul.hMul p b) →
    HighamBench.P15Matrix (instHMul.hMul p b) →
      HighamBench.P15Matrix (instHMul.hMul p b) →
        (Fin p → Fin p → Fin p → HighamBench.P15Matrix b) → Fin p → Fin p → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{p b : Nat} →
  (A L U : HighamBench.P15Matrix (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) →
    (recompressionError : Fin p → Fin p → Fin p → HighamBench.P15Matrix b) → (i k : Fin p) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun {p b} A L U recompressionError i k =>
  instHSub.hSub (HighamBench.p15MatrixBlock A i k)
    ((Finset.filter (fun j => instLTFin.lt j k) Finset.univ).sum fun j =>
      instHAdd.hAdd (HighamBench.p15MatMul (HighamBench.p15MatrixBlock L i j) (HighamBench.p15MatrixBlock U j k))
        (recompressionError i k j))
```

### D082: `HighamBench.p15BlockIndex._proof_1`

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

### D083: `HighamBench.p15EntrywiseStandardRound`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `b4b39896c74a1366171121011c9dad42a50bd6c6628aade1c3f8576af08ba6b7`

Type:

```lean
{m n : Nat} → Real → HighamBench.P15RectMatrix m n → HighamBench.P15RectMatrix m n → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (gamma : Real) → (exact rounded : HighamBench.P15RectMatrix m n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} gamma exact rounded => ∀ (i : Fin m) (j : Fin n), HighamBench.p15StandardRound gamma (exact i j) (rounded i j)
```

### D084: `HighamBench.p15RecompressionModel`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `e1573b954e5445ccf2fc8871fe1d41abaff3c3829f7c8839c63ea7272fc8311a`

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
    ∀ (i k j : Fin p),
      instLTFin.lt j k →
        Real.instLE.le (HighamBench.p15FrobNorm (error i k j))
          (instHMul.hMul epsilon (HighamBench.p15BLRCompressionBase threshold A i k))
```

### D085: `HighamBench.P15BlockCompression.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `6bb3c8f995823b61d041ffe374ea5f803718940d50008c9c166e034c376ca432`

Type:

```lean
{b : Nat} →
  {epsilon beta : Real} →
    {exact compressed : HighamBench.P15Matrix b} →
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
      (error : HighamBench.P15Matrix b) →
        (compressed_eq :
            @Eq.{1} (HighamBench.P15Matrix b) compressed
              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
                (@instHAdd.{0} (HighamBench.P15Matrix b) (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                exact error)) →
          (error_le :
              @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm b error)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon beta)) →
            @HighamBench.P15BlockCompression b epsilon beta exact compressed
```

### D086: `HighamBench.P15TriangularSolveDirection.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `7`
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

### D087: `HighamBench.instReprP15BLRRecompression.repr.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
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

### D088: `And`

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

### D089: `Eq`

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

### D090: `Exists`

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

### D091: `Fin`

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

### D092: `HAdd.hAdd`

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

### D093: `HMul.hMul`

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

### D094: `LE.le`

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

### D095: `Matrix.add`

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

### D096: `Nat`

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

### D097: `Nat.cast`

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

### D098: `Nat.instAtLeastTwoHAddOfNat`

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

### D099: `Nat.instNeZeroSucc`

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

### D100: `OfNat.ofNat`

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

### D101: `Pi.instAdd`

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

### D102: `Real`

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

### D103: `Real.instAdd`

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

### D104: `Real.instLE`

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

### D105: `Real.instMul`

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

### D106: `Real.instNatCast`

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

### D107: `Real.instZero`

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

### D108: `Zero.toOfNat0`

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

### D109: `instHAdd`

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

### D110: `instHMul`

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

### D111: `instMulNat`

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

### D112: `instOfNatAtLeastTwo`

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

### D113: `instOfNatNat`

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

### D114: `DivInvMonoid.toDiv`

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

### D115: `Fin.fintype`

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

### D116: `Finset.sum`

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

### D117: `Finset.univ`

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

### D118: `HDiv.hDiv`

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

### D119: `HPow.hPow`

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

### D120: `HSub.hSub`

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

### D121: `LT.lt`

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

### D122: `Matrix`

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

### D123: `Monoid.toNatPow`

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

### D124: `One.toOfNat1`

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

### D125: `Real.instAddCommMonoid`

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

### D126: `Real.instAddGroup`

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

### D127: `Real.instDivInvMonoid`

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

### D128: `Real.instLT`

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

### D129: `Real.instMonoid`

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

### D130: `Real.instOne`

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

### D131: `Real.instSub`

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

### D132: `Real.lattice`

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

### D133: `Real.sqrt`

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

### D134: `Unit`

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

### D135: `abs`

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

### D136: `instHDiv`

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

### D137: `instHPow`

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

### D138: `instHSub`

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

### D139: `Nat.AtLeastTwo`

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

### D140: `Unit.unit`

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

### D141: `instAddNat`

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

### D142: `instLENat`

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

### D143: `instLTNat`

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

### D144: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D145: `Ne`

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

### D146: `Nonempty`

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

### D147: `instDecidableEqFin`

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

### D148: `ite`

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

### D149: `Fin.decLt`

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

### D150: `Fin.mk`

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

### D151: `Fin.val`

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

### D152: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D153: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D154: `instLEFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D155: `instLTFin`

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

### D156: `Matrix.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D157: `Nat.instPreorder`

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

### D158: `Preorder.toLT`

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
