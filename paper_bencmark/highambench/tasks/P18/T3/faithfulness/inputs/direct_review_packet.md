# Declaration dossier for P18-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p18_t3_method4s3pc_order_certificate :
    p18Method4s3pCBPerturbation = (fun _ => 0) ∧
      |p18CoeffDot p18Method4s3pCBTilde p18Method4s3pCE - 1| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde p18Method4s3pCCTilde - 1 / 2| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffHadamard p18Method4s3pCCTilde
            p18Method4s3pCCTilde) - 1 / 3| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCATilde
            p18Method4s3pCCTilde) - 1 / 6| ≤
        p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          p18Method4s3pCCPerturbation| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCAPerturbation
            p18Method4s3pCCTilde)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCATilde
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffHadamard p18Method4s3pCCTilde
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffMatVec p18Method4s3pCAPerturbation
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      |p18CoeffDot p18Method4s3pCBTilde
          (p18CoeffHadamard p18Method4s3pCCPerturbation
            p18Method4s3pCCPerturbation)| ≤ p18PrintedCoeffTolerance ∧
      1 / 100 < p18CoeffAbsDot p18Method4s3pCBTilde
        p18Method4s3pCCPerturbation
```

## Elaborated target type

```lean
And (Eq HighamBench.p18Method4s3pCBPerturbation fun x => 0)
  (And
    (Real.instLE.le
      (abs (instHSub.hSub (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCE) 1))
      HighamBench.p18PrintedCoeffTolerance)
    (And
      (Real.instLE.le
        (abs
          (instHSub.hSub (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCCTilde)
            (1 / 2)))
        HighamBench.p18PrintedCoeffTolerance)
      (And
        (Real.instLE.le
          (abs
            (instHSub.hSub
              (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                (HighamBench.p18CoeffHadamard HighamBench.p18Method4s3pCCTilde HighamBench.p18Method4s3pCCTilde))
              (1 / 3)))
          HighamBench.p18PrintedCoeffTolerance)
        (And
          (Real.instLE.le
            (abs
              (instHSub.hSub
                (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                  (HighamBench.p18CoeffMatVec HighamBench.p18Method4s3pCATilde HighamBench.p18Method4s3pCCTilde))
                (1 / 6)))
            HighamBench.p18PrintedCoeffTolerance)
          (And
            (Real.instLE.le
              (abs (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCCPerturbation))
              HighamBench.p18PrintedCoeffTolerance)
            (And
              (Real.instLE.le
                (abs
                  (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                    (HighamBench.p18CoeffMatVec HighamBench.p18Method4s3pCAPerturbation
                      HighamBench.p18Method4s3pCCTilde)))
                HighamBench.p18PrintedCoeffTolerance)
              (And
                (Real.instLE.le
                  (abs
                    (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                      (HighamBench.p18CoeffMatVec HighamBench.p18Method4s3pCATilde
                        HighamBench.p18Method4s3pCCPerturbation)))
                  HighamBench.p18PrintedCoeffTolerance)
                (And
                  (Real.instLE.le
                    (abs
                      (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                        (HighamBench.p18CoeffHadamard HighamBench.p18Method4s3pCCTilde
                          HighamBench.p18Method4s3pCCPerturbation)))
                    HighamBench.p18PrintedCoeffTolerance)
                  (And
                    (Real.instLE.le
                      (abs
                        (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                          (HighamBench.p18CoeffMatVec HighamBench.p18Method4s3pCAPerturbation
                            HighamBench.p18Method4s3pCCPerturbation)))
                      HighamBench.p18PrintedCoeffTolerance)
                    (And
                      (Real.instLE.le
                        (abs
                          (HighamBench.p18CoeffDot HighamBench.p18Method4s3pCBTilde
                            (HighamBench.p18CoeffHadamard HighamBench.p18Method4s3pCCPerturbation
                              HighamBench.p18Method4s3pCCPerturbation)))
                        HighamBench.p18PrintedCoeffTolerance)
                      (Real.instLT.lt (1 / 100)
                        (HighamBench.p18CoeffAbsDot HighamBench.p18Method4s3pCBTilde
                          HighamBench.p18Method4s3pCCPerturbation))))))))))))
```

## Fully explicit elaborated target type

```lean
And
  (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
    HighamBench.p18Method4s3pCBPerturbation
    fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  (And
    (@LE.le.{0} Real Real.instLE
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCE)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      HighamBench.p18PrintedCoeffTolerance)
    (And
      (@LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCCTilde)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
        HighamBench.p18PrintedCoeffTolerance)
      (And
        (@LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                HighamBench.p18Method4s3pCBTilde
                (@HighamBench.p18CoeffHadamard (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  HighamBench.p18Method4s3pCCTilde HighamBench.p18Method4s3pCCTilde))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
          HighamBench.p18PrintedCoeffTolerance)
        (And
          (@LE.le.{0} Real Real.instLE
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  HighamBench.p18Method4s3pCBTilde
                  (@HighamBench.p18CoeffMatVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    HighamBench.p18Method4s3pCATilde HighamBench.p18Method4s3pCCTilde))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 6)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
            HighamBench.p18PrintedCoeffTolerance)
          (And
            (@LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCCPerturbation))
              HighamBench.p18PrintedCoeffTolerance)
            (And
              (@LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    HighamBench.p18Method4s3pCBTilde
                    (@HighamBench.p18CoeffMatVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      HighamBench.p18Method4s3pCAPerturbation HighamBench.p18Method4s3pCCTilde)))
                HighamBench.p18PrintedCoeffTolerance)
              (And
                (@LE.le.{0} Real Real.instLE
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      HighamBench.p18Method4s3pCBTilde
                      (@HighamBench.p18CoeffMatVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        HighamBench.p18Method4s3pCATilde HighamBench.p18Method4s3pCCPerturbation)))
                  HighamBench.p18PrintedCoeffTolerance)
                (And
                  (@LE.le.{0} Real Real.instLE
                    (@abs.{0} Real Real.lattice Real.instAddGroup
                      (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        HighamBench.p18Method4s3pCBTilde
                        (@HighamBench.p18CoeffHadamard (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          HighamBench.p18Method4s3pCCTilde HighamBench.p18Method4s3pCCPerturbation)))
                    HighamBench.p18PrintedCoeffTolerance)
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup
                        (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          HighamBench.p18Method4s3pCBTilde
                          (@HighamBench.p18CoeffMatVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            HighamBench.p18Method4s3pCAPerturbation HighamBench.p18Method4s3pCCPerturbation)))
                      HighamBench.p18PrintedCoeffTolerance)
                    (And
                      (@LE.le.{0} Real Real.instLE
                        (@abs.{0} Real Real.lattice Real.instAddGroup
                          (@HighamBench.p18CoeffDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            HighamBench.p18Method4s3pCBTilde
                            (@HighamBench.p18CoeffHadamard (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              HighamBench.p18Method4s3pCCPerturbation HighamBench.p18Method4s3pCCPerturbation)))
                        HighamBench.p18PrintedCoeffTolerance)
                      (@LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 100)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 100) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))))))
                        (@HighamBench.p18CoeffAbsDot (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          HighamBench.p18Method4s3pCBTilde HighamBench.p18Method4s3pCCPerturbation))))))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P18Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P18Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p18CoeffAbsDot`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7e32a3976cd9c6452f67f1af32fa787b9558b077a4296ba345b436d4681da878`

Type:

```lean
{s : Nat} → (Fin s → Real) → (Fin s → Real) → Real
```

Fully explicit type:

```lean
{s : Nat} → (x y : Fin s → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} x y => Finset.univ.sum fun i => instHMul.hMul (abs (x i)) (abs (y i))
```

### D002: `HighamBench.p18CoeffDot`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bd9b2b87931791a0513395de521f55820ffea08ecd6e5327f9285fb57802653d`

Type:

```lean
{s : Nat} → (Fin s → Real) → (Fin s → Real) → Real
```

Fully explicit type:

```lean
{s : Nat} → (x y : Fin s → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} x y => Finset.univ.sum fun i => instHMul.hMul (x i) (y i)
```

### D003: `HighamBench.p18CoeffHadamard`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9744d86b4fa53b459dbaebbe4af9ed542fc9df730bcfb949971f292acb657aa1`

Type:

```lean
{s : Nat} → (Fin s → Real) → (Fin s → Real) → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (x y : Fin s → Real) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} x y i => instHMul.hMul (x i) (y i)
```

### D004: `HighamBench.p18CoeffMatVec`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6d6065bfcec4876b221aaa96bfe3d07b5525312256365327c3ca230674119e64`

Type:

```lean
{s : Nat} → (Fin s → Fin s → Real) → (Fin s → Real) → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (A : Fin s → Fin s → Real) → (x : Fin s → Real) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D005: `HighamBench.p18Method4s3pCAPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7a67cace1a40b012320ffef3e09252bb2ff0dc641aa170fe4343dbbe67fdf9c4`

Type:

```lean
Fin 4 → Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
  Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
EquivLike.toFunLike.coe Matrix.of
  (Matrix.vecCons
    (Matrix.vecCons 0.511243008730995 (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty))))
    (Matrix.vecCons
      (Matrix.vecCons (Real.instNeg.neg 1.999347282862640)
        (Matrix.vecCons 1.957161067302390 (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty))))
      (Matrix.vecCons
        (Matrix.vecCons 0.443312893511937
          (Matrix.vecCons (Real.instNeg.neg 0.573131033672219)
            (Matrix.vecCons 0.128283796414019 (Matrix.vecCons 0 Matrix.vecEmpty))))
        (Matrix.vecCons
          (Matrix.vecCons (-2)
            (Matrix.vecCons (Real.instNeg.neg 0.160330320741428)
              (Matrix.vecCons 0.579597314161362 (Matrix.vecCons 1.484688928981990 Matrix.vecEmpty))))
          Matrix.vecEmpty))))
```

### D006: `HighamBench.p18Method4s3pCATilde`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `570fbbd76f311900e3eac6c2b636e11fde499d1a07e435056fa7d1315ba56904`

Type:

```lean
Fin 4 → Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
  Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
HighamBench.p18CoeffMatAdd HighamBench.p18Method4s3pCA HighamBench.p18Method4s3pCAPerturbation
```

### D007: `HighamBench.p18Method4s3pCBPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `69775b489476c6ecbe51ee265877065402533479b40317d4df09dde4f8da2db5`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty)))
```

### D008: `HighamBench.p18Method4s3pCBTilde`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `edc4091f790eca1e9654480be0f42c18de2a5548f826a454b2348cb689197c1c`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
HighamBench.p18Add HighamBench.p18Method4s3pCB HighamBench.p18Method4s3pCBPerturbation
```

### D009: `HighamBench.p18Method4s3pCCPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bb902564fe6db78b1f9476daa8751e86dd619935a5adbcf51b48687c67abd17e`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
HighamBench.p18CoeffMatVec HighamBench.p18Method4s3pCAPerturbation HighamBench.p18Method4s3pCE
```

### D010: `HighamBench.p18Method4s3pCCTilde`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a88499b88aef26e52ef5c4e4d6233ea321dd23961bbec880c5a25f1ea1bf5810`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
HighamBench.p18Add HighamBench.p18Method4s3pCC HighamBench.p18Method4s3pCCPerturbation
```

### D011: `HighamBench.p18Method4s3pCE`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `760cef8178686529b3bf57f252b31ee6d01bb900cb7f3d86b62948729285d1eb`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
Matrix.vecCons 1 (Matrix.vecCons 1 (Matrix.vecCons 1 (Matrix.vecCons 1 Matrix.vecEmpty)))
```

### D012: `HighamBench.p18PrintedCoeffTolerance`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5aec3c5eac7bdf53b9c6dc8db2ed6bf5a703036add869b4ac24898da40eaf103`

Type:

```lean
Real
```

Fully explicit type:

```lean
Real
```

Definition body (one-level semantic boundary):

```lean
instHDiv.hDiv 2 (instHPow.hPow 10 15)
```

### D013: `HighamBench.p18Add`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a618ade07a852d5fd95ede3f352cb8e1b2123e6bc0d9cc7b34857ff4b7502a01`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y i => instHAdd.hAdd (x i) (y i)
```

### D014: `HighamBench.p18CoeffMatAdd`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `56b7797f070c648392187943e282e7b0bd11f79ea8e2fa3f5d933012f7f63e9c`

Type:

```lean
{s : Nat} → (Fin s → Fin s → Real) → (Fin s → Fin s → Real) → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (A B : Fin s → Fin s → Real) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} A B i j => instHAdd.hAdd (A i j) (B i j)
```

### D015: `HighamBench.p18CorrectedMidpointA._proof_1`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `73b505915b492ba531c87e9764e0d5ad003f6adabc0e4e427d7163ba079d5cba`

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

### D016: `HighamBench.p18Method4s3pCA`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `10abd914ca1f0fb0ac862cd1266e6483df16523e3e8ee700ced315fef2df57d8`

Type:

```lean
Fin 4 → Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
  Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
EquivLike.toFunLike.coe Matrix.of
  (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty))))
    (Matrix.vecCons
      (Matrix.vecCons (Real.instNeg.neg 50470366527530e-15)
        (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty))))
      (Matrix.vecCons
        (Matrix.vecCons 0.368613367355336
          (Matrix.vecCons 0.273504374252976 (Matrix.vecCons 0 (Matrix.vecCons 0 Matrix.vecEmpty))))
        (Matrix.vecCons
          (Matrix.vecCons 1.803794668975043
            (Matrix.vecCons 97485042980759e-15
              (Matrix.vecCons (Real.instNeg.neg 1.895660952342050) (Matrix.vecCons 0 Matrix.vecEmpty))))
          Matrix.vecEmpty))))
```

### D017: `HighamBench.p18Method4s3pCB`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fe369ccc2bc8ba45c478f5b78677aea891e401e70146e25b10f8acd963b2c7a8`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
Matrix.vecCons 2837446974069e-15
  (Matrix.vecCons 0.336264433650450
    (Matrix.vecCons 0.806376720267787 (Matrix.vecCons (Real.instNeg.neg 0.145478600892306) Matrix.vecEmpty)))
```

### D018: `HighamBench.p18Method4s3pCC`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f51ca73d3629dd2d9bf2f0f30be4198518b61e4a9795d5ae902087e338f38bd0`

Type:

```lean
Fin 4 → Real
```

Fully explicit type:

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

Definition body (one-level semantic boundary):

```lean
HighamBench.p18CoeffMatVec HighamBench.p18Method4s3pCA HighamBench.p18Method4s3pCE
```

### D019: `HighamBench.p18PrintedCoeffTolerance._proof_1`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `e6ff41ab4cd4feb1e53af23280a19cb8ecc3d04041572ad1706c9b5bf65fd661`

Type:

```lean
(instHAdd.hAdd 9 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D020: `And`

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

### D021: `DivInvMonoid.toDiv`

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

### D022: `Eq`

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

### D023: `Fin`

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

### D024: `HDiv.hDiv`

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

### D025: `HSub.hSub`

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

### D026: `LE.le`

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

### D027: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D028: `Nat`

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

### D029: `Nat.instAtLeastTwoHAddOfNat`

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

### D030: `Nat.instNeZeroSucc`

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

### D031: `OfNat.ofNat`

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

### D032: `One.toOfNat1`

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

### D033: `Real`

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

### D034: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D035: `Real.instDivInvMonoid`

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

### D036: `Real.instLE`

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

### D037: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D038: `Real.instNatCast`

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

### D039: `Real.instOne`

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

### D040: `Real.instSub`

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

### D041: `Real.instZero`

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

### D042: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D043: `Zero.toOfNat0`

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

### D044: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D045: `instHDiv`

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

### D046: `instHSub`

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

### D047: `instOfNatAtLeastTwo`

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

### D048: `instOfNatNat`

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

### D049: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D050: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Fully explicit type:

```lean
{F : Sort u_1} →
  {α : outParam.{u_2 + 1} (Sort u_2)} →
    {β : outParam.{max u_2 (u_3 + 1)} (α → Sort u_3)} → [self : DFunLike.{u_1, u_2, u_3} F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D051: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

Fully explicit type:

```lean
(α : Sort u_1) → (β : Sort u_2) → Sort (max (max 1 u_1) u_2)
```

### D052: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike.{max (max 1 v) u, u, v} (Equiv.{u, v} α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D053: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Fully explicit type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike.{u_1, u_3, u_4} E α β] → FunLike.{u_1, u_3, u_4} E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D054: `Fin.fintype`

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

### D055: `Finset.sum`

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

### D056: `Finset.univ`

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

### D057: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D058: `HPow.hPow`

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

### D059: `Matrix`

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

### D060: `Matrix.of`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2fd11c1f258b666a5be58a830ae21c93bc674ab3014a8a722530d141dddb3638`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Equiv (m → n → α) (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {α : Type v} →
      Equiv.{max (max (u_2 + 1) (u_3 + 1)) (v + 1), max (max (v + 1) (u_3 + 1)) (u_2 + 1)} (m → n → α)
        (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} => Equiv.refl (m → n → α)
```

### D061: `Matrix.vecCons`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fin.VecNotation`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6d598529744fc7ed189026f2f83ca39c93930021427c51096eca547bc6750a25`

Type:

```lean
{α : Type u} → {n : Nat} → α → (Fin n → α) → Fin n.succ → α
```

Fully explicit type:

```lean
{α : Type u} → {n : Nat} → (h : α) → (t : Fin n → α) → Fin (Nat.succ n) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {n} h t => Fin.cons h t
```

### D062: `Matrix.vecEmpty`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fin.VecNotation`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `43307adb40ece2d70b6319d8e8f7f5551cf96af32e64c2288a2ca8610f456de1`

Type:

```lean
{α : Type u} → Fin 0 → α
```

Fully explicit type:

```lean
{α : Type u} → Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} => Fin.elim0
```

### D063: `Monoid.toNatPow`

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

### D064: `NNRatCast.toOfScientific`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Ring.Unbundled.Rat`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cd07bd77da24569af2062c2bed58ee77100bffdb8fcba677c84f7bb0f0e0e218`

Type:

```lean
{K : Type u_1} → [NNRatCast K] → OfScientific K
```

Fully explicit type:

```lean
{K : Type u_1} → [NNRatCast.{u_1} K] → OfScientific.{u_1} K
```

Definition body (one-level semantic boundary):

```lean
fun {K} [NNRatCast K] => { ofScientific := fun m b d => NNRat.cast ⟨Rat.ofScientific m b d, ⋯⟩ }
```

### D065: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Neg.{u} α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D066: `OfScientific.ofScientific`

- Role: `external-frontier`
- Owner module: `Init.Data.OfScientific`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2e86ffcefde3a128235ad8657546e1e75f8adc5e0f719edfcd04466913c5ad0e`

Type:

```lean
{α : Type u} → [self : OfScientific α] → Nat → Bool → Nat → α
```

Fully explicit type:

```lean
{α : Type u} → [self : OfScientific.{u} α] → (mantissa : Nat) → (exponentSign : Bool) → (decimalExponent : Nat) → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : OfScientific α] => self.1
```

### D067: `Real.instAddCommMonoid`

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

### D068: `Real.instMonoid`

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

### D069: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D070: `Real.instNNRatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `305e7c9b667d948e846364178de3be991ff25bd848da3810d89241f9b532b584`

Type:

```lean
NNRatCast Real
```

Fully explicit type:

```lean
NNRatCast.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ nnratCast := fun q => { cauchy := q.cast } }
```

### D071: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Fully explicit type:

```lean
Neg.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D072: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D073: `instHPow`

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

### D074: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D075: `Nat.AtLeastTwo`

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

### D076: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D077: `instAddNat`

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

### D078: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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
