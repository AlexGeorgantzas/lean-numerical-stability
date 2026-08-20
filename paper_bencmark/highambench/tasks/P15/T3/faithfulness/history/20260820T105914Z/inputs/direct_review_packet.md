# Declaration dossier for P15-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p15_t3_blr_lu_solve_backward_error {n : ℕ}
    (A L U factorError lowerError upperError : P15Matrix n)
    (v y computed rhsLower rhsUpper : P15Vector n)
    (xi epsilon gammaP gammaC factorRemainder : ℝ)
    (hgammaP : 0 ≤ gammaP) (hgammaPsmall : gammaP < 1)
    (hgammaC : 0 ≤ gammaC)
    (hfactor : p15MatMul L U = A + factorError)
    (hlower : p15MatVec (L + lowerError) y = v + rhsLower)
    (hupper : p15MatVec (U + upperError) computed = y + rhsUpper)
    (hfactorBound :
      p15FrobNorm factorError ≤
        (xi * epsilon + gammaP) * p15FrobNorm A +
          gammaC * p15FrobNorm L * p15FrobNorm U + factorRemainder)
    (hlowerBound : p15FrobNorm lowerError ≤ gammaC * p15FrobNorm L)
    (hupperBound : p15FrobNorm upperError ≤ gammaC * p15FrobNorm U)
    (hrhsLower : p15VecNorm rhsLower ≤ gammaP * p15VecNorm v)
    (hrhsUpper : p15VecNorm rhsUpper ≤ gammaP * p15VecNorm y) :
    p15MatVec
        (A + p15ComposedMatrixError factorError lowerError upperError L U)
        computed =
      v + p15ComposedRhsError rhsLower rhsUpper L lowerError ∧
    p15FrobNorm
        (p15ComposedMatrixError factorError lowerError upperError L U) ≤
      (xi * epsilon + gammaP) * p15FrobNorm A +
        (3 * gammaC + gammaC ^ 2) * p15FrobNorm L * p15FrobNorm U +
          factorRemainder ∧
    p15VecNorm (p15ComposedRhsError rhsLower rhsUpper L lowerError) ≤
      gammaP * p15VecNorm v +
        (gammaP * (1 + gammaC) ^ 2 / (1 - gammaP)) *
          p15FrobNorm L * p15FrobNorm U * p15VecNorm computed
```

## Elaborated target type

```lean
∀ {n : Nat} (A L U factorError lowerError upperError : HighamBench.P15Matrix n)
  (v y computed rhsLower rhsUpper : HighamBench.P15Vector n) (xi epsilon gammaP gammaC factorRemainder : Real),
  Real.instLE.le 0 gammaP →
    Real.instLT.lt gammaP 1 →
      Real.instLE.le 0 gammaC →
        Eq (HighamBench.p15MatMul L U) (instHAdd.hAdd A factorError) →
          Eq (HighamBench.p15MatVec (instHAdd.hAdd L lowerError) y) (instHAdd.hAdd v rhsLower) →
            Eq (HighamBench.p15MatVec (instHAdd.hAdd U upperError) computed) (instHAdd.hAdd y rhsUpper) →
              Real.instLE.le (HighamBench.p15FrobNorm factorError)
                  (instHAdd.hAdd
                    (instHAdd.hAdd
                      (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi epsilon) gammaP) (HighamBench.p15FrobNorm A))
                      (instHMul.hMul (instHMul.hMul gammaC (HighamBench.p15FrobNorm L)) (HighamBench.p15FrobNorm U)))
                    factorRemainder) →
                Real.instLE.le (HighamBench.p15FrobNorm lowerError) (instHMul.hMul gammaC (HighamBench.p15FrobNorm L)) →
                  Real.instLE.le (HighamBench.p15FrobNorm upperError)
                      (instHMul.hMul gammaC (HighamBench.p15FrobNorm U)) →
                    Real.instLE.le (HighamBench.p15VecNorm rhsLower) (instHMul.hMul gammaP (HighamBench.p15VecNorm v)) →
                      Real.instLE.le (HighamBench.p15VecNorm rhsUpper)
                          (instHMul.hMul gammaP (HighamBench.p15VecNorm y)) →
                        And
                          (Eq
                            (HighamBench.p15MatVec
                              (instHAdd.hAdd A
                                (HighamBench.p15ComposedMatrixError factorError lowerError upperError L U))
                              computed)
                            (instHAdd.hAdd v (HighamBench.p15ComposedRhsError rhsLower rhsUpper L lowerError)))
                          (And
                            (Real.instLE.le
                              (HighamBench.p15FrobNorm
                                (HighamBench.p15ComposedMatrixError factorError lowerError upperError L U))
                              (instHAdd.hAdd
                                (instHAdd.hAdd
                                  (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi epsilon) gammaP)
                                    (HighamBench.p15FrobNorm A))
                                  (instHMul.hMul
                                    (instHMul.hMul (instHAdd.hAdd (instHMul.hMul 3 gammaC) (instHPow.hPow gammaC 2))
                                      (HighamBench.p15FrobNorm L))
                                    (HighamBench.p15FrobNorm U)))
                                factorRemainder))
                            (Real.instLE.le
                              (HighamBench.p15VecNorm (HighamBench.p15ComposedRhsError rhsLower rhsUpper L lowerError))
                              (instHAdd.hAdd (instHMul.hMul gammaP (HighamBench.p15VecNorm v))
                                (instHMul.hMul
                                  (instHMul.hMul
                                    (instHMul.hMul
                                      (instHDiv.hDiv (instHMul.hMul gammaP (instHPow.hPow (instHAdd.hAdd 1 gammaC) 2))
                                        (instHSub.hSub 1 gammaP))
                                      (HighamBench.p15FrobNorm L))
                                    (HighamBench.p15FrobNorm U))
                                  (HighamBench.p15VecNorm computed)))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A L U factorError lowerError upperError : HighamBench.P15Matrix n)
  (v y computed rhsLower rhsUpper : HighamBench.P15Vector n) (xi epsilon gammaP gammaC factorRemainder : Real)
  (hgammaP :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) gammaP)
  (hgammaPsmall :
    @LT.lt.{0} Real Real.instLT gammaP (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hgammaC :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) gammaC)
  (hfactor :
    @Eq.{1} (HighamBench.P15Matrix n) (@HighamBench.p15MatMul n L U)
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
        (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) A
        factorError))
  (hlower :
    @Eq.{1} (HighamBench.P15Vector n)
      (@HighamBench.p15MatVec n
        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
          (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) L
          lowerError)
        y)
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Vector n) (HighamBench.P15Vector n) (HighamBench.P15Vector n)
        (@instHAdd.{0} (HighamBench.P15Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        v rhsLower))
  (hupper :
    @Eq.{1} (HighamBench.P15Vector n)
      (@HighamBench.p15MatVec n
        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
          (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) U
          upperError)
        computed)
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Vector n) (HighamBench.P15Vector n) (HighamBench.P15Vector n)
        (@instHAdd.{0} (HighamBench.P15Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        y rhsUpper))
  (hfactorBound :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm n factorError)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi epsilon) gammaP)
            (@HighamBench.p15FrobNorm n A))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
              (@HighamBench.p15FrobNorm n L))
            (@HighamBench.p15FrobNorm n U)))
        factorRemainder))
  (hlowerBound :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm n lowerError)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC (@HighamBench.p15FrobNorm n L)))
  (hupperBound :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm n upperError)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC (@HighamBench.p15FrobNorm n U)))
  (hrhsLower :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15VecNorm n rhsLower)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP (@HighamBench.p15VecNorm n v)))
  (hrhsUpper :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15VecNorm n rhsUpper)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP (@HighamBench.p15VecNorm n y))),
  And
    (@Eq.{1} (HighamBench.P15Vector n)
      (@HighamBench.p15MatVec n
        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
          (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) A
          (@HighamBench.p15ComposedMatrixError n factorError lowerError upperError L U))
        computed)
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Vector n) (HighamBench.P15Vector n) (HighamBench.P15Vector n)
        (@instHAdd.{0} (HighamBench.P15Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        v (@HighamBench.p15ComposedRhsError n rhsLower rhsUpper L lowerError)))
    (And
      (@LE.le.{0} Real Real.instLE
        (@HighamBench.p15FrobNorm n (@HighamBench.p15ComposedMatrixError n factorError lowerError upperError L U))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi epsilon) gammaP)
              (@HighamBench.p15FrobNorm n A))
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
                (@HighamBench.p15FrobNorm n L))
              (@HighamBench.p15FrobNorm n U)))
          factorRemainder))
      (@LE.le.{0} Real Real.instLE
        (@HighamBench.p15VecNorm n (@HighamBench.p15ComposedRhsError n rhsLower rhsUpper L lowerError))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP (@HighamBench.p15VecNorm n v))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaC)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaP))
                (@HighamBench.p15FrobNorm n L))
              (@HighamBench.p15FrobNorm n U))
            (@HighamBench.p15VecNorm n computed)))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P15Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P15Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P15Matrix`

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

### D002: `HighamBench.P15Vector`

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

### D003: `HighamBench.p15ComposedMatrixError`

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

### D004: `HighamBench.p15ComposedRhsError`

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

### D005: `HighamBench.p15FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `ba1b58b4e7fdbcda54fe1a9ee4d2ebd9f8d43b80907403bf6ea885fff386083f`
- Reuse SHA-256: `6a91bf9c84bfcbacb1ea3b560b005b8de47822ea8755913ca95adfd0a9e1869d`

Hash-verified prior interpretation:

The function returns the norm field of Matrix.frobeniusNormedRing for the supplied finite square real matrix.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `HighamBench.p15MatMul`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `82a32c03123a1b58cce8a2734d2ddfed6b499db78b5c4e68d56caf8636e3bb0e`
- Reuse SHA-256: `84739a36864c3daa138eb88394c6cd946e85312d57564909c51a246f55efdca9`

Hash-verified prior interpretation:

Its (i,j) entry is the finite sum over every k in Fin n of A i k multiplied by B k j.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `HighamBench.p15MatVec`

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

### D008: `HighamBench.p15VecNorm`

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

### D009: `And`

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

### D010: `DivInvMonoid.toDiv`

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

### D011: `Eq`

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

### D012: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `e737486c67f9dbea0f2bcbe83634be51e58d0d92cf1cfb23c776a2f4a7e59c97`

Hash-verified prior interpretation:

Fin n is the finite bounded index type with n elements.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `HAdd.hAdd`

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

### D014: `HDiv.hDiv`

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

### D015: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `3572f804982d8e02cdb90fefa4ba09c86e248bb74e338dbccdf5e34e05538eb1`

Hash-verified prior interpretation:

This abbreviation selects the binary multiplication operation from an HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `HPow.hPow`

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

### D017: `HSub.hSub`

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

### D018: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `ba63226d47485a0686b361b82ac9938d26080ba88527d42eda0b433bc8a394af`

Hash-verified prior interpretation:

This abbreviation selects the non-strict order relation from an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `LT.lt`

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

### D020: `Matrix.add`

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

### D021: `Monoid.toNatPow`

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

### D022: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `ed4370998b8d9dbde5a6b5b4d574c7c396509b78ab3bca72cc8b612c8d4357de`

Hash-verified prior interpretation:

Nat supplies the target's matrix-size parameter n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Nat.instAtLeastTwoHAddOfNat`

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

### D024: `Nat.instNeZeroSucc`

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

### D025: `OfNat.ofNat`

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

### D026: `One.toOfNat1`

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

### D027: `Pi.instAdd`

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

### D028: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `33b5a5009512de034973263c33e6107bb25484411cca37b571a00491e1dc8681`

Hash-verified prior interpretation:

Real is the scalar type of every matrix entry and the codomain of the norm.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Real.instAdd`

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

### D030: `Real.instDivInvMonoid`

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

### D031: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `6005e17e5289b370343d36a1373b58f2243742c58aacd4708762ee2b8f8403e7`

Hash-verified prior interpretation:

This instance installs the ordinary real order Real.le as LE Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `Real.instLT`

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

### D033: `Real.instMonoid`

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

### D034: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `bc3810a73f8d595e308695fedc5608856bba227a7ac7eb8d39a9aea9023506a9`

Hash-verified prior interpretation:

This instance installs ordinary real multiplication as Mul Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Real.instNatCast`

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

### D036: `Real.instOne`

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

### D037: `Real.instSub`

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

### D038: `Real.instZero`

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

### D039: `Zero.toOfNat0`

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

### D040: `instHAdd`

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

### D041: `instHDiv`

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

### D042: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `3b55530701c5ce29596c1bf762341e1b88002ec2ffa277efcd64bb97025789ef`

Hash-verified prior interpretation:

This construction turns a homogeneous Mul instance into an HMul instance by using the same multiplication operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D043: `instHPow`

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

### D044: `instHSub`

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

### D045: `instOfNatAtLeastTwo`

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

### D046: `instOfNatNat`

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

### D047: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `8457a8d4ad0d78e4cf0c14700f1480df720d518fa77b11738bbce3325090eee5`

Hash-verified prior interpretation:

This instance enumerates all elements of Fin n using finRange n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D048: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `fa5c7c8cb376d6defbad0c4b48ccd19139f66e98f56c7ce2c55d211e8fbea4d6`

Hash-verified prior interpretation:

Finset.sum maps a function over a finite set and combines the results with commutative-monoid addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D049: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `d34f479cade36f2caaaeb813b8e491070246e5aa1c89610ed2939d9020326955`

Hash-verified prior interpretation:

Finset.univ selects all elements supplied by a Fintype instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D050: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`
- Reuse SHA-256: `9f65add277408970718ba49cc0f20472a0d50ce11ba23dfae35afc9b92aa201a`

Hash-verified prior interpretation:

Matrix m n alpha is definitionally the function type m -> n -> alpha.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D051: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`
- Reuse SHA-256: `9c4583ea78f575b045680ee6d7f1b24bc850c7fc1e7c142d50ce821c0c823c4f`

Hash-verified prior interpretation:

This instance combines the matrix ring operations with the norm inherited from Matrix.frobeniusSeminormedAddCommGroup and includes Frobenius-norm submultiplicativity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D052: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`
- Reuse SHA-256: `d85b24047182364c6d653ef7a6dc1b8fbf56132f7c05e7422dff98364ef3b656`

Hash-verified prior interpretation:

This abbreviation projects the norm function from a Norm instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D053: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`
- Reuse SHA-256: `7b650485a13ebb4f91630d4a15ff66e9b6446a56cf1c892594741b7c2e7cc33e`

Hash-verified prior interpretation:

This abbreviation projects the Norm structure contained in a NormedRing.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D054: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `9535fc8b7317cb6988393fc4e210d35fb791659d51385e14049518b93614fcee`

Hash-verified prior interpretation:

This instance supplies real zero and commutative addition for finite sums.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D055: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`
- Reuse SHA-256: `6cd230752e597453d6b57a967a53b590162a3a2cf6278ed6e067438550193c58`

Hash-verified prior interpretation:

This instance equips Real with the RCLike structure used by the Frobenius matrix norm construction.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D056: `Real.sqrt`

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

### D057: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`
- Reuse SHA-256: `44a573b68a98935896e14a575844e3cd0229658a863bdabc933be0e006f683c0`

Hash-verified prior interpretation:

This instance decides equality of Fin n indices by deciding equality of their underlying natural values.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
