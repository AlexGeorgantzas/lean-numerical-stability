# Declaration dossier for P08-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p08_t3_lemma_4_3_exact_residual_bound
    {n : ℕ}
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (roundoff :
      P08Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall :
      constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2) :
    ∀ m i,
      |p08ExactResidualAfterCorrection run m i| ≤
        p08Lemma43Bound constants m i
```

## Elaborated target type

```lean
∀ {n : Nat} (dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds)
  (run : HighamBench.P08IterativeRefinementRun n) (norm : HighamBench.P08AbsoluteMonotoneNorm n)
  (constants : HighamBench.P08Lemma43Constants run norm dimensionBounds)
  (roundoff : HighamBench.P08Lemma43RoundoffAnalysis run norm dimensionBounds constants),
  Real.instLE.le (instHMul.hMul (instHMul.hMul constants.c8 run.u) (HighamBench.p08KappaInverse run norm)) (1 / 2) →
    ∀ (m : Nat) (i : Fin n),
      Real.instLE.le (abs (HighamBench.p08ExactResidualAfterCorrection run m i))
        (HighamBench.p08Lemma43Bound constants m i)
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds)
  (run : HighamBench.P08IterativeRefinementRun n) (norm : HighamBench.P08AbsoluteMonotoneNorm n)
  (constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds)
  (roundoff : @HighamBench.P08Lemma43RoundoffAnalysis n run norm dimensionBounds constants)
  (hsmall :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P08Lemma43Constants.c8 n run norm dimensionBounds constants)
          (@HighamBench.P08IterativeRefinementRun.u n run))
        (@HighamBench.p08KappaInverse n run norm))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  (m : Nat) (i : Fin n),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p08ExactResidualAfterCorrection n run m i))
    (@HighamBench.p08Lemma43Bound n run norm dimensionBounds constants m i)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P08Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P08Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P08AbsoluteMonotoneNorm`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `dd44ecce5ee7bc279fb3789632aa3a89a4eceaab370a1801dca66ce25c418532`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D002: `HighamBench.P08DimensionOnlyConstantBounds`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4dd8b7025f930376404b6a7dddeea3bb578073682211d233857649dc325a5f68`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D003: `HighamBench.P08IterativeRefinementRun`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `74c20dc7827a5cbd4fe74d9eb34378daa2c4739f993fcee66863d0ec4aff993d`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D004: `HighamBench.P08IterativeRefinementRun.u`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d92d8e8ea4be1097fd2e64076c9c9d9d41d04452c46a6bb284a4fd8a0351fae4`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D005: `HighamBench.P08Lemma43Constants`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `0adef817138f4a0901fa7c892048022fa14bf009fedc27ce043ae20778a33f27`

Type:

```lean
{n : Nat} →
  HighamBench.P08IterativeRefinementRun n →
    HighamBench.P08AbsoluteMonotoneNorm n → HighamBench.P08DimensionOnlyConstantBounds → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (run : HighamBench.P08IterativeRefinementRun n) →
    (norm : HighamBench.P08AbsoluteMonotoneNorm n) →
      (dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds) → Type
```

### D006: `HighamBench.P08Lemma43Constants.c8`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b24d536ae870e768229a42191b43bbaa320bac9410946d6c7ba49140378bcc32`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.11
```

### D007: `HighamBench.P08Lemma43RoundoffAnalysis`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `17c73f1751e8c2ae2ee80c48aaf56093805596b4f0200ba2e61484f5862dda1d`

Type:

```lean
{n : Nat} →
  (run : HighamBench.P08IterativeRefinementRun n) →
    (norm : HighamBench.P08AbsoluteMonotoneNorm n) →
      (dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds) →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (run : HighamBench.P08IterativeRefinementRun n) →
    (norm : HighamBench.P08AbsoluteMonotoneNorm n) →
      (dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds) →
        (constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Type
```

### D008: `HighamBench.p08ExactResidualAfterCorrection`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `89c907d225e6345e34dadb67383fc546189772a4d5602bb4b9ab06ae0758fad1`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P08IterativeRefinementRun n) → (m : Nat) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run m =>
  HighamBench.p08VecSub (HighamBench.p08MatVec run.A (HighamBench.p08VecSub (run.iterate m) (run.correction m))) run.b
```

### D009: `HighamBench.p08KappaInverse`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bfd0f39983da4c12e3f750ed71076fbdd2f5522eadc206111adf42edf2facde8`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → HighamBench.P08AbsoluteMonotoneNorm n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P08IterativeRefinementRun n) → (norm : HighamBench.P08AbsoluteMonotoneNorm n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run norm =>
  norm.matrixNorm (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A) (HighamBench.p08AbsMatrix run.Ainv))
```

### D010: `HighamBench.p08Lemma43Bound`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3059b4edb0e06983e98da42488edf26e73e7a05fb9285f72affa64f8f765da55`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → (m : Nat) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} {dimensionBounds} constants m =>
  HighamBench.p08VecAdd
    (HighamBench.p08MatVec (HighamBench.p08MatPow (HighamBench.p08Lemma43Propagation constants) m)
      (HighamBench.p08Lemma43InitialVector constants))
    (HighamBench.p08Lemma43StationaryVector constants)
```

### D011: `HighamBench.P08AbsoluteMonotoneNorm.matrixNorm`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cb6f2c04a418b2caa76e756725fcea42ee330eb2025b1c853e005a409b93b65b`

Type:

```lean
{n : Nat} → HighamBench.P08AbsoluteMonotoneNorm n → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08AbsoluteMonotoneNorm n) → (Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D012: `HighamBench.P08AbsoluteMonotoneNorm.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `7dd24e6fd070f0254a34fafc339c24a872f093b562989902deb8ec0012c991d5`

Type:

```lean
{n : Nat} →
  (vecNorm : (Fin n → Real) → Real) →
    (matrixNorm : (Fin n → Fin n → Real) → Real) →
      (∀ (x : Fin n → Real), Real.instLE.le 0 (vecNorm x)) →
        (∀ (x : Fin n → Real), Iff (Eq (vecNorm x) 0) (Eq x 0)) →
          (∀ (x y : Fin n → Real),
              Real.instLE.le (vecNorm (HighamBench.p08VecAdd x y)) (instHAdd.hAdd (vecNorm x) (vecNorm y))) →
            (∀ (a : Real) (x : Fin n → Real),
                Eq (vecNorm (HighamBench.p08VecScale a x)) (instHMul.hMul (abs a) (vecNorm x))) →
              (∀ (x : Fin n → Real), Eq (vecNorm (HighamBench.p08AbsVec x)) (vecNorm x)) →
                (∀ (x y : Fin n → Real),
                    (∀ (i : Fin n), Real.instLE.le (abs (x i)) (abs (y i))) → Real.instLE.le (vecNorm x) (vecNorm y)) →
                  (∀ (j : Fin n), Eq (vecNorm (HighamBench.p08BasisVector j)) 1) →
                    (∀ (A : Fin n → Fin n → Real), Real.instLE.le 0 (matrixNorm A)) →
                      (∀ (A : Fin n → Fin n → Real) (x : Fin n → Real),
                          Real.instLE.le (vecNorm (HighamBench.p08MatVec A x))
                            (instHMul.hMul (matrixNorm A) (vecNorm x))) →
                        (∀ (A : Fin n → Fin n → Real) (c : Real),
                            Real.instLE.le 0 c →
                              (∀ (x : Fin n → Real),
                                  Real.instLE.le (vecNorm (HighamBench.p08MatVec A x)) (instHMul.hMul c (vecNorm x))) →
                                Real.instLE.le (matrixNorm A) c) →
                          HighamBench.P08AbsoluteMonotoneNorm n
```

Fully explicit type:

```lean
{n : Nat} →
  (vecNorm : (Fin n → Real) → Real) →
    (matrixNorm : (Fin n → Fin n → Real) → Real) →
      (vec_norm_nonnegative :
          ∀ (x : Fin n → Real),
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (vecNorm x)) →
        (vec_norm_eq_zero :
            ∀ (x : Fin n → Real),
              Iff (@Eq.{1} Real (vecNorm x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                (@Eq.{1} (Fin n → Real) x
                  (@OfNat.ofNat.{0} (Fin n → Real) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (Fin n → Real)
                      (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero))))) →
          (vec_norm_add :
              ∀ (x y : Fin n → Real),
                @LE.le.{0} Real Real.instLE (vecNorm (@HighamBench.p08VecAdd n x y))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (vecNorm x) (vecNorm y))) →
            (vec_norm_scale :
                ∀ (a : Real) (x : Fin n → Real),
                  @Eq.{1} Real (vecNorm (@HighamBench.p08VecScale n a x))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@abs.{0} Real Real.lattice Real.instAddGroup a) (vecNorm x))) →
              (vec_norm_absolute :
                  ∀ (x : Fin n → Real), @Eq.{1} Real (vecNorm (@HighamBench.p08AbsVec n x)) (vecNorm x)) →
                (vec_norm_monotone :
                    ∀ (x y : Fin n → Real),
                      (∀ (i : Fin n),
                          @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (x i))
                            (@abs.{0} Real Real.lattice Real.instAddGroup (y i))) →
                        @LE.le.{0} Real Real.instLE (vecNorm x) (vecNorm y)) →
                  (basis_normalized :
                      ∀ (j : Fin n),
                        @Eq.{1} Real (vecNorm (@HighamBench.p08BasisVector n j))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                    (matrix_norm_nonnegative :
                        ∀ (A : Fin n → Fin n → Real),
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (matrixNorm A)) →
                      (matrix_action_bound :
                          ∀ (A : Fin n → Fin n → Real) (x : Fin n → Real),
                            @LE.le.{0} Real Real.instLE (vecNorm (@HighamBench.p08MatVec n A x))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (matrixNorm A)
                                (vecNorm x))) →
                        (matrix_norm_least :
                            ∀ (A : Fin n → Fin n → Real) (c : Real),
                              @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
                                (∀ (x : Fin n → Real),
                                    @LE.le.{0} Real Real.instLE (vecNorm (@HighamBench.p08MatVec n A x))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                                        (vecNorm x))) →
                                  @LE.le.{0} Real Real.instLE (matrixNorm A) c) →
                          HighamBench.P08AbsoluteMonotoneNorm n
```

### D013: `HighamBench.P08DimensionOnlyConstantBounds.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `610355c3cbe90d966e947b5d8cecd1135a6194218b00313b1e2510582dcd4d80`

Type:

```lean
(scalar matrixEntry : Nat → Real) →
  (∀ (n : Nat), Real.instLE.le 0 (scalar n)) →
    (∀ (n : Nat), Real.instLE.le 0 (matrixEntry n)) → HighamBench.P08DimensionOnlyConstantBounds
```

Fully explicit type:

```lean
(scalar matrixEntry : Nat → Real) →
  (scalar_nonnegative :
      ∀ (n : Nat),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (scalar n)) →
    (matrixEntry_nonnegative :
        ∀ (n : Nat),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (matrixEntry n)) →
      HighamBench.P08DimensionOnlyConstantBounds
```

### D014: `HighamBench.P08IterativeRefinementRun.A`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d7cdfae3226ea26062f3da03b4f8a09cc08e415f9cfcab71b8e6d164e93f07b6`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D015: `HighamBench.P08IterativeRefinementRun.Ainv`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fbf658b7d4cc30fd907c3d1b54f65373c09d2022e41ba7e215476d43daf6c6de`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D016: `HighamBench.P08IterativeRefinementRun.b`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `910e89d666adca66e589b98cb1b747e0a33a3e2fab50bc88cf50fdd1eea6fae6`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.10
```

### D017: `HighamBench.P08IterativeRefinementRun.correction`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `619684715a0a5fdce031c4a8c55f8ba7de76d0491827935369921dbed9a221be`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Nat → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.18
```

### D018: `HighamBench.P08IterativeRefinementRun.iterate`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3e59b00c78203e511203f3ad3405ec217a1ed95a250eff9fabcf7dcbf5932db0`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Nat → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.16
```

### D019: `HighamBench.P08IterativeRefinementRun.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e7b19ac32cfc452db53a1f4beb6a49aefbcf0dbd3a5e2b7fcf3f357afc041fc5`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    HighamBench.P08ResidualPrecision →
      (u : Real) →
        Real.instLT.lt 0 u →
          Real.instLE.le (instHMul.hMul n.cast u) (1 / 100) →
            (A Ainv : Fin n → Fin n → Real) →
              Eq (HighamBench.p08MatMul Ainv A) (HighamBench.p08IdMatrix n) →
                Eq (HighamBench.p08MatMul A Ainv) (HighamBench.p08IdMatrix n) →
                  (b exactSolution : Fin n → Real) →
                    Eq (HighamBench.p08MatVec A exactSolution) b →
                      (C1 : Fin n → Fin n → Real) →
                        HighamBench.p08MatNonnegative C1 →
                          (initialSolve : HighamBench.P08ColumnPivotedSolveCertificate A b C1 u) →
                            (iterate computedResidual correction : Nat → Fin n → Real) →
                              (Eq (iterate 0) fun x => 0) →
                                Eq (iterate 1) initialSolve.output →
                                  (Eq (computedResidual 0) fun i => Real.instNeg.neg (b i)) →
                                    (Eq (correction 0) fun i => Real.instNeg.neg (iterate 1 i)) →
                                      (correctionSolve :
                                          (m : Nat) →
                                            HighamBench.P08ColumnPivotedSolveCertificate A
                                              (computedResidual (instHAdd.hAdd m 1)) C1 u) →
                                        (∀ (m : Nat), Eq (correction (instHAdd.hAdd m 1)) (correctionSolve m).output) →
                                          (updateError : Nat → Fin n → Real) →
                                            (∀ (m : Nat),
                                                Eq (iterate (instHAdd.hAdd m 1))
                                                  (HighamBench.p08VecAdd
                                                    (HighamBench.p08VecSub (iterate m) (correction m))
                                                    (updateError (instHAdd.hAdd m 1)))) →
                                              (∀ (m : Nat) (i : Fin n),
                                                  Real.instLE.le (abs (updateError (instHAdd.hAdd m 1) i))
                                                    (instHMul.hMul u
                                                      (abs (instHSub.hSub (iterate m i) (correction m i))))) →
                                                HighamBench.P08IterativeRefinementRun n
```

Fully explicit type:

```lean
{n : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (precision : HighamBench.P08ResidualPrecision) →
      (u : Real) →
        (u_pos :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u) →
          (dimension_roundoff_small :
              @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast n) u)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 100)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 100) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))))))) →
            (A Ainv : Fin n → Fin n → Real) →
              (inverse_left :
                  @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p08MatMul n Ainv A) (HighamBench.p08IdMatrix n)) →
                (inverse_right :
                    @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p08MatMul n A Ainv) (HighamBench.p08IdMatrix n)) →
                  (b exactSolution : Fin n → Real) →
                    (exact_system : @Eq.{1} (Fin n → Real) (@HighamBench.p08MatVec n A exactSolution) b) →
                      (C1 : Fin n → Fin n → Real) →
                        (C1_nonnegative : @HighamBench.p08MatNonnegative n C1) →
                          (initialSolve : @HighamBench.P08ColumnPivotedSolveCertificate n A b C1 u) →
                            (iterate computedResidual correction : Nat → Fin n → Real) →
                              (iterate_zero :
                                  @Eq.{1} (Fin n → Real)
                                    (iterate (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    fun (x : Fin n) =>
                                    @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                (iterate_one :
                                    @Eq.{1} (Fin n → Real)
                                      (iterate (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@HighamBench.P08ColumnPivotedSolveCertificate.output n A b C1 u initialSolve)) →
                                  (residual_zero :
                                      @Eq.{1} (Fin n → Real)
                                        (computedResidual (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        fun (i : Fin n) => @Neg.neg.{0} Real Real.instNeg (b i)) →
                                    (correction_zero :
                                        @Eq.{1} (Fin n → Real)
                                          (correction (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          fun (i : Fin n) =>
                                          @Neg.neg.{0} Real Real.instNeg
                                            (iterate (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) i)) →
                                      (correctionSolve :
                                          (m : Nat) →
                                            @HighamBench.P08ColumnPivotedSolveCertificate n A
                                              (computedResidual
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              C1 u) →
                                        (correction_output :
                                            ∀ (m : Nat),
                                              @Eq.{1} (Fin n → Real)
                                                (correction
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (@HighamBench.P08ColumnPivotedSolveCertificate.output n A
                                                  (computedResidual
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  C1 u (correctionSolve m))) →
                                          (updateError : Nat → Fin n → Real) →
                                            (update_equation :
                                                ∀ (m : Nat),
                                                  @Eq.{1} (Fin n → Real)
                                                    (iterate
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (@HighamBench.p08VecAdd n
                                                      (@HighamBench.p08VecSub n (iterate m) (correction m))
                                                      (updateError
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          m
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))))) →
                                              (update_error_bound :
                                                  ∀ (m : Nat) (i : Fin n),
                                                    @LE.le.{0} Real Real.instLE
                                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                                        (updateError
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) m
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          i))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) u
                                                        (@abs.{0} Real Real.lattice Real.instAddGroup
                                                          (@HSub.hSub.{0, 0, 0} Real Real Real
                                                            (@instHSub.{0} Real Real.instSub) (iterate m i)
                                                            (correction m i))))) →
                                                HighamBench.P08IterativeRefinementRun n
```

### D020: `HighamBench.P08Lemma43Constants.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `4c70837cf08b2e18d98b6610cf5e128d140ba43a36c9028930ab1b413ccb483b`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (C2 C6 C7 C8 C9 C10 C11 C12 : Fin n → Fin n → Real) →
          (c1 c5 c8 : Real) →
            (C2ResolventInv C11ResolventInv : Fin n → Fin n → Real) →
              Eq c1 (norm.matrixNorm run.C1) →
                Eq c5
                    (instHAdd.hAdd n.cast
                      (instHDiv.hDiv
                        (instHMul.hMul (instHAdd.hAdd (HighamBench.p08Lemma43c3 run) (HighamBench.p08Lemma43c4 run))
                          (instHPow.hPow run.u 2))
                        (HighamBench.p08ResidualUnitRoundoff run.precision run.u))) →
                  Eq
                      (HighamBench.p08MatMul
                        (HighamBench.p08MatSub (HighamBench.p08IdMatrix n)
                          (HighamBench.p08MatScale run.u
                            (HighamBench.p08MatMul run.C1
                              (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                (HighamBench.p08AbsMatrix run.Ainv)))))
                        C2ResolventInv)
                      (HighamBench.p08IdMatrix n) →
                    Eq
                        (HighamBench.p08MatMul C2ResolventInv
                          (HighamBench.p08MatSub (HighamBench.p08IdMatrix n)
                            (HighamBench.p08MatScale run.u
                              (HighamBench.p08MatMul run.C1
                                (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                  (HighamBench.p08AbsMatrix run.Ainv))))))
                        (HighamBench.p08IdMatrix n) →
                      Eq C2 (HighamBench.p08MatMul C2ResolventInv run.C1) →
                        Eq C6
                            (HighamBench.p08MatAdd C2
                              (HighamBench.p08MatScale
                                (instHAdd.hAdd 1
                                  (instHDiv.hDiv
                                    (instHMul.hMul c5 (HighamBench.p08ResidualUnitRoundoff run.precision run.u)) run.u))
                                (HighamBench.p08MatAdd (HighamBench.p08IdMatrix n)
                                  (HighamBench.p08MatScale run.u
                                    (HighamBench.p08MatMul C2
                                      (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                        (HighamBench.p08AbsMatrix run.Ainv))))))) →
                          Eq C7
                              (HighamBench.p08MatScale
                                (instHAdd.hAdd n.cast
                                  (instHDiv.hDiv (instHMul.hMul (HighamBench.p08Lemma43c3 run) (instHPow.hPow run.u 2))
                                    (HighamBench.p08ResidualUnitRoundoff run.precision run.u)))
                                C2) →
                            Eq C8 (HighamBench.p08MatScale (instHAdd.hAdd 1 run.u) C6) →
                              Eq c8 (norm.matrixNorm C8) →
                                Eq C9
                                    (HighamBench.p08MatAdd C6
                                      (HighamBench.p08MatScale (HighamBench.p08Lemma43c3 run)
                                        (HighamBench.p08IdMatrix n))) →
                                  Eq C10
                                      (HighamBench.p08MatAdd
                                        (HighamBench.p08MatAdd C6
                                          (HighamBench.p08MatScale
                                            (instHAdd.hAdd
                                              (instHDiv.hDiv
                                                (instHMul.hMul n.cast
                                                  (HighamBench.p08ResidualUnitRoundoff run.precision run.u))
                                                run.u)
                                              (instHMul.hMul (HighamBench.p08Lemma43c3 run) run.u))
                                            (HighamBench.p08IdMatrix n)))
                                        (HighamBench.p08MatScale
                                          (HighamBench.p08ResidualUnitRoundoff run.precision run.u)
                                          (HighamBench.p08MatMul C7
                                            (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                              (HighamBench.p08AbsMatrix run.Ainv))))) →
                                    Eq
                                        (HighamBench.p08MatMul
                                          (HighamBench.p08MatSub (HighamBench.p08IdMatrix n)
                                            (HighamBench.p08MatScale run.u
                                              (HighamBench.p08MatMul C8
                                                (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                                  (HighamBench.p08AbsMatrix run.Ainv)))))
                                          C11ResolventInv)
                                        (HighamBench.p08IdMatrix n) →
                                      Eq
                                          (HighamBench.p08MatMul C11ResolventInv
                                            (HighamBench.p08MatSub (HighamBench.p08IdMatrix n)
                                              (HighamBench.p08MatScale run.u
                                                (HighamBench.p08MatMul C8
                                                  (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                                    (HighamBench.p08AbsMatrix run.Ainv))))))
                                          (HighamBench.p08IdMatrix n) →
                                        Eq C11 (HighamBench.p08MatMul C11ResolventInv C9) →
                                          Eq C12
                                              (HighamBench.p08MatMul C11ResolventInv
                                                (HighamBench.p08MatAdd (HighamBench.p08MatScale n.cast C8) C7)) →
                                            Eq C11
                                                (HighamBench.p08MatAdd C9
                                                  (HighamBench.p08MatMul
                                                    (HighamBench.p08MatScale run.u
                                                      (HighamBench.p08MatMul C8
                                                        (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                                          (HighamBench.p08AbsMatrix run.Ainv))))
                                                    C11)) →
                                              Eq C12
                                                  (HighamBench.p08MatAdd
                                                    (HighamBench.p08MatAdd (HighamBench.p08MatScale n.cast C8) C7)
                                                    (HighamBench.p08MatMul
                                                      (HighamBench.p08MatScale run.u
                                                        (HighamBench.p08MatMul C8
                                                          (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A)
                                                            (HighamBench.p08AbsMatrix run.Ainv))))
                                                      C12)) →
                                                HighamBench.p08MatNonnegative C2 →
                                                  HighamBench.p08MatNonnegative C6 →
                                                    HighamBench.p08MatNonnegative C7 →
                                                      HighamBench.p08MatNonnegative C8 →
                                                        HighamBench.p08MatNonnegative C9 →
                                                          HighamBench.p08MatNonnegative C10 →
                                                            HighamBench.p08MatNonnegative C11 →
                                                              HighamBench.p08MatNonnegative C12 →
                                                                Real.instLE.le 0 c1 →
                                                                  Real.instLE.le 0 c8 →
                                                                    Real.instLE.le c1 c8 →
                                                                      (∀ (i j : Fin n),
                                                                          Real.instLE.le (run.C1 i j)
                                                                            (dimensionBounds.matrixEntry n)) →
                                                                        (∀ (i j : Fin n),
                                                                            Real.instLE.le (C2 i j)
                                                                              (dimensionBounds.matrixEntry n)) →
                                                                          (∀ (i j : Fin n),
                                                                              Real.instLE.le (C6 i j)
                                                                                (dimensionBounds.matrixEntry n)) →
                                                                            (∀ (i j : Fin n),
                                                                                Real.instLE.le (C7 i j)
                                                                                  (dimensionBounds.matrixEntry n)) →
                                                                              (∀ (i j : Fin n),
                                                                                  Real.instLE.le (C8 i j)
                                                                                    (dimensionBounds.matrixEntry n)) →
                                                                                (∀ (i j : Fin n),
                                                                                    Real.instLE.le (C9 i j)
                                                                                      (dimensionBounds.matrixEntry n)) →
                                                                                  (∀ (i j : Fin n),
                                                                                      Real.instLE.le (C10 i j)
                                                                                        (dimensionBounds.matrixEntry
                                                                                          n)) →
                                                                                    (∀ (i j : Fin n),
                                                                                        Real.instLE.le (C11 i j)
                                                                                          (dimensionBounds.matrixEntry
                                                                                            n)) →
                                                                                      (∀ (i j : Fin n),
                                                                                          Real.instLE.le (C12 i j)
                                                                                            (dimensionBounds.matrixEntry
                                                                                              n)) →
                                                                                        Real.instLE.le c1
                                                                                            (dimensionBounds.scalar n) →
                                                                                          Real.instLE.le c5
                                                                                              (dimensionBounds.scalar
                                                                                                n) →
                                                                                            Real.instLE.le c8
                                                                                                (dimensionBounds.scalar
                                                                                                  n) →
                                                                                              HighamBench.P08Lemma43Constants
                                                                                                run norm dimensionBounds
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (C2 C6 C7 C8 C9 C10 C11 C12 : Fin n → Fin n → Real) →
          (c1 c5 c8 : Real) →
            (C2ResolventInv C11ResolventInv : Fin n → Fin n → Real) →
              (c1_definition :
                  @Eq.{1} Real c1
                    (@HighamBench.P08AbsoluteMonotoneNorm.matrixNorm n norm
                      (@HighamBench.P08IterativeRefinementRun.C1 n run))) →
                (c5_definition :
                    @Eq.{1} Real c5
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HighamBench.p08Lemma43c3 n run) (@HighamBench.p08Lemma43c4 n run))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                              (@HighamBench.P08IterativeRefinementRun.u n run)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (HighamBench.p08ResidualUnitRoundoff (@HighamBench.P08IterativeRefinementRun.precision n run)
                            (@HighamBench.P08IterativeRefinementRun.u n run))))) →
                  (C2_resolvent_left :
                      @Eq.{1} (Fin n → Fin n → Real)
                        (@HighamBench.p08MatMul n
                          (@HighamBench.p08MatSub n (HighamBench.p08IdMatrix n)
                            (@HighamBench.p08MatScale n (@HighamBench.P08IterativeRefinementRun.u n run)
                              (@HighamBench.p08MatMul n (@HighamBench.P08IterativeRefinementRun.C1 n run)
                                (@HighamBench.p08MatMul n
                                  (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                                  (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.Ainv n run))))))
                          C2ResolventInv)
                        (HighamBench.p08IdMatrix n)) →
                    (C2_resolvent_right :
                        @Eq.{1} (Fin n → Fin n → Real)
                          (@HighamBench.p08MatMul n C2ResolventInv
                            (@HighamBench.p08MatSub n (HighamBench.p08IdMatrix n)
                              (@HighamBench.p08MatScale n (@HighamBench.P08IterativeRefinementRun.u n run)
                                (@HighamBench.p08MatMul n (@HighamBench.P08IterativeRefinementRun.C1 n run)
                                  (@HighamBench.p08MatMul n
                                    (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                                    (@HighamBench.p08AbsMatrix n
                                      (@HighamBench.P08IterativeRefinementRun.Ainv n run)))))))
                          (HighamBench.p08IdMatrix n)) →
                      (C2_definition :
                          @Eq.{1} (Fin n → Fin n → Real) C2
                            (@HighamBench.p08MatMul n C2ResolventInv
                              (@HighamBench.P08IterativeRefinementRun.C1 n run))) →
                        (C6_definition :
                            @Eq.{1} (Fin n → Fin n → Real) C6
                              (@HighamBench.p08MatAdd n C2
                                (@HighamBench.p08MatScale n
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c5
                                        (HighamBench.p08ResidualUnitRoundoff
                                          (@HighamBench.P08IterativeRefinementRun.precision n run)
                                          (@HighamBench.P08IterativeRefinementRun.u n run)))
                                      (@HighamBench.P08IterativeRefinementRun.u n run)))
                                  (@HighamBench.p08MatAdd n (HighamBench.p08IdMatrix n)
                                    (@HighamBench.p08MatScale n (@HighamBench.P08IterativeRefinementRun.u n run)
                                      (@HighamBench.p08MatMul n C2
                                        (@HighamBench.p08MatMul n
                                          (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                                          (@HighamBench.p08AbsMatrix n
                                            (@HighamBench.P08IterativeRefinementRun.Ainv n run))))))))) →
                          (C7_definition :
                              @Eq.{1} (Fin n → Fin n → Real) C7
                                (@HighamBench.p08MatScale n
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@Nat.cast.{0} Real Real.instNatCast n)
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HighamBench.p08Lemma43c3 n run)
                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                          (@HighamBench.P08IterativeRefinementRun.u n run)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                      (HighamBench.p08ResidualUnitRoundoff
                                        (@HighamBench.P08IterativeRefinementRun.precision n run)
                                        (@HighamBench.P08IterativeRefinementRun.u n run))))
                                  C2)) →
                            (C8_definition :
                                @Eq.{1} (Fin n → Fin n → Real) C8
                                  (@HighamBench.p08MatScale n
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                      (@HighamBench.P08IterativeRefinementRun.u n run))
                                    C6)) →
                              (c8_definition :
                                  @Eq.{1} Real c8 (@HighamBench.P08AbsoluteMonotoneNorm.matrixNorm n norm C8)) →
                                (C9_definition :
                                    @Eq.{1} (Fin n → Fin n → Real) C9
                                      (@HighamBench.p08MatAdd n C6
                                        (@HighamBench.p08MatScale n (@HighamBench.p08Lemma43c3 n run)
                                          (HighamBench.p08IdMatrix n)))) →
                                  (C10_definition :
                                      @Eq.{1} (Fin n → Fin n → Real) C10
                                        (@HighamBench.p08MatAdd n
                                          (@HighamBench.p08MatAdd n C6
                                            (@HighamBench.p08MatScale n
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@Nat.cast.{0} Real Real.instNatCast n)
                                                    (HighamBench.p08ResidualUnitRoundoff
                                                      (@HighamBench.P08IterativeRefinementRun.precision n run)
                                                      (@HighamBench.P08IterativeRefinementRun.u n run)))
                                                  (@HighamBench.P08IterativeRefinementRun.u n run))
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HighamBench.p08Lemma43c3 n run)
                                                  (@HighamBench.P08IterativeRefinementRun.u n run)))
                                              (HighamBench.p08IdMatrix n)))
                                          (@HighamBench.p08MatScale n
                                            (HighamBench.p08ResidualUnitRoundoff
                                              (@HighamBench.P08IterativeRefinementRun.precision n run)
                                              (@HighamBench.P08IterativeRefinementRun.u n run))
                                            (@HighamBench.p08MatMul n C7
                                              (@HighamBench.p08MatMul n
                                                (@HighamBench.p08AbsMatrix n
                                                  (@HighamBench.P08IterativeRefinementRun.A n run))
                                                (@HighamBench.p08AbsMatrix n
                                                  (@HighamBench.P08IterativeRefinementRun.Ainv n run))))))) →
                                    (C11_resolvent_left :
                                        @Eq.{1} (Fin n → Fin n → Real)
                                          (@HighamBench.p08MatMul n
                                            (@HighamBench.p08MatSub n (HighamBench.p08IdMatrix n)
                                              (@HighamBench.p08MatScale n
                                                (@HighamBench.P08IterativeRefinementRun.u n run)
                                                (@HighamBench.p08MatMul n C8
                                                  (@HighamBench.p08MatMul n
                                                    (@HighamBench.p08AbsMatrix n
                                                      (@HighamBench.P08IterativeRefinementRun.A n run))
                                                    (@HighamBench.p08AbsMatrix n
                                                      (@HighamBench.P08IterativeRefinementRun.Ainv n run))))))
                                            C11ResolventInv)
                                          (HighamBench.p08IdMatrix n)) →
                                      (C11_resolvent_right :
                                          @Eq.{1} (Fin n → Fin n → Real)
                                            (@HighamBench.p08MatMul n C11ResolventInv
                                              (@HighamBench.p08MatSub n (HighamBench.p08IdMatrix n)
                                                (@HighamBench.p08MatScale n
                                                  (@HighamBench.P08IterativeRefinementRun.u n run)
                                                  (@HighamBench.p08MatMul n C8
                                                    (@HighamBench.p08MatMul n
                                                      (@HighamBench.p08AbsMatrix n
                                                        (@HighamBench.P08IterativeRefinementRun.A n run))
                                                      (@HighamBench.p08AbsMatrix n
                                                        (@HighamBench.P08IterativeRefinementRun.Ainv n run)))))))
                                            (HighamBench.p08IdMatrix n)) →
                                        (C11_definition :
                                            @Eq.{1} (Fin n → Fin n → Real) C11
                                              (@HighamBench.p08MatMul n C11ResolventInv C9)) →
                                          (C12_definition :
                                              @Eq.{1} (Fin n → Fin n → Real) C12
                                                (@HighamBench.p08MatMul n C11ResolventInv
                                                  (@HighamBench.p08MatAdd n
                                                    (@HighamBench.p08MatScale n (@Nat.cast.{0} Real Real.instNatCast n)
                                                      C8)
                                                    C7))) →
                                            (C11_fixed_point :
                                                @Eq.{1} (Fin n → Fin n → Real) C11
                                                  (@HighamBench.p08MatAdd n C9
                                                    (@HighamBench.p08MatMul n
                                                      (@HighamBench.p08MatScale n
                                                        (@HighamBench.P08IterativeRefinementRun.u n run)
                                                        (@HighamBench.p08MatMul n C8
                                                          (@HighamBench.p08MatMul n
                                                            (@HighamBench.p08AbsMatrix n
                                                              (@HighamBench.P08IterativeRefinementRun.A n run))
                                                            (@HighamBench.p08AbsMatrix n
                                                              (@HighamBench.P08IterativeRefinementRun.Ainv n run)))))
                                                      C11))) →
                                              (C12_fixed_point :
                                                  @Eq.{1} (Fin n → Fin n → Real) C12
                                                    (@HighamBench.p08MatAdd n
                                                      (@HighamBench.p08MatAdd n
                                                        (@HighamBench.p08MatScale n
                                                          (@Nat.cast.{0} Real Real.instNatCast n) C8)
                                                        C7)
                                                      (@HighamBench.p08MatMul n
                                                        (@HighamBench.p08MatScale n
                                                          (@HighamBench.P08IterativeRefinementRun.u n run)
                                                          (@HighamBench.p08MatMul n C8
                                                            (@HighamBench.p08MatMul n
                                                              (@HighamBench.p08AbsMatrix n
                                                                (@HighamBench.P08IterativeRefinementRun.A n run))
                                                              (@HighamBench.p08AbsMatrix n
                                                                (@HighamBench.P08IterativeRefinementRun.Ainv n run)))))
                                                        C12))) →
                                                (C2_nonnegative : @HighamBench.p08MatNonnegative n C2) →
                                                  (C6_nonnegative : @HighamBench.p08MatNonnegative n C6) →
                                                    (C7_nonnegative : @HighamBench.p08MatNonnegative n C7) →
                                                      (C8_nonnegative : @HighamBench.p08MatNonnegative n C8) →
                                                        (C9_nonnegative : @HighamBench.p08MatNonnegative n C9) →
                                                          (C10_nonnegative : @HighamBench.p08MatNonnegative n C10) →
                                                            (C11_nonnegative : @HighamBench.p08MatNonnegative n C11) →
                                                              (C12_nonnegative : @HighamBench.p08MatNonnegative n C12) →
                                                                (c1_nonnegative :
                                                                    @LE.le.{0} Real Real.instLE
                                                                      (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                        (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                      c1) →
                                                                  (c8_nonnegative :
                                                                      @LE.le.{0} Real Real.instLE
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                          (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                        c8) →
                                                                    (c1_le_c8 : @LE.le.{0} Real Real.instLE c1 c8) →
                                                                      (C1_dimension_bound :
                                                                          ∀ (i j : Fin n),
                                                                            @LE.le.{0} Real Real.instLE
                                                                              (@HighamBench.P08IterativeRefinementRun.C1
                                                                                n run i j)
                                                                              (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                dimensionBounds n)) →
                                                                        (C2_dimension_bound :
                                                                            ∀ (i j : Fin n),
                                                                              @LE.le.{0} Real Real.instLE (C2 i j)
                                                                                (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                  dimensionBounds n)) →
                                                                          (C6_dimension_bound :
                                                                              ∀ (i j : Fin n),
                                                                                @LE.le.{0} Real Real.instLE (C6 i j)
                                                                                  (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                    dimensionBounds n)) →
                                                                            (C7_dimension_bound :
                                                                                ∀ (i j : Fin n),
                                                                                  @LE.le.{0} Real Real.instLE (C7 i j)
                                                                                    (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                      dimensionBounds n)) →
                                                                              (C8_dimension_bound :
                                                                                  ∀ (i j : Fin n),
                                                                                    @LE.le.{0} Real Real.instLE (C8 i j)
                                                                                      (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                        dimensionBounds n)) →
                                                                                (C9_dimension_bound :
                                                                                    ∀ (i j : Fin n),
                                                                                      @LE.le.{0} Real Real.instLE
                                                                                        (C9 i j)
                                                                                        (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                          dimensionBounds n)) →
                                                                                  (C10_dimension_bound :
                                                                                      ∀ (i j : Fin n),
                                                                                        @LE.le.{0} Real Real.instLE
                                                                                          (C10 i j)
                                                                                          (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                            dimensionBounds n)) →
                                                                                    (C11_dimension_bound :
                                                                                        ∀ (i j : Fin n),
                                                                                          @LE.le.{0} Real Real.instLE
                                                                                            (C11 i j)
                                                                                            (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                              dimensionBounds n)) →
                                                                                      (C12_dimension_bound :
                                                                                          ∀ (i j : Fin n),
                                                                                            @LE.le.{0} Real Real.instLE
                                                                                              (C12 i j)
                                                                                              (HighamBench.P08DimensionOnlyConstantBounds.matrixEntry
                                                                                                dimensionBounds n)) →
                                                                                        (c1_dimension_bound :
                                                                                            @LE.le.{0} Real Real.instLE
                                                                                              c1
                                                                                              (HighamBench.P08DimensionOnlyConstantBounds.scalar
                                                                                                dimensionBounds n)) →
                                                                                          (c5_dimension_bound :
                                                                                              @LE.le.{0} Real
                                                                                                Real.instLE c5
                                                                                                (HighamBench.P08DimensionOnlyConstantBounds.scalar
                                                                                                  dimensionBounds n)) →
                                                                                            (c8_dimension_bound :
                                                                                                @LE.le.{0} Real
                                                                                                  Real.instLE c8
                                                                                                  (HighamBench.P08DimensionOnlyConstantBounds.scalar
                                                                                                    dimensionBounds
                                                                                                    n)) →
                                                                                              @HighamBench.P08Lemma43Constants
                                                                                                n run norm
                                                                                                dimensionBounds
```

### D021: `HighamBench.P08Lemma43RoundoffAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `73683a4284a37367b266f180956ce9f42c778286096583e945d99010a104289f`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        {constants : HighamBench.P08Lemma43Constants run norm dimensionBounds} →
          (residualError : Nat → Fin n → Real) →
            (∀ (m : Nat),
                Eq (run.computedResidual m)
                  (HighamBench.p08VecAdd (HighamBench.p08VecSub (HighamBench.p08MatVec run.A (run.iterate m)) run.b)
                    (residualError m))) →
              (∀ (m : Nat) (i : Fin n),
                  Real.instLE.le (abs (residualError m i))
                    (instHAdd.hAdd
                      (instHAdd.hAdd
                        (instHMul.hMul
                          (instHAdd.hAdd
                            (instHMul.hMul n.cast (HighamBench.p08ResidualUnitRoundoff run.precision run.u))
                            (instHMul.hMul (HighamBench.p08Lemma43c3 run) (instHPow.hPow run.u 2)))
                          (HighamBench.p08MatVec (HighamBench.p08AbsMatrix run.A)
                            (HighamBench.p08AbsVec run.exactSolution) i))
                        (instHMul.hMul
                          (instHMul.hMul constants.c5 (HighamBench.p08ResidualUnitRoundoff run.precision run.u))
                          (HighamBench.p08MatVec (HighamBench.p08AbsMatrix run.A)
                            (HighamBench.p08AbsVec (HighamBench.p08VecSub (run.iterate m) run.exactSolution)) i)))
                      (instHMul.hMul run.u
                        (abs
                          (HighamBench.p08MatVec run.A (HighamBench.p08VecSub (run.iterate m) run.exactSolution)
                            i))))) →
                (correctionError : Nat → Fin n → Real) →
                  (∀ (m : Nat),
                      Eq (HighamBench.p08MatVec run.A (run.correction m))
                        (HighamBench.p08VecAdd (run.computedResidual m) (correctionError m))) →
                    (Real.instLE.le
                          (instHMul.hMul (instHMul.hMul constants.c1 run.u) (HighamBench.p08KappaInverse run norm))
                          (1 / 2) →
                        ∀ (m : Nat) (i : Fin n),
                          Real.instLE.le (abs (correctionError m i))
                            (instHAdd.hAdd
                              (instHMul.hMul run.u
                                (HighamBench.p08MatVec
                                  (HighamBench.p08MatMul constants.C2 (HighamBench.p08AbsMatrix run.A))
                                  (HighamBench.p08AbsVec (HighamBench.p08VecSub (run.iterate m) run.exactSolution)) i))
                              (instHMul.hMul run.u
                                (HighamBench.p08MatVec
                                  (HighamBench.p08MatMul
                                    (HighamBench.p08MatMul constants.C2 (HighamBench.p08AbsMatrix run.A))
                                    (HighamBench.p08AbsMatrix run.Ainv))
                                  (HighamBench.p08AbsVec (residualError m)) i)))) →
                      HighamBench.P08Lemma43RoundoffAnalysis run norm dimensionBounds constants
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        {constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds} →
          (residualError : Nat → Fin n → Real) →
            (residual_equation :
                ∀ (m : Nat),
                  @Eq.{1} (Fin n → Real) (@HighamBench.P08IterativeRefinementRun.computedResidual n run m)
                    (@HighamBench.p08VecAdd n
                      (@HighamBench.p08VecSub n
                        (@HighamBench.p08MatVec n (@HighamBench.P08IterativeRefinementRun.A n run)
                          (@HighamBench.P08IterativeRefinementRun.iterate n run m))
                        (@HighamBench.P08IterativeRefinementRun.b n run))
                      (residualError m))) →
              (residual_error_bound :
                  ∀ (m : Nat) (i : Fin n),
                    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (residualError m i))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@Nat.cast.{0} Real Real.instNatCast n)
                                (HighamBench.p08ResidualUnitRoundoff
                                  (@HighamBench.P08IterativeRefinementRun.precision n run)
                                  (@HighamBench.P08IterativeRefinementRun.u n run)))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HighamBench.p08Lemma43c3 n run)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                  (@HighamBench.P08IterativeRefinementRun.u n run)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                            (@HighamBench.p08MatVec n
                              (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                              (@HighamBench.p08AbsVec n (@HighamBench.P08IterativeRefinementRun.exactSolution n run))
                              i))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HighamBench.P08Lemma43Constants.c5 n run norm dimensionBounds constants)
                              (HighamBench.p08ResidualUnitRoundoff
                                (@HighamBench.P08IterativeRefinementRun.precision n run)
                                (@HighamBench.P08IterativeRefinementRun.u n run)))
                            (@HighamBench.p08MatVec n
                              (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                              (@HighamBench.p08AbsVec n
                                (@HighamBench.p08VecSub n (@HighamBench.P08IterativeRefinementRun.iterate n run m)
                                  (@HighamBench.P08IterativeRefinementRun.exactSolution n run)))
                              i)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HighamBench.P08IterativeRefinementRun.u n run)
                          (@abs.{0} Real Real.lattice Real.instAddGroup
                            (@HighamBench.p08MatVec n (@HighamBench.P08IterativeRefinementRun.A n run)
                              (@HighamBench.p08VecSub n (@HighamBench.P08IterativeRefinementRun.iterate n run m)
                                (@HighamBench.P08IterativeRefinementRun.exactSolution n run))
                              i))))) →
                (correctionError : Nat → Fin n → Real) →
                  (correction_equation :
                      ∀ (m : Nat),
                        @Eq.{1} (Fin n → Real)
                          (@HighamBench.p08MatVec n (@HighamBench.P08IterativeRefinementRun.A n run)
                            (@HighamBench.P08IterativeRefinementRun.correction n run m))
                          (@HighamBench.p08VecAdd n (@HighamBench.P08IterativeRefinementRun.computedResidual n run m)
                            (correctionError m))) →
                    (correction_error_bound :
                        @LE.le.{0} Real Real.instLE
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HighamBench.P08Lemma43Constants.c1 n run norm dimensionBounds constants)
                                (@HighamBench.P08IterativeRefinementRun.u n run))
                              (@HighamBench.p08KappaInverse n run norm))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
                          ∀ (m : Nat) (i : Fin n),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup (correctionError m i))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HighamBench.P08IterativeRefinementRun.u n run)
                                  (@HighamBench.p08MatVec n
                                    (@HighamBench.p08MatMul n
                                      (@HighamBench.P08Lemma43Constants.C2 n run norm dimensionBounds constants)
                                      (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run)))
                                    (@HighamBench.p08AbsVec n
                                      (@HighamBench.p08VecSub n (@HighamBench.P08IterativeRefinementRun.iterate n run m)
                                        (@HighamBench.P08IterativeRefinementRun.exactSolution n run)))
                                    i))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HighamBench.P08IterativeRefinementRun.u n run)
                                  (@HighamBench.p08MatVec n
                                    (@HighamBench.p08MatMul n
                                      (@HighamBench.p08MatMul n
                                        (@HighamBench.P08Lemma43Constants.C2 n run norm dimensionBounds constants)
                                        (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run)))
                                      (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.Ainv n run)))
                                    (@HighamBench.p08AbsVec n (residualError m)) i)))) →
                      @HighamBench.P08Lemma43RoundoffAnalysis n run norm dimensionBounds constants
```

### D022: `HighamBench.p08AbsMatrix`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e805548fdc53f300f35b23b599d9e0cce148e3d8c77b379efa381e734712ca5e`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A i j => abs (A i j)
```

### D023: `HighamBench.p08Lemma43InitialVector`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6f51903a6cd95edb972bc40fd17d2fcf52fd559ea050fae065f3832c41a69c78`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} {dimensionBounds} constants =>
  HighamBench.p08VecScale run.u
    (HighamBench.p08MatVec (HighamBench.p08MatMul constants.C10 (HighamBench.p08AbsMatrix run.A))
      (HighamBench.p08AbsVec run.exactSolution))
```

### D024: `HighamBench.p08Lemma43Propagation`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fc8538d8bc9f07d48d50e64d015175e1119275cd83e232fb005dcd46ace4b037`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} {dimensionBounds} constants =>
  HighamBench.p08MatScale run.u
    (HighamBench.p08MatMul constants.C8
      (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A) (HighamBench.p08AbsMatrix run.Ainv)))
```

### D025: `HighamBench.p08Lemma43StationaryVector`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1b5c03a53e3e7fcebe6bb0e4a313ad7a6b359634ffdb49d664ddd58f39f707c9`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (constants : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} {dimensionBounds} constants =>
  have absA := HighamBench.p08AbsMatrix run.A;
  have absAinv := HighamBench.p08AbsMatrix run.Ainv;
  have absx := HighamBench.p08AbsVec run.exactSolution;
  have ubar := HighamBench.p08ResidualUnitRoundoff run.precision run.u;
  HighamBench.p08VecAdd (HighamBench.p08VecScale (instHMul.hMul n.cast ubar) (HighamBench.p08MatVec absA absx))
    (HighamBench.p08VecAdd
      (HighamBench.p08VecScale (instHPow.hPow run.u 2)
        (HighamBench.p08MatVec (HighamBench.p08MatMul constants.C11 absA) absx))
      (HighamBench.p08VecScale (instHMul.hMul ubar run.u)
        (HighamBench.p08MatVec
          (HighamBench.p08MatMul (HighamBench.p08MatMul constants.C12 (HighamBench.p08MatMul absA absAinv)) absA)
          absx)))
```

### D026: `HighamBench.p08MatMul`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d0da17f42708be972b7710bd91ed5479fc07923ec7ea0e2767ff54131b2c3ec0`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D027: `HighamBench.p08MatPow`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `489fa9aeca464a7c43c76f1d8f771ecb486c6f1109d220d5f27db122c28f21b7`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Nat → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (B : Fin n → Fin n → Real) → Nat → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} B x =>
  Nat.brecOn (motive := fun x => Fin n → Fin n → Real) x fun x f =>
    HighamBench.p08MatPow.match_1
      (fun x => Nat.below (motive := fun x => Fin n → Fin n → Real) x → Fin n → Fin n → Real) x
      (fun _ x => HighamBench.p08IdMatrix n) (fun k x => HighamBench.p08MatMul B x.1) f
```

### D028: `HighamBench.p08MatVec`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a592839d471927bb3cc257d8a1d685487e1a3d3378b7ad9ee731c33e3c99b742`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D029: `HighamBench.p08VecAdd`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `48044aa432a436b28ce14db73d143a7f56206968c45cb1e2a875ac972c0c05c8`

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

### D030: `HighamBench.p08VecSub`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `441efa53ccbc8055dbb223ccd54794324a03325218e39203ecb218d295342c86`

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
fun {n} x y i => instHSub.hSub (x i) (y i)
```

### D031: `HighamBench.P08ColumnPivotedSolveCertificate`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `b694445b6edb36738cb9972cfec4a23fb96652d48e65d25a3e8d15c761a1e258`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → (Fin n → Fin n → Real) → Real → Type
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (rhs : Fin n → Real) → (C1 : Fin n → Fin n → Real) → (u : Real) → Type
```

### D032: `HighamBench.P08ColumnPivotedSolveCertificate.output`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `26474c9523e744eabd7c64a71be338ecf1547a53130c1a6c3f05a19f89763bce`

Type:

```lean
{n : Nat} →
  {A : Fin n → Fin n → Real} →
    {rhs : Fin n → Real} →
      {C1 : Fin n → Fin n → Real} → {u : Real} → HighamBench.P08ColumnPivotedSolveCertificate A rhs C1 u → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {A : Fin n → Fin n → Real} →
    {rhs : Fin n → Real} →
      {C1 : Fin n → Fin n → Real} →
        {u : Real} → (self : @HighamBench.P08ColumnPivotedSolveCertificate n A rhs C1 u) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n A rhs C1 u self => self.1
```

### D033: `HighamBench.P08DimensionOnlyConstantBounds.matrixEntry`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7807c5b0443354e41892839092dfb1798c40704ab6a59916d3426e87f4a0dc34`

Type:

```lean
HighamBench.P08DimensionOnlyConstantBounds → Nat → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08DimensionOnlyConstantBounds) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D034: `HighamBench.P08DimensionOnlyConstantBounds.scalar`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d6088e0225cfe0110055e45e4e97c0da46a8f6f891a1d079662801ffc7f89006`

Type:

```lean
HighamBench.P08DimensionOnlyConstantBounds → Nat → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08DimensionOnlyConstantBounds) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D035: `HighamBench.P08IterativeRefinementRun.C1`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `768997f4ed7501b5e1d8b1583cb98d0fc1e01408d7e0649458fbf868ce594534`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.13
```

### D036: `HighamBench.P08IterativeRefinementRun.computedResidual`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c05758c4ef94973c8c25605a9956d10811edc355ed0d4b4d7749f098ab14fa17`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Nat → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.17
```

### D037: `HighamBench.P08IterativeRefinementRun.exactSolution`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `81375c3265f25d00cfa101f64f9f9d50cdc1354772ba920dcc0a5c26a647df4b`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.11
```

### D038: `HighamBench.P08IterativeRefinementRun.precision`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0545949cc8af01a726c7a3c120fdc1d5a19e5cfd531d7d911c451b33f08dc85a`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → HighamBench.P08ResidualPrecision
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → HighamBench.P08ResidualPrecision
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D039: `HighamBench.P08Lemma43Constants.C10`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9ae892a2919f5ef5d7fe83095ff14f0a21e44885747984d04716d888e20ef5d5`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.6
```

### D040: `HighamBench.P08Lemma43Constants.C11`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cb40f032154afa002ddf244eb17b91237ab04da771de5b8c16d652cb11007012`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.7
```

### D041: `HighamBench.P08Lemma43Constants.C12`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3bc8aadae3baed9f5b7f93e37032d0ba4fa9392b68373b08bf9b9cec3e567831`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.8
```

### D042: `HighamBench.P08Lemma43Constants.C2`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e11b1c218c5e0cea9b24a56d21cbee0568cfb7345d668eab797fb33f0c0baba0`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.1
```

### D043: `HighamBench.P08Lemma43Constants.C8`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `94053baacd4d4d794b4cee0ddcaf96dbe87eb45844dc2cdb37a0fd8d0cf0d7b8`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.4
```

### D044: `HighamBench.P08Lemma43Constants.c1`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e92ead70a36524d08e7dd1894512923400272f9edd8e09a1b7602a0b7c90daf8`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.9
```

### D045: `HighamBench.P08Lemma43Constants.c5`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6e796277136197ddf99f6c60f55184168c4471f64b47901dc73a08b828484c15`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        HighamBench.P08Lemma43Constants run norm dimensionBounds → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      {dimensionBounds : HighamBench.P08DimensionOnlyConstantBounds} →
        (self : @HighamBench.P08Lemma43Constants n run norm dimensionBounds) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm dimensionBounds self => self.10
```

### D046: `HighamBench.P08ResidualPrecision`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `d7549ecbed39af141999846c1c07ed08e8f2c8780d0dfe8c5b2006e7fc1faea4`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D047: `HighamBench.p08AbsVec`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `251d18073f7d0601a1d26c052e923b84818bac3d391608244c9b58516ce6c9f2`

Type:

```lean
{n : Nat} → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x i => abs (x i)
```

### D048: `HighamBench.p08BasisVector`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `943e670d3ba4601b3fd4545be0b69f3b002661c43ddc5c52382f72aab70e4a78`

Type:

```lean
{n : Nat} → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (j : Fin n) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} j i => ite (Eq i j) 1 0
```

### D049: `HighamBench.p08IdMatrix`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5e6389de03e053212362456681133b045c00c04678538b53fc2e2c60f503e204`

Type:

```lean
(n : Nat) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
(n : Nat) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n i j => ite (Eq i j) 1 0
```

### D050: `HighamBench.p08Lemma43c3`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1b7b6fc388731fbbe5e5edf509e81718c2ece61301cd270a32ea630188cf2f8d`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P08IterativeRefinementRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  HighamBench.p08ResidualUnitRoundoff.match_1 (fun x => Real) run.precision
    (fun _ =>
      instHSub.hSub
        (instHDiv.hDiv
          (instHMul.hMul (instHAdd.hAdd 1 run.u) (instHSub.hSub (instHPow.hPow (instHAdd.hAdd 1 run.u) n) 1))
          (instHPow.hPow run.u 2))
        (instHDiv.hDiv n.cast run.u))
    fun _ =>
    instHSub.hSub
      (instHDiv.hDiv
        (instHMul.hMul (instHMul.hMul (instHAdd.hAdd 1 run.u) (instHAdd.hAdd 1 (instHPow.hPow run.u 2)))
          (instHSub.hSub (instHPow.hPow (instHAdd.hAdd 1 (instHPow.hPow run.u 2)) n) 1))
        (instHPow.hPow run.u 2))
      n.cast
```

### D051: `HighamBench.p08Lemma43c4`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `672fe46b40849d9eecb89e024cded83bba77838b4bf46f06b9ae1d6a7c0afa72`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P08IterativeRefinementRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  HighamBench.p08ResidualUnitRoundoff.match_1 (fun x => Real) run.precision (fun _ => 0) fun _ => instHAdd.hAdd 1 run.u
```

### D052: `HighamBench.p08MatAdd`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2609ed33694abd0b60e21ae93a7ddeb0a0f5d699c42a86f70667bc3993bf0295`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => instHAdd.hAdd (A i j) (B i j)
```

### D053: `HighamBench.p08MatNonnegative`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `64127facdf54b3e4aee2946afe35ed21a0566b4759a2439fec1c8ac316f56cd3`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => ∀ (i j : Fin n), Real.instLE.le 0 (A i j)
```

### D054: `HighamBench.p08MatPow.match_1`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0d4b2b6183d9d2349786d34e92b9461732ad4ea08fe3e26ebfab22261a830af1`

Type:

```lean
(motive : Nat → Sort u_1) → (x : Nat) → (Unit → motive 0) → ((k : Nat) → motive k.succ) → motive x
```

Fully explicit type:

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (a : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (k : Nat) → motive (Nat.succ k)) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 Unit.unit) fun n => h_2 n
```

### D055: `HighamBench.p08MatScale`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `699272c225366e6c2d1ef283454245411d0c3bad0dba6a9659dfb3c225479071`

Type:

```lean
{n : Nat} → Real → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (a : Real) → (A : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a A i j => instHMul.hMul a (A i j)
```

### D056: `HighamBench.p08MatSub`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `499546f906ee1c73a8bc14fd14b5362b8af21b67ad4c407dc75360ad3b3ecb8d`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => instHSub.hSub (A i j) (B i j)
```

### D057: `HighamBench.p08ResidualUnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ba0c3c6a8980bf14670536e3c01d93fe3e449716ef3c0122d4f2136d3f8aa1fd`

Type:

```lean
HighamBench.P08ResidualPrecision → Real → Real
```

Fully explicit type:

```lean
(precision : HighamBench.P08ResidualPrecision) → (u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision u =>
  HighamBench.p08ResidualUnitRoundoff.match_1 (fun precision => Real) precision (fun _ => u) fun _ => instHPow.hPow u 2
```

### D058: `HighamBench.p08VecScale`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `fb1211b6e3f0aa8c81abbea4ef17958ce920ab3ada9211d91ffb6eab3118d704`

Type:

```lean
{n : Nat} → Real → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (a : Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a x i => instHMul.hMul a (x i)
```

### D059: `HighamBench.P08ColumnPivotedSolveCertificate.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `32cb8ef3635ca87399bad3910b77b3802f3d739e78e4457e871a6069935efa42`

Type:

```lean
{n : Nat} →
  {A : Fin n → Fin n → Real} →
    {rhs : Fin n → Real} →
      {C1 : Fin n → Fin n → Real} →
        {u : Real} →
          (output backwardError : Fin n → Real) →
            Eq (HighamBench.p08MatVec A output) (HighamBench.p08VecAdd rhs backwardError) →
              (∀ (i : Fin n),
                  Real.instLE.le (abs (backwardError i))
                    (instHMul.hMul u (HighamBench.p08MatVec C1 (HighamBench.p08AbsAction A output) i))) →
                HighamBench.P08ColumnPivotedSolveCertificate A rhs C1 u
```

Fully explicit type:

```lean
{n : Nat} →
  {A : Fin n → Fin n → Real} →
    {rhs : Fin n → Real} →
      {C1 : Fin n → Fin n → Real} →
        {u : Real} →
          (output backwardError : Fin n → Real) →
            (equation :
                @Eq.{1} (Fin n → Real) (@HighamBench.p08MatVec n A output)
                  (@HighamBench.p08VecAdd n rhs backwardError)) →
              (backward_error_bound :
                  ∀ (i : Fin n),
                    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (backwardError i))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
                        (@HighamBench.p08MatVec n C1 (@HighamBench.p08AbsAction n A output) i))) →
                @HighamBench.P08ColumnPivotedSolveCertificate n A rhs C1 u
```

### D060: `HighamBench.P08ResidualPrecision.double`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `338a37198896bd23dd4b9df74ea75f587c793386b8fcd6edd3cdaf1722fa8ded`

Type:

```lean
HighamBench.P08ResidualPrecision
```

Fully explicit type:

```lean
HighamBench.P08ResidualPrecision
```

### D061: `HighamBench.P08ResidualPrecision.single`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `295399acf2b054574bf28389bfa961fb4a8c6d0ddca4892fb93bf4d33d6cc840`

Type:

```lean
HighamBench.P08ResidualPrecision
```

Fully explicit type:

```lean
HighamBench.P08ResidualPrecision
```

### D062: `HighamBench.p08ResidualUnitRoundoff.match_1`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `49e9dd09a1edbfc9990270754d1cd4f0aa0fce2302a26e1874b995b1f0c07d72`

Type:

```lean
(motive : HighamBench.P08ResidualPrecision → Sort u_1) →
  (precision : HighamBench.P08ResidualPrecision) →
    (Unit → motive HighamBench.P08ResidualPrecision.single) →
      (Unit → motive HighamBench.P08ResidualPrecision.double) → motive precision
```

Fully explicit type:

```lean
(motive : HighamBench.P08ResidualPrecision → Sort u_1) →
  (precision : HighamBench.P08ResidualPrecision) →
    (h_1 : (a : Unit) → motive HighamBench.P08ResidualPrecision.single) →
      (h_2 : (a : Unit) → motive HighamBench.P08ResidualPrecision.double) → motive precision
```

Definition body (one-level semantic boundary):

```lean
fun motive precision h_1 h_2 => HighamBench.P08ResidualPrecision.casesOn precision (h_1 Unit.unit) (h_2 Unit.unit)
```

### D063: `HighamBench.P08ResidualPrecision.casesOn`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `ef6bb9641dd3962a514e35510b1298ed2e76b6beb424f5eb5b4f9e369ab97fd2`

Type:

```lean
{motive : HighamBench.P08ResidualPrecision → Sort u} →
  (t : HighamBench.P08ResidualPrecision) →
    motive HighamBench.P08ResidualPrecision.single → motive HighamBench.P08ResidualPrecision.double → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P08ResidualPrecision) → Sort u} →
  (t : HighamBench.P08ResidualPrecision) →
    (single : motive HighamBench.P08ResidualPrecision.single) →
      (double : motive HighamBench.P08ResidualPrecision.double) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t single double => HighamBench.P08ResidualPrecision.rec single double t
```

### D064: `HighamBench.p08AbsAction`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `2e411afdeeff87e69866a73e67fc559f4099fa28d728bac01a806d5050ad1e33`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (abs (A i j)) (abs (x j))
```

### D065: `HighamBench.P08ResidualPrecision.rec`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `recursor`
- Distance from target type: `6`
- Semantic SHA-256: `ea639447496f6c9e2a35485c6927422f54b5c8c94811e8c659e89ac626e80beb`

Type:

```lean
{motive : HighamBench.P08ResidualPrecision → Sort u} →
  motive HighamBench.P08ResidualPrecision.single →
    motive HighamBench.P08ResidualPrecision.double → (t : HighamBench.P08ResidualPrecision) → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P08ResidualPrecision) → Sort u} →
  (single : motive HighamBench.P08ResidualPrecision.single) →
    (double : motive HighamBench.P08ResidualPrecision.double) → (t : HighamBench.P08ResidualPrecision) → motive t
```

### D066: `DivInvMonoid.toDiv`

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

### D067: `Fin`

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

### D068: `HDiv.hDiv`

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

### D069: `HMul.hMul`

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

### D070: `LE.le`

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

### D071: `Nat`

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

### D076: `Real`

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

### D077: `Real.instAddGroup`

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

### D078: `Real.instDivInvMonoid`

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

### D079: `Real.instLE`

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

### D080: `Real.instMul`

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

### D081: `Real.instNatCast`

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

### D082: `Real.instOne`

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

### D083: `Real.lattice`

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

### D084: `abs`

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

### D085: `instHDiv`

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

### D086: `instHMul`

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

### D087: `instOfNatAtLeastTwo`

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

### D088: `instOfNatNat`

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

### D089: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D090: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D091: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D092: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D093: `HAdd.hAdd`

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

### D094: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D095: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D096: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D097: `LT.lt`

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

### D098: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D099: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D100: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → (F_1 : (t : Nat) → (f : @Nat.below.{u} motive t) → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D101: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D102: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D103: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D104: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eb5c70d9b813d7099537e8db11f59a65a3f5ad951da7314a1aa554471a122049`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero (M i)] → Zero ((i : ι) → M i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero.{u_5} (M i)] → Zero.{max u_1 u_5} ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Zero (M i)] => { zero := fun x => 0 }
```

### D105: `Real.instAdd`

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

### D106: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D107: `Real.instLT`

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

### D108: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D109: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D110: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D111: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D112: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D113: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D114: `instAddNat`

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

### D115: `instHAdd`

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

### D116: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D117: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D118: `instLTNat`

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

### D119: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} →
  (t : Nat) → (zero : motive Nat.zero) → (succ : (n : Nat) → motive (Nat.succ n)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D120: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D121: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D122: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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
