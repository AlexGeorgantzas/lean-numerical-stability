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
- Semantic SHA-256: `85f2f086955453d6a2d870b44117beca5f3a6d0996f8607a8118d458a36419fe`

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
fun n self => self.12
```

### D015: `HighamBench.P08IterativeRefinementRun.Ainv`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b13393dd2007ec7b119a102881fb8d9ce6e29491cad66c4a82b842082e01280d`

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

### D016: `HighamBench.P08IterativeRefinementRun.b`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `90deb8b3cf8e5a340ce1bde5cb32f2d0f43225d06d77b01f9d60ccaa450814ba`

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
fun n self => self.16
```

### D017: `HighamBench.P08IterativeRefinementRun.correction`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `95a14dfc4c0311ba3f7c922d3d473a2e213593713bf86d6ec9d9bcfb6571368c`

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
fun n self => self.24
```

### D018: `HighamBench.P08IterativeRefinementRun.iterate`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `836574bf044469fb2e1989ada8641ce5e2ba72a65a90b5546b99d2138b17f1ff`

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
fun n self => self.22
```

### D019: `HighamBench.P08IterativeRefinementRun.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `ab1d4981689407c76646be74fcb3dad9570376f69a96a275e6e8a4b1a5810373`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (precision : HighamBench.P08ResidualPrecision) →
      (u : Real) →
        Real.instLT.lt 0 u →
          Real.instLE.le (instHMul.hMul n.cast u) (1 / 100) →
            (workingModel : HighamBench.P08ScalarArithmeticModel) →
              Eq workingModel.unitRoundoff u →
                (residualModel : HighamBench.P08ScalarArithmeticModel) →
                  Eq residualModel.unitRoundoff (HighamBench.p08ResidualUnitRoundoff precision u) →
                    (convert : Real → Real) →
                      (∀ (x : Real),
                          Exists fun delta =>
                            And (Real.instLE.le (abs delta) u)
                              (Eq (convert x) (instHMul.hMul x (instHAdd.hAdd 1 delta)))) →
                        (A Ainv : Fin n → Fin n → Real) →
                          Eq (HighamBench.p08MatMul Ainv A) (HighamBench.p08IdMatrix n) →
                            Eq (HighamBench.p08MatMul A Ainv) (HighamBench.p08IdMatrix n) →
                              (b exactSolution : Fin n → Real) →
                                Eq (HighamBench.p08MatVec A exactSolution) b →
                                  (C1 : Fin n → Fin n → Real) →
                                    HighamBench.p08MatNonnegative C1 →
                                      (initialSolve :
                                          HighamBench.P08ColumnPivotedSolveCertificate workingModel A b C1 u) →
                                        (iterate computedResidual correction : Nat → Fin n → Real) →
                                          (Eq (iterate 0) fun x => 0) →
                                            Eq (iterate 1) initialSolve.output →
                                              (Eq (computedResidual 0) fun i => Real.instNeg.neg (b i)) →
                                                (Eq (correction 0) fun i => Real.instNeg.neg (iterate 1 i)) →
                                                  (residualTrace :
                                                      (m : Nat) →
                                                        HighamBench.P08SubtractionLastResidualTrace precision
                                                          residualModel convert A b (iterate (instHAdd.hAdd m 1))) →
                                                    (∀ (m : Nat),
                                                        Eq (computedResidual (instHAdd.hAdd m 1))
                                                          (residualTrace m).output) →
                                                      (correctionSolve :
                                                          (m : Nat) →
                                                            HighamBench.P08ColumnPivotedSolveCertificate workingModel A
                                                              (computedResidual m) C1 u) →
                                                        (∀ (m : Nat), Eq (correction m) (correctionSolve m).output) →
                                                          (∀ (m : Nat) (i : Fin n),
                                                              Eq (iterate (instHAdd.hAdd m 1) i)
                                                                (workingModel.flSub (iterate m i) (correction m i))) →
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
            (workingModel : HighamBench.P08ScalarArithmeticModel) →
              (working_roundoff : @Eq.{1} Real (HighamBench.P08ScalarArithmeticModel.unitRoundoff workingModel) u) →
                (residualModel : HighamBench.P08ScalarArithmeticModel) →
                  (residual_roundoff :
                      @Eq.{1} Real (HighamBench.P08ScalarArithmeticModel.unitRoundoff residualModel)
                        (HighamBench.p08ResidualUnitRoundoff precision u)) →
                    (convert : Real → Real) →
                      (conversion_model :
                          ∀ (x : Real),
                            @Exists.{1} Real fun (delta : Real) =>
                              And (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup delta) u)
                                (@Eq.{1} Real (convert x)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                      delta)))) →
                        (A Ainv : Fin n → Fin n → Real) →
                          (inverse_left :
                              @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p08MatMul n Ainv A)
                                (HighamBench.p08IdMatrix n)) →
                            (inverse_right :
                                @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p08MatMul n A Ainv)
                                  (HighamBench.p08IdMatrix n)) →
                              (b exactSolution : Fin n → Real) →
                                (exact_system : @Eq.{1} (Fin n → Real) (@HighamBench.p08MatVec n A exactSolution) b) →
                                  (C1 : Fin n → Fin n → Real) →
                                    (C1_nonnegative : @HighamBench.p08MatNonnegative n C1) →
                                      (initialSolve :
                                          @HighamBench.P08ColumnPivotedSolveCertificate n workingModel A b C1 u) →
                                        (iterate computedResidual correction : Nat → Fin n → Real) →
                                          (iterate_zero :
                                              @Eq.{1} (Fin n → Real)
                                                (iterate (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                fun (x : Fin n) =>
                                                @OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                            (iterate_one :
                                                @Eq.{1} (Fin n → Real)
                                                  (iterate
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@HighamBench.P08ColumnPivotedSolveCertificate.output n workingModel A
                                                    b C1 u initialSolve)) →
                                              (residual_zero :
                                                  @Eq.{1} (Fin n → Real)
                                                    (computedResidual
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                    fun (i : Fin n) => @Neg.neg.{0} Real Real.instNeg (b i)) →
                                                (correction_zero :
                                                    @Eq.{1} (Fin n → Real)
                                                      (correction
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      fun (i : Fin n) =>
                                                      @Neg.neg.{0} Real Real.instNeg
                                                        (iterate
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                          i)) →
                                                  (residualTrace :
                                                      (m : Nat) →
                                                        @HighamBench.P08SubtractionLastResidualTrace n precision
                                                          residualModel convert A b
                                                          (iterate
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) m
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))) →
                                                    (residual_trace_output :
                                                        ∀ (m : Nat),
                                                          @Eq.{1} (Fin n → Real)
                                                            (computedResidual
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) m
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (@HighamBench.P08SubtractionLastResidualTrace.output n
                                                              precision residualModel convert A b
                                                              (iterate
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) m
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              (residualTrace m))) →
                                                      (correctionSolve :
                                                          (m : Nat) →
                                                            @HighamBench.P08ColumnPivotedSolveCertificate n workingModel
                                                              A (computedResidual m) C1 u) →
                                                        (correction_output :
                                                            ∀ (m : Nat),
                                                              @Eq.{1} (Fin n → Real) (correction m)
                                                                (@HighamBench.P08ColumnPivotedSolveCertificate.output n
                                                                  workingModel A (computedResidual m) C1 u
                                                                  (correctionSolve m))) →
                                                          (update_computation :
                                                              ∀ (m : Nat) (i : Fin n),
                                                                @Eq.{1} Real
                                                                  (iterate
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) m
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))
                                                                    i)
                                                                  (HighamBench.P08ScalarArithmeticModel.flSub
                                                                    workingModel (iterate m i) (correction m i))) →
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
- Semantic SHA-256: `820b5da34de9963773519b1a761c8c11371c85943cd5809a2713d99d0df5290b`

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
                (Real.instLE.le
                      (instHMul.hMul (instHMul.hMul constants.c1 run.u) (HighamBench.p08KappaInverse run norm))
                      (1 / 2) →
                    ∀ (m : Nat) (i : Fin n),
                      Real.instLE.le (abs ((run.correctionSolve m).backwardError i))
                        (instHAdd.hAdd
                          (instHMul.hMul run.u
                            (HighamBench.p08MatVec (HighamBench.p08MatMul constants.C2 (HighamBench.p08AbsMatrix run.A))
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
                          (@abs.{0} Real Real.lattice Real.instAddGroup
                            (@HighamBench.P08ColumnPivotedSolveCertificate.backwardError n
                              (@HighamBench.P08IterativeRefinementRun.workingModel n run)
                              (@HighamBench.P08IterativeRefinementRun.A n run)
                              (@HighamBench.P08IterativeRefinementRun.computedResidual n run m)
                              (@HighamBench.P08IterativeRefinementRun.C1 n run)
                              (@HighamBench.P08IterativeRefinementRun.u n run)
                              (@HighamBench.P08IterativeRefinementRun.correctionSolve n run m) i))
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
- Semantic SHA-256: `4a742ed2a083d341d7389896497910c6584f007dcf88c3b7bfa64bc38080b51b`

Type:

```lean
{n : Nat} →
  HighamBench.P08ScalarArithmeticModel → (Fin n → Fin n → Real) → (Fin n → Real) → (Fin n → Fin n → Real) → Real → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (model : HighamBench.P08ScalarArithmeticModel) →
    (A : Fin n → Fin n → Real) → (rhs : Fin n → Real) → (C1 : Fin n → Fin n → Real) → (u : Real) → Type
```

### D032: `HighamBench.P08ColumnPivotedSolveCertificate.backwardError`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7f2bf591bcaf3e103d5204bbda24f4ed2597fea06069bee014ae32c14d9ba5a6`

Type:

```lean
{n : Nat} →
  {model : HighamBench.P08ScalarArithmeticModel} →
    {A : Fin n → Fin n → Real} →
      {rhs : Fin n → Real} →
        {C1 : Fin n → Fin n → Real} →
          {u : Real} → HighamBench.P08ColumnPivotedSolveCertificate model A rhs C1 u → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {model : HighamBench.P08ScalarArithmeticModel} →
    {A : Fin n → Fin n → Real} →
      {rhs : Fin n → Real} →
        {C1 : Fin n → Fin n → Real} →
          {u : Real} → (self : @HighamBench.P08ColumnPivotedSolveCertificate n model A rhs C1 u) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n model A rhs C1 u self => self.3
```

### D033: `HighamBench.P08ColumnPivotedSolveCertificate.output`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `54cbe1342c9bdf08751602d675ad8f7beb46818f6a52638defa77739b6b0ac3c`

Type:

```lean
{n : Nat} →
  {model : HighamBench.P08ScalarArithmeticModel} →
    {A : Fin n → Fin n → Real} →
      {rhs : Fin n → Real} →
        {C1 : Fin n → Fin n → Real} →
          {u : Real} → HighamBench.P08ColumnPivotedSolveCertificate model A rhs C1 u → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {model : HighamBench.P08ScalarArithmeticModel} →
    {A : Fin n → Fin n → Real} →
      {rhs : Fin n → Real} →
        {C1 : Fin n → Fin n → Real} →
          {u : Real} → (self : @HighamBench.P08ColumnPivotedSolveCertificate n model A rhs C1 u) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n model A rhs C1 u self => self.1
```

### D034: `HighamBench.P08DimensionOnlyConstantBounds.matrixEntry`

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

### D035: `HighamBench.P08DimensionOnlyConstantBounds.scalar`

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

### D036: `HighamBench.P08IterativeRefinementRun.C1`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `11db68dc524b6f4453b97274ae61cebe6f397e015f167ebc73d342d233c94d77`

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
fun n self => self.19
```

### D037: `HighamBench.P08IterativeRefinementRun.computedResidual`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `58270e7b7c127cccb8493ee87248f50d8b8227e2332d1c36b3359b50eacfbfa0`

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
fun n self => self.23
```

### D038: `HighamBench.P08IterativeRefinementRun.correctionSolve`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `49c7a58fecc0b38fa47e1a7aee4d392460fab5da334be050109887a543bdff61`

Type:

```lean
{n : Nat} →
  (self : HighamBench.P08IterativeRefinementRun n) →
    (m : Nat) →
      HighamBench.P08ColumnPivotedSolveCertificate self.workingModel self.A (self.computedResidual m) self.C1 self.u
```

Fully explicit type:

```lean
{n : Nat} →
  (self : HighamBench.P08IterativeRefinementRun n) →
    (m : Nat) →
      @HighamBench.P08ColumnPivotedSolveCertificate n (@HighamBench.P08IterativeRefinementRun.workingModel n self)
        (@HighamBench.P08IterativeRefinementRun.A n self)
        (@HighamBench.P08IterativeRefinementRun.computedResidual n self m)
        (@HighamBench.P08IterativeRefinementRun.C1 n self) (@HighamBench.P08IterativeRefinementRun.u n self)
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.31
```

### D039: `HighamBench.P08IterativeRefinementRun.exactSolution`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `14d7b8a66771d4d9ee275d3281507a2d8dcedc0f9509dd1004df9cff35fa15e9`

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
fun n self => self.17
```

### D040: `HighamBench.P08IterativeRefinementRun.precision`

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

### D041: `HighamBench.P08IterativeRefinementRun.workingModel`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `197f8cf0352d97d80831ac9a763d9dda5f4184951698067c96f49e3b7ab078ff`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → HighamBench.P08ScalarArithmeticModel
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P08IterativeRefinementRun n) → HighamBench.P08ScalarArithmeticModel
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D042: `HighamBench.P08Lemma43Constants.C10`

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

### D043: `HighamBench.P08Lemma43Constants.C11`

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

### D044: `HighamBench.P08Lemma43Constants.C12`

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

### D045: `HighamBench.P08Lemma43Constants.C2`

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

### D046: `HighamBench.P08Lemma43Constants.C8`

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

### D047: `HighamBench.P08Lemma43Constants.c1`

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

### D048: `HighamBench.P08Lemma43Constants.c5`

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

### D049: `HighamBench.P08ResidualPrecision`

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

### D050: `HighamBench.P08ScalarArithmeticModel`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `e7bbc2335c38e8a786a9d00d6341c669a3a2294cbf8f0288fb3e9880eab5f68d`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D051: `HighamBench.P08ScalarArithmeticModel.flSub`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8adc77897914530b6395788942bbc1bf0bcf3f0c982d3510fbafa07bd301f628`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D052: `HighamBench.P08ScalarArithmeticModel.unitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `79af0e36b62b3ea8268fe82fc682fe415d0aa3c886259b931dbd042931597b88`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08ScalarArithmeticModel) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D053: `HighamBench.P08SubtractionLastResidualTrace`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `853ac33b96eada40f12ea75106ed15e56a6c8b83e44c7a5e212fcb29695b75a6`

Type:

```lean
{n : Nat} →
  HighamBench.P08ResidualPrecision →
    HighamBench.P08ScalarArithmeticModel →
      (Real → Real) → (Fin n → Fin n → Real) → (Fin n → Real) → (Fin n → Real) → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (precision : HighamBench.P08ResidualPrecision) →
    (residualModel : HighamBench.P08ScalarArithmeticModel) →
      (convert : Real → Real) → (A : Fin n → Fin n → Real) → (b x : Fin n → Real) → Type
```

### D054: `HighamBench.P08SubtractionLastResidualTrace.output`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `42f5c5faaadde417e3048fe02066ab5f3088fa6f1e36636a3fc3a06cc41a686b`

Type:

```lean
{n : Nat} →
  {precision : HighamBench.P08ResidualPrecision} →
    {residualModel : HighamBench.P08ScalarArithmeticModel} →
      {convert : Real → Real} →
        {A : Fin n → Fin n → Real} →
          {b x : Fin n → Real} →
            HighamBench.P08SubtractionLastResidualTrace precision residualModel convert A b x → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {precision : HighamBench.P08ResidualPrecision} →
    {residualModel : HighamBench.P08ScalarArithmeticModel} →
      {convert : Real → Real} →
        {A : Fin n → Fin n → Real} →
          {b x : Fin n → Real} →
            (self : @HighamBench.P08SubtractionLastResidualTrace n precision residualModel convert A b x) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n precision residualModel convert A b x self => self.3
```

### D055: `HighamBench.p08AbsVec`

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

### D056: `HighamBench.p08BasisVector`

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

### D057: `HighamBench.p08IdMatrix`

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

### D058: `HighamBench.p08Lemma43c3`

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

### D059: `HighamBench.p08Lemma43c4`

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

### D060: `HighamBench.p08MatAdd`

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

### D061: `HighamBench.p08MatNonnegative`

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

### D062: `HighamBench.p08MatPow.match_1`

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

### D063: `HighamBench.p08MatScale`

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

### D064: `HighamBench.p08MatSub`

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

### D065: `HighamBench.p08ResidualUnitRoundoff`

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

### D066: `HighamBench.p08VecScale`

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

### D067: `HighamBench.P08ColumnPivotedSolveCertificate.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `d44df443c4835549078a664241bff572d99a62f4d3e457329d0c4d8a5d2b0696`

Type:

```lean
{n : Nat} →
  {model : HighamBench.P08ScalarArithmeticModel} →
    {A : Fin n → Fin n → Real} →
      {rhs : Fin n → Real} →
        {C1 : Fin n → Fin n → Real} →
          {u : Real} →
            (output : Fin n → Real) →
              HighamBench.P08ColumnPivotedGaussianEliminationTrace model A rhs output →
                (backwardError : Fin n → Real) →
                  Eq (HighamBench.p08MatVec A output) (HighamBench.p08VecAdd rhs backwardError) →
                    (∀ (i : Fin n),
                        Real.instLE.le (abs (backwardError i))
                          (instHMul.hMul u (HighamBench.p08MatVec C1 (HighamBench.p08AbsAction A output) i))) →
                      HighamBench.P08ColumnPivotedSolveCertificate model A rhs C1 u
```

Fully explicit type:

```lean
{n : Nat} →
  {model : HighamBench.P08ScalarArithmeticModel} →
    {A : Fin n → Fin n → Real} →
      {rhs : Fin n → Real} →
        {C1 : Fin n → Fin n → Real} →
          {u : Real} →
            (output : Fin n → Real) →
              (execution : @HighamBench.P08ColumnPivotedGaussianEliminationTrace model n A rhs output) →
                (backwardError : Fin n → Real) →
                  (equation :
                      @Eq.{1} (Fin n → Real) (@HighamBench.p08MatVec n A output)
                        (@HighamBench.p08VecAdd n rhs backwardError)) →
                    (backward_error_bound :
                        ∀ (i : Fin n),
                          @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (backwardError i))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
                              (@HighamBench.p08MatVec n C1 (@HighamBench.p08AbsAction n A output) i))) →
                      @HighamBench.P08ColumnPivotedSolveCertificate n model A rhs C1 u
```

### D068: `HighamBench.P08ResidualPrecision.double`

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

### D069: `HighamBench.P08ResidualPrecision.single`

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

### D070: `HighamBench.P08ScalarArithmeticModel.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `24f2ea7999198982ad4a308c8470d6081fb22bd0a25b8593d507e73993ab37f9`

Type:

```lean
(unitRoundoff : Real) →
  Real.instLE.le 0 unitRoundoff →
    (flAdd flSub flMul flDiv : Real → Real → Real) →
      (∀ (x y : Real),
          Exists fun delta =>
            And (Real.instLE.le (abs delta) unitRoundoff)
              (Eq (flAdd x y) (instHMul.hMul (instHAdd.hAdd x y) (instHAdd.hAdd 1 delta)))) →
        (∀ (x y : Real),
            Exists fun delta =>
              And (Real.instLE.le (abs delta) unitRoundoff)
                (Eq (flSub x y) (instHMul.hMul (instHSub.hSub x y) (instHAdd.hAdd 1 delta)))) →
          (∀ (x y : Real),
              Exists fun delta =>
                And (Real.instLE.le (abs delta) unitRoundoff)
                  (Eq (flMul x y) (instHMul.hMul (instHMul.hMul x y) (instHAdd.hAdd 1 delta)))) →
            (∀ (x y : Real),
                Ne y 0 →
                  Exists fun delta =>
                    And (Real.instLE.le (abs delta) unitRoundoff)
                      (Eq (flDiv x y) (instHMul.hMul (instHDiv.hDiv x y) (instHAdd.hAdd 1 delta)))) →
              HighamBench.P08ScalarArithmeticModel
```

Fully explicit type:

```lean
(unitRoundoff : Real) →
  (unitRoundoff_nonneg :
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        unitRoundoff) →
    (flAdd flSub flMul flDiv : Real → Real → Real) →
      (add_model :
          ∀ (x y : Real),
            @Exists.{1} Real fun (delta : Real) =>
              And (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup delta) unitRoundoff)
                (@Eq.{1} Real (flAdd x y)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) delta)))) →
        (sub_model :
            ∀ (x y : Real),
              @Exists.{1} Real fun (delta : Real) =>
                And (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup delta) unitRoundoff)
                  (@Eq.{1} Real (flSub x y)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) x y)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) delta)))) →
          (mul_model :
              ∀ (x y : Real),
                @Exists.{1} Real fun (delta : Real) =>
                  And (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup delta) unitRoundoff)
                    (@Eq.{1} Real (flMul x y)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x y)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) delta)))) →
            (div_model :
                ∀ (x y : Real),
                  @Ne.{1} Real y (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    @Exists.{1} Real fun (delta : Real) =>
                      And
                        (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup delta) unitRoundoff)
                        (@Eq.{1} Real (flDiv x y)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) x y)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) delta)))) →
              HighamBench.P08ScalarArithmeticModel
```

### D071: `HighamBench.P08SubtractionLastResidualTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `9f043e9784e45839aa3b5f755595e064c62125610855a11b0c177fe25902f99f`

Type:

```lean
{n : Nat} →
  {precision : HighamBench.P08ResidualPrecision} →
    {residualModel : HighamBench.P08ScalarArithmeticModel} →
      {convert : Real → Real} →
        {A : Fin n → Fin n → Real} →
          {b x : Fin n → Real} →
            (roundedAx beforeConversion output : Fin n → Real) →
              (∀ (i : Fin n), Eq (roundedAx i) (HighamBench.p08RoundedDot residualModel A x i)) →
                (∀ (i : Fin n), Eq (beforeConversion i) (residualModel.flSub (roundedAx i) (b i))) →
                  Eq output
                      (HighamBench.p08ResidualUnitRoundoff.match_1 (fun precision => Fin n → Real) precision
                        (fun _ => beforeConversion) fun _ i => convert (beforeConversion i)) →
                    HighamBench.P08SubtractionLastResidualTrace precision residualModel convert A b x
```

Fully explicit type:

```lean
{n : Nat} →
  {precision : HighamBench.P08ResidualPrecision} →
    {residualModel : HighamBench.P08ScalarArithmeticModel} →
      {convert : Real → Real} →
        {A : Fin n → Fin n → Real} →
          {b x : Fin n → Real} →
            (roundedAx beforeConversion output : Fin n → Real) →
              (roundedAx_relation :
                  ∀ (i : Fin n), @Eq.{1} Real (roundedAx i) (@HighamBench.p08RoundedDot residualModel n A x i)) →
                (subtraction_last :
                    ∀ (i : Fin n),
                      @Eq.{1} Real (beforeConversion i)
                        (HighamBench.P08ScalarArithmeticModel.flSub residualModel (roundedAx i) (b i))) →
                  (output_relation :
                      @Eq.{1} (Fin n → Real) output
                        (HighamBench.p08ResidualUnitRoundoff.match_1.{1}
                          (fun (precision : HighamBench.P08ResidualPrecision) => Fin n → Real) precision
                          (fun (_ : Unit) => beforeConversion) fun (_ : Unit) (i : Fin n) =>
                          convert (beforeConversion i))) →
                    @HighamBench.P08SubtractionLastResidualTrace n precision residualModel convert A b x
```

### D072: `HighamBench.p08ResidualUnitRoundoff.match_1`

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

### D073: `HighamBench.P08ColumnPivotedGaussianEliminationTrace`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `04ef73fc38e76e7aa817d01e5e91d746fd8a6d6d1369d6142456a8c1e7a9638e`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → {n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → (Fin n → Real) → Type
```

Fully explicit type:

```lean
(model : HighamBench.P08ScalarArithmeticModel) →
  {n : Nat} → (A : Fin n → Fin n → Real) → (rhs output : Fin n → Real) → Type
```

### D074: `HighamBench.P08ResidualPrecision.casesOn`

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

### D075: `HighamBench.p08AbsAction`

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

### D076: `HighamBench.p08RoundedDot`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5ed6a73db466e72c573339b7f8660f2cd8603f77c90d1ed10f24aa41f15e75b9`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → {n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
(model : HighamBench.P08ScalarArithmeticModel) →
  {n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → (i : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model {n} A x i => HighamBench.recursiveSum model.flAdd n fun j => model.flMul (A i j) (x j)
```

### D077: `HighamBench.P08ColumnPivotedGaussianEliminationTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `5c979a9ca09c426bc2ed032a04c306277455a9accc6d7f0f552352ce087aeefa`

Type:

```lean
{model : HighamBench.P08ScalarArithmeticModel} →
  {n : Nat} →
    {A : Fin n → Fin n → Real} →
      {rhs output : Fin n → Real} →
        (matrixState : Nat → Fin n → Fin n → Real) →
          (rhsState : Nat → Fin n → Real) →
            (pivotRow : Fin n → Fin n) →
              Eq (matrixState 0) A →
                Eq (rhsState 0) rhs →
                  (∀ (k : Fin n), instLENat.le k.val (pivotRow k).val) →
                    (∀ (k i : Fin n),
                        instLENat.le k.val i.val →
                          Real.instLE.le (abs (matrixState k.val i k)) (abs (matrixState k.val (pivotRow k) k))) →
                      (∀ (k : Fin n), Ne (matrixState k.val (pivotRow k) k) 0) →
                        (∀ (k : Fin n),
                            Eq (matrixState (instHAdd.hAdd k.val 1))
                              (HighamBench.p08ColumnPivotedMatrixStep model (matrixState k.val) k (pivotRow k))) →
                          (∀ (k : Fin n),
                              Eq (rhsState (instHAdd.hAdd k.val 1))
                                (HighamBench.p08ColumnPivotedRhsStep model (matrixState k.val) (rhsState k.val) k
                                  (pivotRow k))) →
                            (∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (matrixState n i j) 0) →
                              (∀ (i : Fin n), Ne (matrixState n i i) 0) →
                                (∀ (i : Fin n),
                                    Eq (output i)
                                      (model.flDiv
                                        (model.flSub (rhsState n i)
                                          (HighamBench.p08RoundedUpperTailDot model (matrixState n) output i))
                                        (matrixState n i i))) →
                                  HighamBench.P08ColumnPivotedGaussianEliminationTrace model A rhs output
```

Fully explicit type:

```lean
{model : HighamBench.P08ScalarArithmeticModel} →
  {n : Nat} →
    {A : Fin n → Fin n → Real} →
      {rhs output : Fin n → Real} →
        (matrixState : Nat → Fin n → Fin n → Real) →
          (rhsState : Nat → Fin n → Real) →
            (pivotRow : Fin n → Fin n) →
              (initial_matrix :
                  @Eq.{1} (Fin n → Fin n → Real)
                    (matrixState (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) A) →
                (initial_rhs :
                    @Eq.{1} (Fin n → Real) (rhsState (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      rhs) →
                  (pivot_active : ∀ (k : Fin n), @LE.le.{0} Nat instLENat (@Fin.val n k) (@Fin.val n (pivotRow k))) →
                    (pivot_largest :
                        ∀ (k i : Fin n),
                          @LE.le.{0} Nat instLENat (@Fin.val n k) (@Fin.val n i) →
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup (matrixState (@Fin.val n k) i k))
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (matrixState (@Fin.val n k) (pivotRow k) k))) →
                      (pivot_nonzero :
                          ∀ (k : Fin n),
                            @Ne.{1} Real (matrixState (@Fin.val n k) (pivotRow k) k)
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                        (matrix_step :
                            ∀ (k : Fin n),
                              @Eq.{1} (Fin n → Fin n → Real)
                                (matrixState
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@HighamBench.p08ColumnPivotedMatrixStep model n (matrixState (@Fin.val n k)) k
                                  (pivotRow k))) →
                          (rhs_step :
                              ∀ (k : Fin n),
                                @Eq.{1} (Fin n → Real)
                                  (rhsState
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (@HighamBench.p08ColumnPivotedRhsStep model n (matrixState (@Fin.val n k))
                                    (rhsState (@Fin.val n k)) k (pivotRow k))) →
                            (final_upper_triangular :
                                ∀ (i j : Fin n),
                                  @LT.lt.{0} Nat instLTNat (@Fin.val n j) (@Fin.val n i) →
                                    @Eq.{1} Real (matrixState n i j)
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                              (final_diagonal_nonzero :
                                  ∀ (i : Fin n),
                                    @Ne.{1} Real (matrixState n i i)
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                                (back_substitution :
                                    ∀ (i : Fin n),
                                      @Eq.{1} Real (output i)
                                        (HighamBench.P08ScalarArithmeticModel.flDiv model
                                          (HighamBench.P08ScalarArithmeticModel.flSub model (rhsState n i)
                                            (@HighamBench.p08RoundedUpperTailDot model n (matrixState n) output i))
                                          (matrixState n i i))) →
                                  @HighamBench.P08ColumnPivotedGaussianEliminationTrace model n A rhs output
```

### D078: `HighamBench.P08ResidualPrecision.rec`

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

### D079: `HighamBench.P08ScalarArithmeticModel.flAdd`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `f37bcf5a6659cff51cd1b022d2627bd079c93426b02455c6a219dc49fae413af`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D080: `HighamBench.P08ScalarArithmeticModel.flMul`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `251455074a55a647642d6f6bfec0f277e2acf648d8ca2ce8cb324f29bc1e750f`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D081: `HighamBench.recursiveSum`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `3a24e7a5c707c014d59b9d90d536db1f1c79ef135d2ba34adb6af8a4258efe41`

Type:

```lean
(Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
(flAdd : Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun flAdd x x_1 =>
  Nat.brecOn (motive := fun x => (Fin x → Real) → Real) x
    (fun x f x_2 =>
      HighamBench.recursiveSum.match_1 (fun x x_3 => Nat.below (motive := fun x => (Fin x → Real) → Real) x → Real) x
        x_2 (fun x x_3 => 0)
        (fun n v x => if h : Eq n 0 then v ⟨0, ⋯⟩ else flAdd (x.1 fun i => v i.castSucc) (v (Fin.last n))) f)
    x_1
```

### D082: `HighamBench.P08ScalarArithmeticModel.flDiv`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `e89ab6cb2f2f523f7cb018bdfc5e5e280ac7b52c225d3490a0126ff08d339b2a`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P08ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D083: `HighamBench.p08ColumnPivotedMatrixStep`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `309cb8a5d5954c0c8eb38407c8d1f1223ca7491444f306ba2ccdce14b967ff64`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → {n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
(model : HighamBench.P08ScalarArithmeticModel) →
  {n : Nat} → (A : Fin n → Fin n → Real) → (k pivot : Fin n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun model {n} A k pivot =>
  have swapped := HighamBench.p08SwapRowsMatrix A k pivot;
  fun i j =>
  ite (instLENat.le i.val k.val) (swapped i j)
    (ite (instLTNat.lt j.val k.val) (swapped i j)
      (ite (Eq j k) 0
        (model.flSub (swapped i j) (model.flMul (model.flDiv (swapped i k) (swapped k k)) (swapped k j)))))
```

### D084: `HighamBench.p08ColumnPivotedRhsStep`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `73efa32de8540c40dd4faddb7e508fdd616fbd985fe9b2e9847cfc54d8baea37`

Type:

```lean
HighamBench.P08ScalarArithmeticModel →
  {n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
(model : HighamBench.P08ScalarArithmeticModel) →
  {n : Nat} → (A : Fin n → Fin n → Real) → (b : Fin n → Real) → (k pivot : Fin n) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun model {n} A b k pivot =>
  have swappedA := HighamBench.p08SwapRowsMatrix A k pivot;
  have swappedB := HighamBench.p08SwapRowsVector b k pivot;
  fun i =>
  ite (instLENat.le i.val k.val) (swappedB i)
    (model.flSub (swappedB i) (model.flMul (model.flDiv (swappedA i k) (swappedA k k)) (swappedB k)))
```

### D085: `HighamBench.p08RoundedUpperTailDot`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `096124e2679f3fa41ab051e331b5aa95013b219c956664030878e8932f480f34`

Type:

```lean
HighamBench.P08ScalarArithmeticModel → {n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
(model : HighamBench.P08ScalarArithmeticModel) →
  {n : Nat} → (U : Fin n → Fin n → Real) → (x : Fin n → Real) → (i : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model {n} U x i =>
  HighamBench.recursiveSum model.flAdd (instHSub.hSub n (instHAdd.hAdd i.val 1)) fun j =>
    model.flMul (U i (HighamBench.p08UpperTailIndex i j)) (x (HighamBench.p08UpperTailIndex i j))
```

### D086: `HighamBench.recursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `theorem`
- Distance from target type: `7`
- Semantic SHA-256: `7f01e5fdb761df0e050b0929b93312fc9084bc345726c816952ed0fd4844be27`

Type:

```lean
∀ (n : Nat), Eq n 0 → instLTNat.lt 0 (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ (n : Nat) (h : @Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D087: `HighamBench.recursiveSum.match_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `56d4f4744c0103a83d3305dc49473baf5a72c1037bbec52ff87f6f4a5419f79e`

Type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      ((x : Fin 0 → Real) → motive 0 x) →
        ((n : Nat) → (v : Fin (instHAdd.hAdd n 1) → Real) → motive n.succ v) → motive x x_1
```

Fully explicit type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      (h_1 :
          (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Real) →
            motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) →
        (h_2 :
            (n : Nat) →
              (v :
                  Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Real) →
                motive (Nat.succ n) v) →
          motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : Fin x → Real) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

### D088: `HighamBench.p08SwapRowsMatrix`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `f22db28acb57c47540470b2443d37f59d2b41281d6e9f25ac2af5f6f7b8dc238`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (r s : Fin n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A r s i j => ite (Eq i r) (A s j) (ite (Eq i s) (A r j) (A i j))
```

### D089: `HighamBench.p08SwapRowsVector`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `697d1103f6d5a8aef9aa5bcf7afe54af67419b72a4479ae1f1c04969c16a2aa4`

Type:

```lean
{n : Nat} → (Fin n → Real) → Fin n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (b : Fin n → Real) → (r s : Fin n) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} b r s i => ite (Eq i r) (b s) (ite (Eq i s) (b r) (b i))
```

### D090: `HighamBench.p08UpperTailIndex`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `ba1de8e9f5ed31084b6b5adda945b1c8c9dca6e1153a406a978b4b09f15a55c7`

Type:

```lean
{n : Nat} → (i : Fin n) → Fin (instHSub.hSub n (instHAdd.hAdd i.val 1)) → Fin n
```

Fully explicit type:

```lean
{n : Nat} →
  (i : Fin n) →
    (j :
        Fin
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      Fin n
```

Definition body (one-level semantic boundary):

```lean
fun {n} i j => ⟨instHAdd.hAdd (instHAdd.hAdd i.val 1) j.val, ⋯⟩
```

### D091: `HighamBench.p08UpperTailIndex._proof_2`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `theorem`
- Distance from target type: `9`
- Semantic SHA-256: `ee246c405abf2f153e4341862aad32b4ad86ebd9874969b6c70b1d7948e3dcf2`

Type:

```lean
∀ {n : Nat} (i : Fin n) (j : Fin (instHSub.hSub n (instHAdd.hAdd i.val 1))),
  instLTNat.lt (instHAdd.hAdd (instHAdd.hAdd i.val 1) j.val) n
```

Fully explicit type:

```lean
∀ {n : Nat} (i : Fin n)
  (j :
    Fin
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Fin.val
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        j))
    n
```

### D092: `DivInvMonoid.toDiv`

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

### D093: `Fin`

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

### D094: `HDiv.hDiv`

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

### D095: `HMul.hMul`

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

### D096: `LE.le`

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

### D097: `Nat`

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

### D101: `One.toOfNat1`

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

### D103: `Real.instAddGroup`

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

### D104: `Real.instDivInvMonoid`

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

### D105: `Real.instLE`

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

### D106: `Real.instMul`

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

### D107: `Real.instNatCast`

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

### D108: `Real.instOne`

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

### D109: `Real.lattice`

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

### D110: `abs`

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

### D111: `instHDiv`

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

### D112: `instHMul`

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

### D113: `instOfNatAtLeastTwo`

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

### D114: `instOfNatNat`

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

### D115: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D116: `Eq`

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

### D117: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D118: `Fin.fintype`

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

### D119: `Finset.sum`

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

### D120: `Finset.univ`

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

### D121: `HAdd.hAdd`

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

### D122: `HPow.hPow`

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

### D123: `HSub.hSub`

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

### D124: `Iff`

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

### D125: `LT.lt`

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

### D126: `Monoid.toNatPow`

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

### D127: `Nat.below`

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

### D128: `Nat.brecOn`

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

### D129: `Nat.cast`

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

### D130: `Nat.succ`

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

### D131: `Neg.neg`

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

### D132: `Pi.instZero`

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

### D133: `Real.instAdd`

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

### D134: `Real.instAddCommMonoid`

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

### D135: `Real.instLT`

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

### D136: `Real.instMonoid`

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

### D137: `Real.instNeg`

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

### D138: `Real.instSub`

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

### D139: `Real.instZero`

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

### D140: `Unit`

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

### D141: `Zero.toOfNat0`

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

### D142: `instAddNat`

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

### D143: `instHAdd`

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

### D144: `instHPow`

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

### D145: `instHSub`

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

### D146: `instLTNat`

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

### D147: `Nat.casesOn`

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

### D148: `Unit.unit`

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

### D149: `instDecidableEqFin`

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

### D150: `ite`

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

### D151: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D152: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
{n : Nat} →
  Fin n →
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D153: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `b7cf2c761ad02a28a34dfdeee30ac4ec7bd4c3ff77700313e3ed2f37d473f5f2`

Type:

```lean
(n : Nat) → Fin (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
(n : Nat) →
  Fin
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun n => ⟨n, ⋯⟩
```

### D154: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D155: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
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

### D156: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`

Type:

```lean
Prop → Prop
```

Fully explicit type:

```lean
(a : Prop) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D157: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `a2551097d29bac847f3c59e8213b5882afd4a95e9247c2382e8bce33011974b5`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (c → α) → (Not c → α) → α
```

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t : c → α) → (e : Not c → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h e t
```

### D158: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`

Type:

```lean
DecidableEq Nat
```

Fully explicit type:

```lean
DecidableEq.{1} Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.decEq
```

### D159: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D160: `Nat.decLe`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `931f48339aefbc000a30f94b69a993dd27e00f38323c7b45743dc5d6ffe51c35`

Type:

```lean
(n m : Nat) → Decidable (instLENat.le n m)
```

Fully explicit type:

```lean
(n m : Nat) → Decidable (@LE.le.{0} Nat instLENat n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => if h : Eq (n.ble m) Bool.true then Decidable.isTrue ⋯ else Decidable.isFalse ⋯
```

### D161: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `652ffb54717682f55eafca6c2b47fca31dfea599c9898709ba2f56fbc9113d99`

Type:

```lean
(n m : Nat) → Decidable (instLTNat.lt n m)
```

Fully explicit type:

```lean
(n m : Nat) → Decidable (@LT.lt.{0} Nat instLTNat n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => n.succ.decLe m
```

### D162: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `8`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`

Type:

```lean
Nat
```

Fully explicit type:

```lean
Nat
```

### D163: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `5b0e20a4d2b3e0a67bd35de1b5c84cc60d6dc867658112d84cad483055804868`

Type:

```lean
Sub Nat
```

Fully explicit type:

```lean
Sub.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ sub := Nat.sub }
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

### `HighamBench.P08Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P08Definitions.lean`
SHA-256: `a8ee8212c2fb281cac5afbbbea92cc09f4a07e22414a692fb103cb08b92a4845`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Square matrix-vector multiplication in the notation used for P08. -/
noncomputable def p08MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Square matrix multiplication in the notation used for P08. -/
noncomputable def p08MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Identity matrix for the paper-scoped matrix powers. -/
noncomputable def p08IdMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Matrix powers used in the finite recurrence certificate for Lemma 4.3. -/
noncomputable def p08MatPow {n : ℕ}
    (B : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0 => p08IdMatrix n
  | k + 1 => p08MatMul B (p08MatPow B k)

/-- Componentwise absolute matrix action, `(abs A) (abs x)`. -/
noncomputable def p08AbsAction {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * |x j|

/-- The expanded componentwise action `(abs A) (abs Ainv) (abs q)`. -/
noncomputable def p08AbsProductAction {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) (q : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * p08AbsAction Ainv q j

/-- Pointwise vector addition. -/
def p08VecAdd {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i + y i

/-- Pointwise vector subtraction. -/
def p08VecSub {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i - y i

/-- Scalar multiplication of a vector. -/
def p08VecScale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ a * x i

/-- Componentwise absolute value of a vector. -/
def p08AbsVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ |x i|

/-- Pointwise matrix addition. -/
def p08MatAdd {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A i j + B i j

/-- Pointwise matrix subtraction. -/
def p08MatSub {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A i j - B i j

/-- Scalar multiplication of a matrix. -/
def p08MatScale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ a * A i j

/-- Componentwise absolute value of a matrix. -/
def p08AbsMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ |A i j|

/-- Entrywise nonnegativity for source-defined `C_i` matrices. -/
def p08MatNonnegative {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- Single- or double-precision residual accumulation from section 4. -/
inductive P08ResidualPrecision where
  | single
  | double
  deriving DecidableEq

/-- The paper's precision-dependent residual unit roundoff `ubar`. -/
def p08ResidualUnitRoundoff (precision : P08ResidualPrecision)
    (u : ℝ) : ℝ :=
  match precision with
  | .single => u
  | .double => u ^ 2

/-- A total real-valued floating-point model with the relative-error
semantics assumed by P08. Totality excludes NaN, infinity, and undefined
operations from represented executions. -/
structure P08ScalarArithmeticModel where
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  flAdd : ℝ → ℝ → ℝ
  flSub : ℝ → ℝ → ℝ
  flMul : ℝ → ℝ → ℝ
  flDiv : ℝ → ℝ → ℝ
  add_model : ∀ x y, ∃ delta, |delta| ≤ unitRoundoff ∧
    flAdd x y = (x + y) * (1 + delta)
  sub_model : ∀ x y, ∃ delta, |delta| ≤ unitRoundoff ∧
    flSub x y = (x - y) * (1 + delta)
  mul_model : ∀ x y, ∃ delta, |delta| ≤ unitRoundoff ∧
    flMul x y = (x * y) * (1 + delta)
  div_model : ∀ x y, y ≠ 0 → ∃ delta, |delta| ≤ unitRoundoff ∧
    flDiv x y = (x / y) * (1 + delta)

/-- A rounded row dot product in the residual-accumulation precision. -/
noncomputable def p08RoundedDot
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  recursiveSum model.flAdd n fun j : Fin n ↦ model.flMul (A i j) (x j)

/-- A residual computation with the subtraction by `b` performed after the
rounded matrix-vector product. In the double variant the result is then
converted to working precision. -/
structure P08SubtractionLastResidualTrace {n : ℕ}
    (precision : P08ResidualPrecision)
    (residualModel : P08ScalarArithmeticModel)
    (convert : ℝ → ℝ) (A : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ) where
  roundedAx : Fin n → ℝ
  beforeConversion : Fin n → ℝ
  output : Fin n → ℝ
  roundedAx_relation : ∀ i,
    roundedAx i = p08RoundedDot residualModel A x i
  subtraction_last : ∀ i,
    beforeConversion i = residualModel.flSub (roundedAx i) (b i)
  output_relation : output =
    match precision with
    | .single => beforeConversion
    | .double => fun i ↦ convert (beforeConversion i)

/-- Swap two rows of a square matrix. -/
def p08SwapRowsMatrix {n : ℕ} (A : Fin n → Fin n → ℝ)
    (r s : Fin n) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = r then A s j else if i = s then A r j else A i j

/-- Swap two entries of a vector. -/
def p08SwapRowsVector {n : ℕ} (b : Fin n → ℝ)
    (r s : Fin n) : Fin n → ℝ :=
  fun i ↦ if i = r then b s else if i = s then b r else b i

/-- One rounded elimination step after the largest active entry in column
`k` has been moved into the pivot position. -/
noncomputable def p08ColumnPivotedMatrixStep
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (k pivot : Fin n) :
    Fin n → Fin n → ℝ :=
  let swapped := p08SwapRowsMatrix A k pivot
  fun i j ↦
    if i.val ≤ k.val then
      swapped i j
    else if j.val < k.val then
      swapped i j
    else if j = k then
      0
    else
      model.flSub (swapped i j)
        (model.flMul (model.flDiv (swapped i k) (swapped k k))
          (swapped k j))

/-- The rounded right-hand-side update paired with one elimination step. -/
noncomputable def p08ColumnPivotedRhsStep
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (k pivot : Fin n) : Fin n → ℝ :=
  let swappedA := p08SwapRowsMatrix A k pivot
  let swappedB := p08SwapRowsVector b k pivot
  fun i ↦
    if i.val ≤ k.val then
      swappedB i
    else
      model.flSub (swappedB i)
        (model.flMul (model.flDiv (swappedA i k) (swappedA k k))
          (swappedB k))

/-- Embed an index in the strict tail following row `i`. -/
def p08UpperTailIndex {n : ℕ} (i : Fin n)
    (j : Fin (n - (i.val + 1))) : Fin n :=
  ⟨i.val + 1 + j.val, by omega⟩

/-- Rounded upper-triangular tail dot product used by back substitution. -/
noncomputable def p08RoundedUpperTailDot
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (U : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  recursiveSum model.flAdd (n - (i.val + 1)) fun j ↦
    model.flMul (U i (p08UpperTailIndex i j))
      (x (p08UpperTailIndex i j))

/-- An operational Gaussian-elimination trace with column pivoting in the
paper's terminology: at stage `k`, the largest active entry in column `k` is
moved to the diagonal, the trailing system is updated in working arithmetic,
and the final triangular system is solved by rounded back substitution. -/
structure P08ColumnPivotedGaussianEliminationTrace
    (model : P08ScalarArithmeticModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (rhs output : Fin n → ℝ) where
  matrixState : ℕ → Fin n → Fin n → ℝ
  rhsState : ℕ → Fin n → ℝ
  pivotRow : Fin n → Fin n
  initial_matrix : matrixState 0 = A
  initial_rhs : rhsState 0 = rhs
  pivot_active : ∀ k, k.val ≤ (pivotRow k).val
  pivot_largest : ∀ k i, k.val ≤ i.val →
    |matrixState k.val i k| ≤ |matrixState k.val (pivotRow k) k|
  pivot_nonzero : ∀ k, matrixState k.val (pivotRow k) k ≠ 0
  matrix_step : ∀ k,
    matrixState (k.val + 1) =
      p08ColumnPivotedMatrixStep model (matrixState k.val) k (pivotRow k)
  rhs_step : ∀ k,
    rhsState (k.val + 1) =
      p08ColumnPivotedRhsStep model (matrixState k.val)
        (rhsState k.val) k (pivotRow k)
  final_upper_triangular : ∀ i j, j.val < i.val → matrixState n i j = 0
  final_diagonal_nonzero : ∀ i, matrixState n i i ≠ 0
  back_substitution : ∀ i,
    output i = model.flDiv
      (model.flSub (rhsState n i)
        (p08RoundedUpperTailDot model (matrixState n) output i))
      (matrixState n i i)

/-- The componentwise backward-error certificate supplied by an operational
column-pivoted Gaussian-elimination solve. -/
structure P08ColumnPivotedSolveCertificate {n : ℕ}
    (model : P08ScalarArithmeticModel)
    (A : Fin n → Fin n → ℝ) (rhs : Fin n → ℝ)
    (C1 : Fin n → Fin n → ℝ) (u : ℝ) where
  output : Fin n → ℝ
  execution :
    P08ColumnPivotedGaussianEliminationTrace model A rhs output
  backwardError : Fin n → ℝ
  equation : p08MatVec A output = p08VecAdd rhs backwardError
  backward_error_bound : ∀ i,
    |backwardError i| ≤
      u * p08MatVec C1 (p08AbsAction A output) i

/-- A source-linked execution of section 4's column-pivoted iterative
refinement. Index `m` on `iterate`, `computedResidual`, and `correction`
denotes the paper's `x_m`, `r_m`, and `d_m`. -/
structure P08IterativeRefinementRun (n : ℕ) where
  dimension_pos : 0 < n
  precision : P08ResidualPrecision
  u : ℝ
  u_pos : 0 < u
  dimension_roundoff_small : (n : ℝ) * u ≤ 1 / 100
  workingModel : P08ScalarArithmeticModel
  working_roundoff : workingModel.unitRoundoff = u
  residualModel : P08ScalarArithmeticModel
  residual_roundoff :
    residualModel.unitRoundoff = p08ResidualUnitRoundoff precision u
  convert : ℝ → ℝ
  conversion_model : ∀ x, ∃ delta, |delta| ≤ u ∧
    convert x = x * (1 + delta)
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  inverse_left : p08MatMul Ainv A = p08IdMatrix n
  inverse_right : p08MatMul A Ainv = p08IdMatrix n
  b : Fin n → ℝ
  exactSolution : Fin n → ℝ
  exact_system : p08MatVec A exactSolution = b
  C1 : Fin n → Fin n → ℝ
  C1_nonnegative : p08MatNonnegative C1
  initialSolve : P08ColumnPivotedSolveCertificate workingModel A b C1 u
  iterate : ℕ → Fin n → ℝ
  computedResidual : ℕ → Fin n → ℝ
  correction : ℕ → Fin n → ℝ
  iterate_zero : iterate 0 = fun _ ↦ 0
  iterate_one : iterate 1 = initialSolve.output
  residual_zero : computedResidual 0 = fun i ↦ -b i
  correction_zero : correction 0 = fun i ↦ -iterate 1 i
  residualTrace : ∀ m,
    P08SubtractionLastResidualTrace precision residualModel convert
      A b (iterate (m + 1))
  residual_trace_output : ∀ m,
    computedResidual (m + 1) = (residualTrace m).output
  correctionSolve : ∀ m,
    P08ColumnPivotedSolveCertificate workingModel A (computedResidual m) C1 u
  correction_output : ∀ m, correction m = (correctionSolve m).output
  update_computation : ∀ m i,
    iterate (m + 1) i = workingModel.flSub (iterate m i) (correction m i)

/-- Skeel's exact residual `q_(m+1) = A(x_m-d_m)-b`. The Lean index `m`
is the paper's iteration index, so no artificial `q_0` is introduced. -/
noncomputable def p08ExactResidualAfterCorrection {n : ℕ}
    (run : P08IterativeRefinementRun n) (m : ℕ) : Fin n → ℝ :=
  p08VecSub (p08MatVec run.A
    (p08VecSub (run.iterate m) (run.correction m))) run.b

/-- A basis vector for the paper's normalized absolute-norm convention. -/
def p08BasisVector {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i ↦ if i = j then 1 else 0

/-- The absolute monotone vector norm and its induced matrix norm used in the
paper's nonstandard condition quantity. -/
structure P08AbsoluteMonotoneNorm (n : ℕ) where
  vecNorm : (Fin n → ℝ) → ℝ
  matrixNorm : (Fin n → Fin n → ℝ) → ℝ
  vec_norm_nonnegative : ∀ x, 0 ≤ vecNorm x
  vec_norm_eq_zero : ∀ x, vecNorm x = 0 ↔ x = 0
  vec_norm_add : ∀ x y,
    vecNorm (p08VecAdd x y) ≤ vecNorm x + vecNorm y
  vec_norm_scale : ∀ a x,
    vecNorm (p08VecScale a x) = |a| * vecNorm x
  vec_norm_absolute : ∀ x, vecNorm (p08AbsVec x) = vecNorm x
  vec_norm_monotone : ∀ x y,
    (∀ i, |x i| ≤ |y i|) → vecNorm x ≤ vecNorm y
  basis_normalized : ∀ j, vecNorm (p08BasisVector j) = 1
  matrix_norm_nonnegative : ∀ A, 0 ≤ matrixNorm A
  matrix_action_bound : ∀ A x,
    vecNorm (p08MatVec A x) ≤ matrixNorm A * vecNorm x
  matrix_norm_least : ∀ A c,
    0 ≤ c → (∀ x, vecNorm (p08MatVec A x) ≤ c * vecNorm x) →
      matrixNorm A ≤ c

/-- The paper's nonstandard `kappa(A^{-1}) = || |A| |A^{-1}| ||`. -/
noncomputable def p08KappaInverse {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n) : ℝ :=
  norm.matrixNorm (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))

/-- The scalar `c_3` from the Note following Lemma 4.1. -/
noncomputable def p08Lemma43c3 {n : ℕ}
    (run : P08IterativeRefinementRun n) : ℝ :=
  match run.precision with
  | .single =>
      (1 + run.u) * ((1 + run.u) ^ n - 1) / run.u ^ 2 - n / run.u
  | .double =>
      (1 + run.u) * (1 + run.u ^ 2) *
        ((1 + run.u ^ 2) ^ n - 1) / run.u ^ 2 - n

/-- The scalar `c_4` from the Note following Lemma 4.1. -/
def p08Lemma43c4 {n : ℕ} (run : P08IterativeRefinementRun n) : ℝ :=
  match run.precision with
  | .single => 0
  | .double => 1 + run.u

/-- Uniform envelopes for the anonymous scalar and matrix quantities.  The
functions are fixed across problem data and depend only on the dimension. -/
structure P08DimensionOnlyConstantBounds where
  scalar : ℕ → ℝ
  matrixEntry : ℕ → ℝ
  scalar_nonnegative : ∀ n, 0 ≤ scalar n
  matrixEntry_nonnegative : ∀ n, 0 ≤ matrixEntry n

/-- The source-defined matrices and resolvents used in Lemma 4.3. The exact
equalities mirror the Notes on printed pages 823, 826, and 827. -/
structure P08Lemma43Constants {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (dimensionBounds : P08DimensionOnlyConstantBounds) where
  C2 : Fin n → Fin n → ℝ
  C6 : Fin n → Fin n → ℝ
  C7 : Fin n → Fin n → ℝ
  C8 : Fin n → Fin n → ℝ
  C9 : Fin n → Fin n → ℝ
  C10 : Fin n → Fin n → ℝ
  C11 : Fin n → Fin n → ℝ
  C12 : Fin n → Fin n → ℝ
  c1 : ℝ
  c5 : ℝ
  c8 : ℝ
  C2ResolventInv : Fin n → Fin n → ℝ
  C11ResolventInv : Fin n → Fin n → ℝ
  c1_definition : c1 = norm.matrixNorm run.C1
  c5_definition : c5 =
    n + (p08Lemma43c3 run + p08Lemma43c4 run) * run.u ^ 2 /
      p08ResidualUnitRoundoff run.precision run.u
  C2_resolvent_left :
    p08MatMul
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul run.C1
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))))
      C2ResolventInv = p08IdMatrix n
  C2_resolvent_right :
    p08MatMul C2ResolventInv
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul run.C1
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))) =
      p08IdMatrix n
  C2_definition : C2 = p08MatMul C2ResolventInv run.C1
  C6_definition : C6 =
    p08MatAdd C2
      (p08MatScale
        (1 + c5 * p08ResidualUnitRoundoff run.precision run.u / run.u)
        (p08MatAdd (p08IdMatrix n)
          (p08MatScale run.u
            (p08MatMul C2
              (p08MatMul (p08AbsMatrix run.A)
                (p08AbsMatrix run.Ainv))))))
  C7_definition : C7 =
    p08MatScale
      (n + p08Lemma43c3 run * run.u ^ 2 /
        p08ResidualUnitRoundoff run.precision run.u) C2
  C8_definition : C8 = p08MatScale (1 + run.u) C6
  c8_definition : c8 = norm.matrixNorm C8
  C9_definition : C9 =
    p08MatAdd C6 (p08MatScale (p08Lemma43c3 run) (p08IdMatrix n))
  C10_definition : C10 =
    p08MatAdd
      (p08MatAdd C6
        (p08MatScale
          (n * p08ResidualUnitRoundoff run.precision run.u / run.u +
            p08Lemma43c3 run * run.u)
          (p08IdMatrix n)))
      (p08MatScale (p08ResidualUnitRoundoff run.precision run.u)
        (p08MatMul C7
          (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))
  C11_resolvent_left :
    p08MatMul
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))))
      C11ResolventInv = p08IdMatrix n
  C11_resolvent_right :
    p08MatMul C11ResolventInv
      (p08MatSub (p08IdMatrix n)
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))) =
      p08IdMatrix n
  C11_definition : C11 = p08MatMul C11ResolventInv C9
  C12_definition : C12 =
    p08MatMul C11ResolventInv
      (p08MatAdd (p08MatScale n C8) C7)
  C11_fixed_point : C11 =
    p08MatAdd C9
      (p08MatMul
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))
        C11)
  C12_fixed_point : C12 =
    p08MatAdd (p08MatAdd (p08MatScale n C8) C7)
      (p08MatMul
        (p08MatScale run.u
          (p08MatMul C8
            (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv))))
        C12)
  C2_nonnegative : p08MatNonnegative C2
  C6_nonnegative : p08MatNonnegative C6
  C7_nonnegative : p08MatNonnegative C7
  C8_nonnegative : p08MatNonnegative C8
  C9_nonnegative : p08MatNonnegative C9
  C10_nonnegative : p08MatNonnegative C10
  C11_nonnegative : p08MatNonnegative C11
  C12_nonnegative : p08MatNonnegative C12
  c1_nonnegative : 0 ≤ c1
  c8_nonnegative : 0 ≤ c8
  c1_le_c8 : c1 ≤ c8
  C1_dimension_bound : ∀ i j, run.C1 i j ≤ dimensionBounds.matrixEntry n
  C2_dimension_bound : ∀ i j, C2 i j ≤ dimensionBounds.matrixEntry n
  C6_dimension_bound : ∀ i j, C6 i j ≤ dimensionBounds.matrixEntry n
  C7_dimension_bound : ∀ i j, C7 i j ≤ dimensionBounds.matrixEntry n
  C8_dimension_bound : ∀ i j, C8 i j ≤ dimensionBounds.matrixEntry n
  C9_dimension_bound : ∀ i j, C9 i j ≤ dimensionBounds.matrixEntry n
  C10_dimension_bound : ∀ i j, C10 i j ≤ dimensionBounds.matrixEntry n
  C11_dimension_bound : ∀ i j, C11 i j ≤ dimensionBounds.matrixEntry n
  C12_dimension_bound : ∀ i j, C12 i j ≤ dimensionBounds.matrixEntry n
  c1_dimension_bound : c1 ≤ dimensionBounds.scalar n
  c5_dimension_bound : c5 ≤ dimensionBounds.scalar n
  c8_dimension_bound : c8 ≤ dimensionBounds.scalar n

/-- The propagation matrix `u C_8 |A| |A^{-1}|`. -/
noncomputable def p08Lemma43Propagation {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) :
    Fin n → Fin n → ℝ :=
  p08MatScale run.u
    (p08MatMul constants.C8
      (p08MatMul (p08AbsMatrix run.A) (p08AbsMatrix run.Ainv)))

/-- The first vector `u C_10 |A| |x|` in Lemma 4.3. -/
noncomputable def p08Lemma43InitialVector {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  p08VecScale run.u
    (p08MatVec (p08MatMul constants.C10 (p08AbsMatrix run.A))
      (p08AbsVec run.exactSolution))

/-- The forcing vector in the one-step recurrence displayed in the proof of
Lemma 4.3. -/
noncomputable def p08Lemma43RecurrenceForcing {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  p08VecAdd
    (p08VecScale (n * ubar) (p08MatVec absA absx))
    (p08VecAdd
      (p08VecScale (run.u ^ 2)
        (p08MatVec (p08MatMul constants.C9 absA) absx))
      (p08VecScale (ubar * run.u)
        (p08MatVec
          (p08MatMul
            (p08MatMul constants.C7
              (p08MatMul absA absAinv)) absA) absx)))

/-- The three non-iteration terms in Lemma 4.3, retaining their exact orders
in `u` and the residual precision `ubar`. -/
noncomputable def p08Lemma43StationaryVector {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  let absA := p08AbsMatrix run.A
  let absAinv := p08AbsMatrix run.Ainv
  let absx := p08AbsVec run.exactSolution
  let ubar := p08ResidualUnitRoundoff run.precision run.u
  p08VecAdd
    (p08VecScale (n * ubar) (p08MatVec absA absx))
    (p08VecAdd
      (p08VecScale (run.u ^ 2)
        (p08MatVec (p08MatMul constants.C11 absA) absx))
      (p08VecScale (ubar * run.u)
        (p08MatVec
          (p08MatMul
            (p08MatMul constants.C12
              (p08MatMul absA absAinv)) absA) absx)))

/-- The exact four-term right-hand side of P08 Lemma 4.3. -/
noncomputable def p08Lemma43Bound {n : ℕ}
    {run : P08IterativeRefinementRun n}
    {norm : P08AbsoluteMonotoneNorm n}
    {dimensionBounds : P08DimensionOnlyConstantBounds}
    (constants : P08Lemma43Constants run norm dimensionBounds)
    (m : ℕ) : Fin n → ℝ :=
  p08VecAdd
    (p08MatVec (p08MatPow (p08Lemma43Propagation constants) m)
      (p08Lemma43InitialVector constants))
    (p08Lemma43StationaryVector constants)

/-- Local residual-accumulation and correction-solve errors used in the proofs
of Lemmas 4.1 and 4.2.  This records the two operation-level error relations;
it does not contain either lemma, the Lemma 4.3 recurrence, or its conclusion. -/
structure P08Lemma43RoundoffAnalysis {n : ℕ}
    (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (dimensionBounds : P08DimensionOnlyConstantBounds)
    (constants : P08Lemma43Constants run norm dimensionBounds) where
  residualError : ℕ → Fin n → ℝ
  residual_equation : ∀ m,
    run.computedResidual m =
      p08VecAdd
        (p08VecSub (p08MatVec run.A (run.iterate m)) run.b)
        (residualError m)
  residual_error_bound : ∀ m i,
    |residualError m i| ≤
      (n * p08ResidualUnitRoundoff run.precision run.u +
          p08Lemma43c3 run * run.u ^ 2) *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec run.exactSolution) i +
      constants.c5 * p08ResidualUnitRoundoff run.precision run.u *
        p08MatVec (p08AbsMatrix run.A)
          (p08AbsVec (p08VecSub (run.iterate m) run.exactSolution)) i +
      run.u *
        |p08MatVec run.A
          (p08VecSub (run.iterate m) run.exactSolution) i|
  correction_error_bound :
    constants.c1 * run.u * p08KappaInverse run norm ≤ 1 / 2 →
      ∀ m i,
        |(run.correctionSolve m).backwardError i| ≤
          run.u * p08MatVec
            (p08MatMul constants.C2 (p08AbsMatrix run.A))
            (p08AbsVec
              (p08VecSub (run.iterate m) run.exactSolution)) i +
          run.u * p08MatVec
            (p08MatMul
              (p08MatMul constants.C2 (p08AbsMatrix run.A))
              (p08AbsMatrix run.Ainv))
            (p08AbsVec (residualError m)) i

end HighamBench
```
