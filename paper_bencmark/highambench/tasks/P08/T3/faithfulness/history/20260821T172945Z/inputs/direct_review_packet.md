# Declaration dossier for P08-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p08_t3_lemma_4_3_exact_residual_bound
    {n : ℕ} (run : P08IterativeRefinementRun n)
    (norm : P08AbsoluteMonotoneNorm n)
    (constants : P08Lemma43Constants run norm)
    (prior : P08Lemma43PriorBounds run norm constants)
    (hsmall :
      constants.c8 * run.u * p08KappaInverse run norm ≤ 1 / 2) :
    ∀ m i,
      |p08ExactResidualAfterCorrection run m i| ≤
        p08Lemma43Bound constants m i
```

## Elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P08IterativeRefinementRun n) (norm : HighamBench.P08AbsoluteMonotoneNorm n)
  (constants : HighamBench.P08Lemma43Constants run norm),
  HighamBench.P08Lemma43PriorBounds run norm constants →
    Real.instLE.le (instHMul.hMul (instHMul.hMul constants.c8 run.u) (HighamBench.p08KappaInverse run norm)) (1 / 2) →
      ∀ (m : Nat) (i : Fin n),
        Real.instLE.le (abs (HighamBench.p08ExactResidualAfterCorrection run m i))
          (HighamBench.p08Lemma43Bound constants m i)
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P08IterativeRefinementRun n) (norm : HighamBench.P08AbsoluteMonotoneNorm n)
  (constants : @HighamBench.P08Lemma43Constants n run norm)
  (prior : @HighamBench.P08Lemma43PriorBounds n run norm constants)
  (hsmall :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P08Lemma43Constants.c8 n run norm constants) (@HighamBench.P08IterativeRefinementRun.u n run))
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
    (@HighamBench.p08Lemma43Bound n run norm constants m i)
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

### D002: `HighamBench.P08IterativeRefinementRun`

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

### D003: `HighamBench.P08IterativeRefinementRun.u`

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

### D004: `HighamBench.P08Lemma43Constants`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `c912c51712aa9c6cc9d8c87a9b6194c1d8834a793d3ab6ef4aa9890518f101a7`

Type:

```lean
{n : Nat} → HighamBench.P08IterativeRefinementRun n → HighamBench.P08AbsoluteMonotoneNorm n → Type
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P08IterativeRefinementRun n) → (norm : HighamBench.P08AbsoluteMonotoneNorm n) → Type
```

### D005: `HighamBench.P08Lemma43Constants.c8`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5dd1e06a94a93cc403bce146c7e007c3fffc9ea74d8a1de9e210db98d622b708`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → (self : @HighamBench.P08Lemma43Constants n run norm) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.11
```

### D006: `HighamBench.P08Lemma43PriorBounds`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `3c92834e8150575c8325b4e75451c469293f8ae1edcfd831528768447f193691`

Type:

```lean
{n : Nat} →
  (run : HighamBench.P08IterativeRefinementRun n) →
    (norm : HighamBench.P08AbsoluteMonotoneNorm n) → HighamBench.P08Lemma43Constants run norm → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  (run : HighamBench.P08IterativeRefinementRun n) →
    (norm : HighamBench.P08AbsoluteMonotoneNorm n) → (constants : @HighamBench.P08Lemma43Constants n run norm) → Prop
```

### D007: `HighamBench.p08ExactResidualAfterCorrection`

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

### D008: `HighamBench.p08KappaInverse`

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

### D009: `HighamBench.p08Lemma43Bound`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a5bee951bf713d6c844a60be935194ee54cf43a603565a9a7ffa61517f91c33c`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (constants : @HighamBench.P08Lemma43Constants n run norm) → (m : Nat) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} constants m =>
  HighamBench.p08VecAdd
    (HighamBench.p08MatVec (HighamBench.p08MatPow (HighamBench.p08Lemma43Propagation constants) m)
      (HighamBench.p08Lemma43InitialVector constants))
    (HighamBench.p08Lemma43StationaryVector constants)
```

### D010: `HighamBench.P08AbsoluteMonotoneNorm.matrixNorm`

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

### D011: `HighamBench.P08AbsoluteMonotoneNorm.mk`

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

### D012: `HighamBench.P08IterativeRefinementRun.A`

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

### D013: `HighamBench.P08IterativeRefinementRun.Ainv`

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

### D014: `HighamBench.P08IterativeRefinementRun.b`

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

### D015: `HighamBench.P08IterativeRefinementRun.correction`

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

### D016: `HighamBench.P08IterativeRefinementRun.iterate`

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

### D017: `HighamBench.P08IterativeRefinementRun.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `5fc3658a782ddb9568e29b7a7ab51353c8c3fd40b6229aed73afd6aa1c8aeeb5`

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
                                      (initialSolve : HighamBench.P08ColumnPivotedSolveCertificate A b C1 u) →
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
                                                            HighamBench.P08ColumnPivotedSolveCertificate A
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
                                      (initialSolve : @HighamBench.P08ColumnPivotedSolveCertificate n A b C1 u) →
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
                                                  (@HighamBench.P08ColumnPivotedSolveCertificate.output n A b C1 u
                                                    initialSolve)) →
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
                                                            @HighamBench.P08ColumnPivotedSolveCertificate n A
                                                              (computedResidual m) C1 u) →
                                                        (correction_output :
                                                            ∀ (m : Nat),
                                                              @Eq.{1} (Fin n → Real) (correction m)
                                                                (@HighamBench.P08ColumnPivotedSolveCertificate.output n
                                                                  A (computedResidual m) C1 u (correctionSolve m))) →
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

### D018: `HighamBench.P08Lemma43Constants.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `dddc36709eadfb0b6343373eb876099afe788de917e669739a91b5a520f05a76`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
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
                                      (HighamBench.p08MatScale (HighamBench.p08ResidualUnitRoundoff run.precision run.u)
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
                                                                    HighamBench.P08Lemma43Constants run norm
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
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
                                  (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.Ainv n run)))))))
                        (HighamBench.p08IdMatrix n)) →
                    (C2_definition :
                        @Eq.{1} (Fin n → Fin n → Real) C2
                          (@HighamBench.p08MatMul n C2ResolventInv (@HighamBench.P08IterativeRefinementRun.C1 n run))) →
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
                                            (@HighamBench.p08MatScale n (@HighamBench.P08IterativeRefinementRun.u n run)
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
                                                                    @HighamBench.P08Lemma43Constants n run norm
```

### D019: `HighamBench.P08Lemma43PriorBounds.mk`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `6c1c605f89d4b18be199e86b750500fb95395f9bc123da5531d3ffabd1ada0ca`

Type:

```lean
∀ {n : Nat} {run : HighamBench.P08IterativeRefinementRun n} {norm : HighamBench.P08AbsoluteMonotoneNorm n}
  {constants : HighamBench.P08Lemma43Constants run norm},
  (Real.instLE.le (instHMul.hMul (instHMul.hMul constants.c1 run.u) (HighamBench.p08KappaInverse run norm)) (1 / 2) →
      ∀ (m : Nat) (i : Fin n),
        Real.instLE.le (abs (HighamBench.p08ExactResidualAfterCorrection run m i))
          (instHAdd.hAdd
            (instHAdd.hAdd
              (instHMul.hMul run.u
                (HighamBench.p08MatVec (HighamBench.p08MatMul constants.C6 (HighamBench.p08AbsMatrix run.A))
                  (HighamBench.p08AbsVec (HighamBench.p08VecSub (run.iterate m) run.exactSolution)) i))
              (instHMul.hMul
                (instHAdd.hAdd (instHMul.hMul n.cast (HighamBench.p08ResidualUnitRoundoff run.precision run.u))
                  (instHMul.hMul (HighamBench.p08Lemma43c3 run) (instHPow.hPow run.u 2)))
                (HighamBench.p08MatVec (HighamBench.p08AbsMatrix run.A) (HighamBench.p08AbsVec run.exactSolution) i)))
            (instHMul.hMul (instHMul.hMul (HighamBench.p08ResidualUnitRoundoff run.precision run.u) run.u)
              (HighamBench.p08MatVec
                (HighamBench.p08MatMul
                  (HighamBench.p08MatMul constants.C7
                    (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A) (HighamBench.p08AbsMatrix run.Ainv)))
                  (HighamBench.p08AbsMatrix run.A))
                (HighamBench.p08AbsVec run.exactSolution) i)))) →
    (∀ (m : Nat) (i : Fin n),
        Real.instLE.le (abs (instHSub.hSub (run.iterate (instHAdd.hAdd m 1) i) (run.exactSolution i)))
          (instHAdd.hAdd
            (instHMul.hMul (instHAdd.hAdd 1 run.u)
              (HighamBench.p08AbsAction run.Ainv (HighamBench.p08ExactResidualAfterCorrection run m) i))
            (instHMul.hMul run.u (abs (run.exactSolution i))))) →
      HighamBench.P08Lemma43PriorBounds run norm constants
```

Fully explicit type:

```lean
∀ {n : Nat} {run : HighamBench.P08IterativeRefinementRun n} {norm : HighamBench.P08AbsoluteMonotoneNorm n}
  {constants : @HighamBench.P08Lemma43Constants n run norm}
  (lemma41 :
    @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.P08Lemma43Constants.c1 n run norm constants) (@HighamBench.P08IterativeRefinementRun.u n run))
          (@HighamBench.p08KappaInverse n run norm))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
      ∀ (m : Nat) (i : Fin n),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p08ExactResidualAfterCorrection n run m i))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P08IterativeRefinementRun.u n run)
                (@HighamBench.p08MatVec n
                  (@HighamBench.p08MatMul n (@HighamBench.P08Lemma43Constants.C6 n run norm constants)
                    (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run)))
                  (@HighamBench.p08AbsVec n
                    (@HighamBench.p08VecSub n (@HighamBench.P08IterativeRefinementRun.iterate n run m)
                      (@HighamBench.P08IterativeRefinementRun.exactSolution n run)))
                  i))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast n)
                    (HighamBench.p08ResidualUnitRoundoff (@HighamBench.P08IterativeRefinementRun.precision n run)
                      (@HighamBench.P08IterativeRefinementRun.u n run)))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HighamBench.p08Lemma43c3 n run)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@HighamBench.P08IterativeRefinementRun.u n run)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@HighamBench.p08MatVec n (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                  (@HighamBench.p08AbsVec n (@HighamBench.P08IterativeRefinementRun.exactSolution n run)) i)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (HighamBench.p08ResidualUnitRoundoff (@HighamBench.P08IterativeRefinementRun.precision n run)
                  (@HighamBench.P08IterativeRefinementRun.u n run))
                (@HighamBench.P08IterativeRefinementRun.u n run))
              (@HighamBench.p08MatVec n
                (@HighamBench.p08MatMul n
                  (@HighamBench.p08MatMul n (@HighamBench.P08Lemma43Constants.C7 n run norm constants)
                    (@HighamBench.p08MatMul n
                      (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run))
                      (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.Ainv n run))))
                  (@HighamBench.p08AbsMatrix n (@HighamBench.P08IterativeRefinementRun.A n run)))
                (@HighamBench.p08AbsVec n (@HighamBench.P08IterativeRefinementRun.exactSolution n run)) i))))
  (lemma42_forward :
    ∀ (m : Nat) (i : Fin n),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HighamBench.P08IterativeRefinementRun.iterate n run
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              i)
            (@HighamBench.P08IterativeRefinementRun.exactSolution n run i)))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HighamBench.P08IterativeRefinementRun.u n run))
            (@HighamBench.p08AbsAction n (@HighamBench.P08IterativeRefinementRun.Ainv n run)
              (@HighamBench.p08ExactResidualAfterCorrection n run m) i))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.P08IterativeRefinementRun.u n run)
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HighamBench.P08IterativeRefinementRun.exactSolution n run i))))),
  @HighamBench.P08Lemma43PriorBounds n run norm constants
```

### D020: `HighamBench.p08AbsMatrix`

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

### D021: `HighamBench.p08Lemma43InitialVector`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9ec709d17d95d069fcc12a3102ce1ee312df3df528a79e9507ec604a2905bead`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (constants : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} constants =>
  HighamBench.p08VecScale run.u
    (HighamBench.p08MatVec (HighamBench.p08MatMul constants.C10 (HighamBench.p08AbsMatrix run.A))
      (HighamBench.p08AbsVec run.exactSolution))
```

### D022: `HighamBench.p08Lemma43Propagation`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `10367d516e13eb84ddf10ad3fd37995263de896d257fbf64bea1a690180219a2`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (constants : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} constants =>
  HighamBench.p08MatScale run.u
    (HighamBench.p08MatMul constants.C8
      (HighamBench.p08MatMul (HighamBench.p08AbsMatrix run.A) (HighamBench.p08AbsMatrix run.Ainv)))
```

### D023: `HighamBench.p08Lemma43StationaryVector`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2ae95b9dcd4166e4c23eaf6b5e6b5d26f90f1682c3e0a70a82d4213e1a520ea1`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (constants : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {run} {norm} constants =>
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

### D024: `HighamBench.p08MatMul`

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

### D025: `HighamBench.p08MatPow`

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

### D026: `HighamBench.p08MatVec`

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

### D027: `HighamBench.p08VecAdd`

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

### D028: `HighamBench.p08VecSub`

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

### D029: `HighamBench.P08ColumnPivotedSolveCertificate`

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

### D030: `HighamBench.P08ColumnPivotedSolveCertificate.output`

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

### D031: `HighamBench.P08IterativeRefinementRun.C1`

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

### D032: `HighamBench.P08IterativeRefinementRun.exactSolution`

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

### D033: `HighamBench.P08IterativeRefinementRun.precision`

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

### D034: `HighamBench.P08Lemma43Constants.C10`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3f89230489efa2acd4b87eef9416f6823b5ad4aaaa9833968c8ec9c226b61de4`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (self : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.6
```

### D035: `HighamBench.P08Lemma43Constants.C11`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b488c8fc7a2055f6c645f84b731807126e6dcf8d76e9b4037de1c02fc5ce2fd7`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (self : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.7
```

### D036: `HighamBench.P08Lemma43Constants.C12`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `046bb31ccf0eec67c502aa1c75b21aa05264d263a7fde0c47f4f26dcdaa176a9`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (self : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.8
```

### D037: `HighamBench.P08Lemma43Constants.C6`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ca15d893794305e77e09c02277a8c451656dfb9e0446207dcbcf65183257d813`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (self : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.2
```

### D038: `HighamBench.P08Lemma43Constants.C7`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `433d8137960836976369880de134edcb0fca599a99306d918ffb293ebcc53dbb`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (self : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.3
```

### D039: `HighamBench.P08Lemma43Constants.C8`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `74f9157d15d939e8df3b310c18b63c26faf46fb4389b85a593a3f0c8881fe268`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} →
      (self : @HighamBench.P08Lemma43Constants n run norm) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.4
```

### D040: `HighamBench.P08Lemma43Constants.c1`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `21c9b73f75387b205c7c6fca385f7080561a919097ef680780383b275c19342b`

Type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → HighamBench.P08Lemma43Constants run norm → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {run : HighamBench.P08IterativeRefinementRun n} →
    {norm : HighamBench.P08AbsoluteMonotoneNorm n} → (self : @HighamBench.P08Lemma43Constants n run norm) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n run norm self => self.9
```

### D041: `HighamBench.P08ResidualPrecision`

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

### D042: `HighamBench.P08ScalarArithmeticModel`

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

### D043: `HighamBench.P08ScalarArithmeticModel.flSub`

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

### D044: `HighamBench.P08ScalarArithmeticModel.unitRoundoff`

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

### D045: `HighamBench.P08SubtractionLastResidualTrace`

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

### D046: `HighamBench.P08SubtractionLastResidualTrace.output`

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

### D047: `HighamBench.p08AbsAction`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D048: `HighamBench.p08AbsVec`

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

### D049: `HighamBench.p08BasisVector`

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

### D050: `HighamBench.p08IdMatrix`

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

### D051: `HighamBench.p08Lemma43c3`

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

### D052: `HighamBench.p08Lemma43c4`

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

### D053: `HighamBench.p08MatAdd`

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

### D054: `HighamBench.p08MatNonnegative`

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

### D055: `HighamBench.p08MatPow.match_1`

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

### D056: `HighamBench.p08MatScale`

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

### D057: `HighamBench.p08MatSub`

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

### D058: `HighamBench.p08ResidualUnitRoundoff`

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

### D059: `HighamBench.p08VecScale`

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

### D060: `HighamBench.P08ColumnPivotedSolveCertificate.mk`

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

### D061: `HighamBench.P08ResidualPrecision.double`

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

### D062: `HighamBench.P08ResidualPrecision.single`

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

### D063: `HighamBench.P08ScalarArithmeticModel.mk`

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

### D064: `HighamBench.P08SubtractionLastResidualTrace.mk`

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

### D065: `HighamBench.p08ResidualUnitRoundoff.match_1`

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

### D066: `HighamBench.P08ResidualPrecision.casesOn`

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

### D067: `HighamBench.p08RoundedDot`

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

### D068: `HighamBench.P08ResidualPrecision.rec`

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

### D069: `HighamBench.P08ScalarArithmeticModel.flAdd`

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

### D070: `HighamBench.P08ScalarArithmeticModel.flMul`

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

### D071: `HighamBench.recursiveSum`

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

### D072: `HighamBench.recursiveSum._proof_1`

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

### D073: `HighamBench.recursiveSum.match_1`

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

### D074: `DivInvMonoid.toDiv`

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

### D075: `Fin`

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

### D076: `HDiv.hDiv`

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

### D077: `HMul.hMul`

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

### D078: `LE.le`

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

### D079: `Nat`

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

### D080: `Nat.instAtLeastTwoHAddOfNat`

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

### D081: `Nat.instNeZeroSucc`

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

### D082: `OfNat.ofNat`

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

### D083: `One.toOfNat1`

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

### D084: `Real`

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

### D085: `Real.instAddGroup`

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

### D086: `Real.instDivInvMonoid`

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

### D087: `Real.instLE`

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

### D088: `Real.instMul`

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

### D089: `Real.instNatCast`

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

### D090: `Real.instOne`

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

### D091: `Real.lattice`

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

### D092: `abs`

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

### D093: `instHDiv`

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

### D094: `instHMul`

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

### D095: `instOfNatAtLeastTwo`

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

### D096: `instOfNatNat`

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

### D097: `And`

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

### D098: `Eq`

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

### D099: `Exists`

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

### D100: `Fin.fintype`

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

### D101: `Finset.sum`

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

### D102: `Finset.univ`

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

### D103: `HAdd.hAdd`

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

### D104: `HPow.hPow`

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

### D105: `HSub.hSub`

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

### D106: `Iff`

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

### D107: `LT.lt`

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

### D108: `Monoid.toNatPow`

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

### D109: `Nat.below`

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

### D110: `Nat.brecOn`

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

### D111: `Nat.cast`

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

### D112: `Nat.succ`

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

### D113: `Neg.neg`

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

### D114: `Pi.instZero`

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

### D115: `Real.instAdd`

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

### D116: `Real.instAddCommMonoid`

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

### D117: `Real.instLT`

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

### D118: `Real.instMonoid`

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

### D119: `Real.instNeg`

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

### D120: `Real.instSub`

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

### D121: `Real.instZero`

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

### D122: `Unit`

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

### D123: `Zero.toOfNat0`

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

### D124: `instAddNat`

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

### D125: `instHAdd`

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

### D126: `instHPow`

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

### D127: `instHSub`

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

### D128: `instLTNat`

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

### D129: `Nat.casesOn`

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

### D130: `Unit.unit`

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

### D131: `instDecidableEqFin`

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

### D132: `ite`

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

### D133: `Ne`

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

### D134: `Fin.castSucc`

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

### D135: `Fin.last`

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

### D136: `Fin.mk`

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

### D137: `Not`

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

### D138: `dite`

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

### D139: `instDecidableEqNat`

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

### D140: `Nat.zero`

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
