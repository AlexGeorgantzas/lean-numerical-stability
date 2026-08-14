# Declaration dossier for P07-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p07_t1_perturbed_preconditioned_map_injective
    {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel)
    (run : P07Lemma32ForwardRun pre model)
    (exactData : P07MatrixPseudoinverseSpectralData
      (p07ExactPreconditionedMatrix pre))
    (errorSpectrum : P07RectSpectralExtrema run.DeltaY)
    (computedData : P07MatrixPseudoinverseSpectralData
      run.forwardSubstitution.output)
    (hsmall : p07Lemma32Epsilon exactData errorSpectrum < 1) :
    Function.Injective (p07MatVec run.forwardSubstitution.output) ∧
      p07ConditionNumber2 computedData ≤
        (p07ConditionNumber2 exactData +
            p07Lemma32Epsilon exactData errorSpectrum) /
          (1 - p07Lemma32Epsilon exactData errorSpectrum)
```

## Elaborated target type

```lean
∀ {m s n : Nat} (pre : HighamBench.P07Lemma31ComputedPreconditioner m s n)
  (model : HighamBench.P07ScalarArithmeticModel) (run : HighamBench.P07Lemma32ForwardRun pre model)
  (exactData : HighamBench.P07MatrixPseudoinverseSpectralData (HighamBench.p07ExactPreconditionedMatrix pre))
  (errorSpectrum : HighamBench.P07RectSpectralExtrema run.DeltaY)
  (computedData : HighamBench.P07MatrixPseudoinverseSpectralData run.forwardSubstitution.output),
  Real.instLT.lt (HighamBench.p07Lemma32Epsilon exactData errorSpectrum) 1 →
    And (Function.Injective (HighamBench.p07MatVec run.forwardSubstitution.output))
      (Real.instLE.le (HighamBench.p07ConditionNumber2 computedData)
        (instHDiv.hDiv
          (instHAdd.hAdd (HighamBench.p07ConditionNumber2 exactData)
            (HighamBench.p07Lemma32Epsilon exactData errorSpectrum))
          (instHSub.hSub 1 (HighamBench.p07Lemma32Epsilon exactData errorSpectrum))))
```

## Fully explicit elaborated target type

```lean
∀ {m s n : Nat} (pre : HighamBench.P07Lemma31ComputedPreconditioner m s n)
  (model : HighamBench.P07ScalarArithmeticModel) (run : @HighamBench.P07Lemma32ForwardRun m s n pre model)
  (exactData :
    @HighamBench.P07MatrixPseudoinverseSpectralData m n (@HighamBench.p07ExactPreconditionedMatrix m s n pre))
  (errorSpectrum :
    @HighamBench.P07RectSpectralExtrema m n (@HighamBench.P07Lemma32ForwardRun.DeltaY m s n pre model run))
  (computedData :
    @HighamBench.P07MatrixPseudoinverseSpectralData m n
      (@HighamBench.P07ForwardSubstitutionTrace.output model m n
        (@HighamBench.P07Lemma31ComputedPreconditioner.A m s n pre)
        (@HighamBench.P07Lemma31ComputedPreconditioner.RHat m s n pre)
        (@HighamBench.P07Lemma32ForwardRun.forwardSubstitution m s n pre model run)))
  (hsmall :
    @LT.lt.{0} Real Real.instLT
      (@HighamBench.p07Lemma32Epsilon m n (@HighamBench.p07ExactPreconditionedMatrix m s n pre) exactData
        (@HighamBench.P07Lemma32ForwardRun.DeltaY m s n pre model run) errorSpectrum)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  And
    (@Function.Injective.{1, 1} (Fin n → Real) (Fin m → Real)
      (@HighamBench.p07MatVec m n
        (@HighamBench.P07ForwardSubstitutionTrace.output model m n
          (@HighamBench.P07Lemma31ComputedPreconditioner.A m s n pre)
          (@HighamBench.P07Lemma31ComputedPreconditioner.RHat m s n pre)
          (@HighamBench.P07Lemma32ForwardRun.forwardSubstitution m s n pre model run))))
    (@LE.le.{0} Real Real.instLE
      (@HighamBench.p07ConditionNumber2 m n
        (@HighamBench.P07ForwardSubstitutionTrace.output model m n
          (@HighamBench.P07Lemma31ComputedPreconditioner.A m s n pre)
          (@HighamBench.P07Lemma31ComputedPreconditioner.RHat m s n pre)
          (@HighamBench.P07Lemma32ForwardRun.forwardSubstitution m s n pre model run))
        computedData)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HighamBench.p07ConditionNumber2 m n (@HighamBench.p07ExactPreconditionedMatrix m s n pre) exactData)
          (@HighamBench.p07Lemma32Epsilon m n (@HighamBench.p07ExactPreconditionedMatrix m s n pre) exactData
            (@HighamBench.P07Lemma32ForwardRun.DeltaY m s n pre model run) errorSpectrum))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HighamBench.p07Lemma32Epsilon m n (@HighamBench.p07ExactPreconditionedMatrix m s n pre) exactData
            (@HighamBench.P07Lemma32ForwardRun.DeltaY m s n pre model run) errorSpectrum))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P07Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P07Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P07ForwardSubstitutionTrace.output`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9f8ff7a3a8b2f273a1e36787f260a90bb8f908d142d0eb8c6eb1dbdb85a54bfa`

Type:

```lean
{model : HighamBench.P07ScalarArithmeticModel} →
  {m n : Nat} →
    {A : Fin m → Fin n → Real} →
      {R : Fin n → Fin n → Real} → HighamBench.P07ForwardSubstitutionTrace model A R → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{model : HighamBench.P07ScalarArithmeticModel} →
  {m n : Nat} →
    {A : Fin m → Fin n → Real} →
      {R : Fin n → Fin n → Real} →
        (self : @HighamBench.P07ForwardSubstitutionTrace model m n A R) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun model m n A R self => self.1
```

### D002: `HighamBench.P07Lemma31ComputedPreconditioner`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9b2d81eb14eb90dc85405116b31aa86d601af39dfeb8973a4179d2144a44c428`

Type:

```lean
Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(m s n : Nat) → Type
```

### D003: `HighamBench.P07Lemma31ComputedPreconditioner.A`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5ff42ae1ca7ac214f16916c67c98185bcbb1e3f81cf71d085f819f267b70d532`

Type:

```lean
{m s n : Nat} → HighamBench.P07Lemma31ComputedPreconditioner m s n → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m s n : Nat} → (self : HighamBench.P07Lemma31ComputedPreconditioner m s n) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m s n self => self.4
```

### D004: `HighamBench.P07Lemma31ComputedPreconditioner.RHat`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `20788d1a984d6e4c5be19ab500ad0520ce3ff8cb77eb52b3307291873194a727`

Type:

```lean
{m s n : Nat} → HighamBench.P07Lemma31ComputedPreconditioner m s n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{m s n : Nat} → (self : HighamBench.P07Lemma31ComputedPreconditioner m s n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m s n self => self.10
```

### D005: `HighamBench.P07Lemma32ForwardRun`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a967bfdbc3ce551e4cf0a4aa6452bc9e34bdc08c759894fce0b6ddaaa80d6f44`

Type:

```lean
{m s n : Nat} → HighamBench.P07Lemma31ComputedPreconditioner m s n → HighamBench.P07ScalarArithmeticModel → Type
```

Fully explicit type:

```lean
{m s n : Nat} →
  (pre : HighamBench.P07Lemma31ComputedPreconditioner m s n) → (model : HighamBench.P07ScalarArithmeticModel) → Type
```

### D006: `HighamBench.P07Lemma32ForwardRun.DeltaY`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c03c5728039e29976868b67858128c93adbd8f433c3d9de5084937125d9dc39b`

Type:

```lean
{m s n : Nat} →
  {pre : HighamBench.P07Lemma31ComputedPreconditioner m s n} →
    {model : HighamBench.P07ScalarArithmeticModel} → HighamBench.P07Lemma32ForwardRun pre model → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m s n : Nat} →
  {pre : HighamBench.P07Lemma31ComputedPreconditioner m s n} →
    {model : HighamBench.P07ScalarArithmeticModel} →
      (self : @HighamBench.P07Lemma32ForwardRun m s n pre model) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m s n pre model self => self.2
```

### D007: `HighamBench.P07Lemma32ForwardRun.forwardSubstitution`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d589e7437203d1f017710b5268d24585b0f3698b39cb221cb0d91fd0df675a40`

Type:

```lean
{m s n : Nat} →
  {pre : HighamBench.P07Lemma31ComputedPreconditioner m s n} →
    {model : HighamBench.P07ScalarArithmeticModel} →
      HighamBench.P07Lemma32ForwardRun pre model → HighamBench.P07ForwardSubstitutionTrace model pre.A pre.RHat
```

Fully explicit type:

```lean
{m s n : Nat} →
  {pre : HighamBench.P07Lemma31ComputedPreconditioner m s n} →
    {model : HighamBench.P07ScalarArithmeticModel} →
      (self : @HighamBench.P07Lemma32ForwardRun m s n pre model) →
        @HighamBench.P07ForwardSubstitutionTrace model m n (@HighamBench.P07Lemma31ComputedPreconditioner.A m s n pre)
          (@HighamBench.P07Lemma31ComputedPreconditioner.RHat m s n pre)
```

Definition body (one-level semantic boundary):

```lean
fun m s n pre model self => self.1
```

### D008: `HighamBench.P07MatrixPseudoinverseSpectralData`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `3e7effbed3798043870382b1ba1f5ff0e9bd923e8fc0afefe780960d3f54f8e0`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Type
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → Type
```

### D009: `HighamBench.P07RectSpectralExtrema`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f28e14c963dda89549d25c991075533210d2267c1374bb6e77cad2d6032d7949`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Type
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → Type
```

### D010: `HighamBench.P07ScalarArithmeticModel`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b08dbe20bb893e2bafe8131d814ad8fe3bcad7ba7268db7e4358a7231b7b6f65`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D011: `HighamBench.p07ConditionNumber2`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c3d104c126f046412efdd715b396c98961a2bc60d1c4d00cd9abc3c449d3c5e4`

Type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → HighamBench.P07MatrixPseudoinverseSpectralData A → Real
```

Fully explicit type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → (data : @HighamBench.P07MatrixPseudoinverseSpectralData m n A) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} {A} data => instHMul.hMul data.matrixSpectrum.upper data.pseudoinverseSpectrum.upper
```

### D012: `HighamBench.p07ExactPreconditionedMatrix`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e7009fd59a8739265c1f2fce6fcb55416e15c271a997d8164c61ee0313386716`

Type:

```lean
{m s n : Nat} → HighamBench.P07Lemma31ComputedPreconditioner m s n → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m s n : Nat} → (pre : HighamBench.P07Lemma31ComputedPreconditioner m s n) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m s n} pre => HighamBench.p07RectMatMul pre.A pre.RHatInv
```

### D013: `HighamBench.p07Lemma32Epsilon`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b7beba037dcbc5c0b5394c249ff08f8300987ea31293d4a7fd5edfaa6c965c4c`

Type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    HighamBench.P07MatrixPseudoinverseSpectralData A →
      {DeltaY : Fin m → Fin n → Real} → HighamBench.P07RectSpectralExtrema DeltaY → Real
```

Fully explicit type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (exactData : @HighamBench.P07MatrixPseudoinverseSpectralData m n A) →
      {DeltaY : Fin m → Fin n → Real} → (errorSpectrum : @HighamBench.P07RectSpectralExtrema m n DeltaY) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} {A} exactData {DeltaY} errorSpectrum =>
  instHMul.hMul errorSpectrum.upper exactData.pseudoinverseSpectrum.upper
```

### D014: `HighamBench.p07MatVec`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c20ee94e8dfa7a21c0972744b89ff2650d7462ecb441662c2e1930d980ab8dc5`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Real) → Fin m → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (x : Fin n → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D015: `HighamBench.P07ForwardSubstitutionTrace`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e94358d44154cccc068549aa9aeff2ab29f66be68f38abdc954963745e662d78`

Type:

```lean
HighamBench.P07ScalarArithmeticModel → {m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Type
```

Fully explicit type:

```lean
(model : HighamBench.P07ScalarArithmeticModel) →
  {m n : Nat} → (A : Fin m → Fin n → Real) → (R : Fin n → Fin n → Real) → Type
```

### D016: `HighamBench.P07Lemma31ComputedPreconditioner.RHatInv`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e6acf6a2c04876133acc77e37bc7623a3764f598e04ea441da0d132bed2f97c6`

Type:

```lean
{m s n : Nat} → HighamBench.P07Lemma31ComputedPreconditioner m s n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{m s n : Nat} → (self : HighamBench.P07Lemma31ComputedPreconditioner m s n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m s n self => self.11
```

### D017: `HighamBench.P07Lemma31ComputedPreconditioner.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `13f09f3e9508d5bfbdf5a81b4f90bce88819f959f66f217e7bc5cbbb90b40902`

Type:

```lean
{m s n : Nat} →
  instLTNat.lt 0 n →
    instLTNat.lt n s →
      instLTNat.lt s m →
        (A : Fin m → Fin n → Real) →
          (S : Fin s → Fin m → Real) →
            (computedSketch sketchError qrError Qtilde : Fin s → Fin n → Real) →
              (RHat RHatInv : Fin n → Fin n → Real) →
                Function.Injective (HighamBench.p07MatVec A) →
                  Function.Injective (HighamBench.p07MatVec (HighamBench.p07RectMatMul S A)) →
                    Eq computedSketch (HighamBench.p07RectAdd (HighamBench.p07RectMatMul S A) sketchError) →
                      Eq (HighamBench.p07RectMatMul Qtilde RHat) (HighamBench.p07RectAdd computedSketch qrError) →
                        HighamBench.p07Isometry Qtilde →
                          HighamBench.p07UpperTriangular RHat →
                            Eq (HighamBench.p07RectMatMul RHat RHatInv) HighamBench.p07FiniteId →
                              Eq (HighamBench.p07RectMatMul RHatInv RHat) HighamBench.p07FiniteId →
                                HighamBench.P07Lemma31ComputedPreconditioner m s n
```

Fully explicit type:

```lean
{m s n : Nat} →
  (columns_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (sketch_gt_columns : @LT.lt.{0} Nat instLTNat n s) →
      (rows_gt_sketch : @LT.lt.{0} Nat instLTNat s m) →
        (A : Fin m → Fin n → Real) →
          (S : Fin s → Fin m → Real) →
            (computedSketch sketchError qrError Qtilde : Fin s → Fin n → Real) →
              (RHat RHatInv : Fin n → Fin n → Real) →
                (A_full_column_rank :
                    @Function.Injective.{1, 1} (Fin n → Real) (Fin m → Real) (@HighamBench.p07MatVec m n A)) →
                  (sketch_full_column_rank :
                      @Function.Injective.{1, 1} (Fin n → Real) (Fin s → Real)
                        (@HighamBench.p07MatVec s n (@HighamBench.p07RectMatMul s m n S A))) →
                    (sketch_multiplication :
                        @Eq.{1} (Fin s → Fin n → Real) computedSketch
                          (@HighamBench.p07RectAdd s n (@HighamBench.p07RectMatMul s m n S A) sketchError)) →
                      (computed_householder_qr :
                          @Eq.{1} (Fin s → Fin n → Real) (@HighamBench.p07RectMatMul s n n Qtilde RHat)
                            (@HighamBench.p07RectAdd s n computedSketch qrError)) →
                        (qtilde_isometry : @HighamBench.p07Isometry s n Qtilde) →
                          (rhat_upper_triangular : @HighamBench.p07UpperTriangular n RHat) →
                            (rhat_inverse_left :
                                @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p07RectMatMul n n n RHat RHatInv)
                                  (@HighamBench.p07FiniteId n)) →
                              (rhat_inverse_right :
                                  @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p07RectMatMul n n n RHatInv RHat)
                                    (@HighamBench.p07FiniteId n)) →
                                HighamBench.P07Lemma31ComputedPreconditioner m s n
```

### D018: `HighamBench.P07Lemma32ForwardRun.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `605aa143920d16447cf7f5ccc9c8e95474f23b22f24b56a784242c22f4cdd50f`

Type:

```lean
{m s n : Nat} →
  {pre : HighamBench.P07Lemma31ComputedPreconditioner m s n} →
    {model : HighamBench.P07ScalarArithmeticModel} →
      (forwardSubstitution : HighamBench.P07ForwardSubstitutionTrace model pre.A pre.RHat) →
        (DeltaY : Fin m → Fin n → Real) →
          Eq DeltaY (HighamBench.p07RectSub forwardSubstitution.output (HighamBench.p07ExactPreconditionedMatrix pre)) →
            HighamBench.P07Lemma32ForwardRun pre model
```

Fully explicit type:

```lean
{m s n : Nat} →
  {pre : HighamBench.P07Lemma31ComputedPreconditioner m s n} →
    {model : HighamBench.P07ScalarArithmeticModel} →
      (forwardSubstitution :
          @HighamBench.P07ForwardSubstitutionTrace model m n (@HighamBench.P07Lemma31ComputedPreconditioner.A m s n pre)
            (@HighamBench.P07Lemma31ComputedPreconditioner.RHat m s n pre)) →
        (DeltaY : Fin m → Fin n → Real) →
          (deltaY_definition :
              @Eq.{1} (Fin m → Fin n → Real) DeltaY
                (@HighamBench.p07RectSub m n
                  (@HighamBench.P07ForwardSubstitutionTrace.output model m n
                    (@HighamBench.P07Lemma31ComputedPreconditioner.A m s n pre)
                    (@HighamBench.P07Lemma31ComputedPreconditioner.RHat m s n pre) forwardSubstitution)
                  (@HighamBench.p07ExactPreconditionedMatrix m s n pre))) →
            @HighamBench.P07Lemma32ForwardRun m s n pre model
```

### D019: `HighamBench.P07MatrixPseudoinverseSpectralData.matrixSpectrum`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a1e93f69403ca1261f9b94a74e7dc192547afebc55decdc706473c578d149f34`

Type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} → HighamBench.P07MatrixPseudoinverseSpectralData A → HighamBench.P07RectSpectralExtrema A
```

Fully explicit type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (self : @HighamBench.P07MatrixPseudoinverseSpectralData m n A) → @HighamBench.P07RectSpectralExtrema m n A
```

Definition body (one-level semantic boundary):

```lean
fun m n A self => self.1
```

### D020: `HighamBench.P07MatrixPseudoinverseSpectralData.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `d02c4d12ad13332a7123eac323b8d215ee33e64926484aeb2eeace0ac1a7d422`

Type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (matrixSpectrum : HighamBench.P07RectSpectralExtrema A) →
      (pseudoinverse : Fin n → Fin m → Real) →
        HighamBench.P07MoorePenrosePseudoinverse A pseudoinverse →
          (pseudoinverseSpectrum : HighamBench.P07RectSpectralExtrema pseudoinverse) →
            (Ne matrixSpectrum.lower 0 → Eq pseudoinverseSpectrum.upper (Real.instInv.inv matrixSpectrum.lower)) →
              HighamBench.P07MatrixPseudoinverseSpectralData A
```

Fully explicit type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (matrixSpectrum : @HighamBench.P07RectSpectralExtrema m n A) →
      (pseudoinverse : Fin n → Fin m → Real) →
        (pseudoinverse_penrose : @HighamBench.P07MoorePenrosePseudoinverse m n A pseudoinverse) →
          (pseudoinverseSpectrum : @HighamBench.P07RectSpectralExtrema n m pseudoinverse) →
            (pseudoinverse_norm_eq_reciprocal :
                @Ne.{1} Real (@HighamBench.P07RectSpectralExtrema.lower m n A matrixSpectrum)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @Eq.{1} Real (@HighamBench.P07RectSpectralExtrema.upper n m pseudoinverse pseudoinverseSpectrum)
                    (@Inv.inv.{0} Real Real.instInv (@HighamBench.P07RectSpectralExtrema.lower m n A matrixSpectrum))) →
              @HighamBench.P07MatrixPseudoinverseSpectralData m n A
```

### D021: `HighamBench.P07MatrixPseudoinverseSpectralData.pseudoinverse`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `225e3c62a7033d5885521474c9a3adfba749e48411be812573d7328ecb35d7ac`

Type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → HighamBench.P07MatrixPseudoinverseSpectralData A → Fin n → Fin m → Real
```

Fully explicit type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} → (self : @HighamBench.P07MatrixPseudoinverseSpectralData m n A) → Fin n → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n A self => self.2
```

### D022: `HighamBench.P07MatrixPseudoinverseSpectralData.pseudoinverseSpectrum`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6be5cb01920966192c414c5927d52035c740f5622e34fb56d251ed2caa151e76`

Type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (self : HighamBench.P07MatrixPseudoinverseSpectralData A) → HighamBench.P07RectSpectralExtrema self.pseudoinverse
```

Fully explicit type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (self : @HighamBench.P07MatrixPseudoinverseSpectralData m n A) →
      @HighamBench.P07RectSpectralExtrema n m (@HighamBench.P07MatrixPseudoinverseSpectralData.pseudoinverse m n A self)
```

Definition body (one-level semantic boundary):

```lean
fun m n A self => self.4
```

### D023: `HighamBench.P07RectSpectralExtrema.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `d54c6d625ba192d59f64e230475073cb01e13e39d694ea1964a3b853a4835ccc`

Type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (upper lower : Real) →
      Real.instLE.le 0 upper →
        Real.instLE.le 0 lower →
          HighamBench.p07RectOpNorm2Le A upper →
            HighamBench.p07RectLowerBound A lower →
              (Exists fun x =>
                  And (Eq (HighamBench.p07VecNorm2 x) 1)
                    (Eq (HighamBench.p07VecNorm2 (HighamBench.p07MatVec A x)) upper)) →
                (Exists fun x =>
                    And (Eq (HighamBench.p07VecNorm2 x) 1)
                      (Eq (HighamBench.p07VecNorm2 (HighamBench.p07MatVec A x)) lower)) →
                  HighamBench.P07RectSpectralExtrema A
```

Fully explicit type:

```lean
{m n : Nat} →
  {A : Fin m → Fin n → Real} →
    (upper lower : Real) →
      (upper_nonneg :
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            upper) →
        (lower_nonneg :
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              lower) →
          (upper_bound : @HighamBench.p07RectOpNorm2Le m n A upper) →
            (lower_bound : @HighamBench.p07RectLowerBound m n A lower) →
              (upper_attained :
                  @Exists.{1} (Fin n → Real) fun (x : Fin n → Real) =>
                    And
                      (@Eq.{1} Real (@HighamBench.p07VecNorm2 n x)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@Eq.{1} Real (@HighamBench.p07VecNorm2 m (@HighamBench.p07MatVec m n A x)) upper)) →
                (lower_attained :
                    @Exists.{1} (Fin n → Real) fun (x : Fin n → Real) =>
                      And
                        (@Eq.{1} Real (@HighamBench.p07VecNorm2 n x)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@Eq.{1} Real (@HighamBench.p07VecNorm2 m (@HighamBench.p07MatVec m n A x)) lower)) →
                  @HighamBench.P07RectSpectralExtrema m n A
```

### D024: `HighamBench.P07RectSpectralExtrema.upper`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c75b4daeaa2539014623f3fe27d424beb7a3525129f1c76b7f1045e18a4a32b9`

Type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → HighamBench.P07RectSpectralExtrema A → Real
```

Fully explicit type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → (self : @HighamBench.P07RectSpectralExtrema m n A) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n A self => self.1
```

### D025: `HighamBench.P07ScalarArithmeticModel.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `6408d56323ba6e427c9158cf9dd6f899b689810bc23e263f0d5ffee297480f62`

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
              HighamBench.P07ScalarArithmeticModel
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
              HighamBench.P07ScalarArithmeticModel
```

### D026: `HighamBench.p07RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f4aa477905f0e4f5f887cacfd9cfe27184181051fd51bd5c72a323007e9f230f`

Type:

```lean
{m n p : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin p → Real) → Fin m → Fin p → Real
```

Fully explicit type:

```lean
{m n p : Nat} → (A : Fin m → Fin n → Real) → (B : Fin n → Fin p → Real) → Fin m → Fin p → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D027: `HighamBench.P07ForwardSubstitutionTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `d57b57c2876ed63e222804792eeec41bea72f69296413d95931f62c9779b8768`

Type:

```lean
{model : HighamBench.P07ScalarArithmeticModel} →
  {m n : Nat} →
    {A : Fin m → Fin n → Real} →
      {R : Fin n → Fin n → Real} →
        (output : Fin m → Fin n → Real) →
          (∀ (j : Fin n), Ne (R j j) 0) →
            (∀ (i : Fin m) (j : Fin n),
                Eq (output i j)
                  (model.flDiv (model.flSub (A i j) (HighamBench.p07RoundedPrefixDot model output R i j)) (R j j))) →
              HighamBench.P07ForwardSubstitutionTrace model A R
```

Fully explicit type:

```lean
{model : HighamBench.P07ScalarArithmeticModel} →
  {m n : Nat} →
    {A : Fin m → Fin n → Real} →
      {R : Fin n → Fin n → Real} →
        (output : Fin m → Fin n → Real) →
          (diagonal_nonzero :
              ∀ (j : Fin n),
                @Ne.{1} Real (R j j) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
            (recurrence :
                ∀ (i : Fin m) (j : Fin n),
                  @Eq.{1} Real (output i j)
                    (HighamBench.P07ScalarArithmeticModel.flDiv model
                      (HighamBench.P07ScalarArithmeticModel.flSub model (A i j)
                        (@HighamBench.p07RoundedPrefixDot model m n output R i j))
                      (R j j))) →
              @HighamBench.P07ForwardSubstitutionTrace model m n A R
```

### D028: `HighamBench.P07MoorePenrosePseudoinverse`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `89b2cf979e20e555abda76fea46f8a8e2147d3e3d1dff15092c57c4f924ffd88`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin m → Real) → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (Aplus : Fin n → Fin m → Real) → Prop
```

### D029: `HighamBench.P07RectSpectralExtrema.lower`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6701d2f74cbedc569bdc435153835376168db8354ea52312b96c30e2ff7f581c`

Type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → HighamBench.P07RectSpectralExtrema A → Real
```

Fully explicit type:

```lean
{m n : Nat} → {A : Fin m → Fin n → Real} → (self : @HighamBench.P07RectSpectralExtrema m n A) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n A self => self.2
```

### D030: `HighamBench.p07FiniteId`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a73bc6e66275a8a807679c459a74cc5617c1524813228aeca6c3fa80c8a5e931`

Type:

```lean
{n : Nat} → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} i j => ite (Eq i j) 1 0
```

### D031: `HighamBench.p07Isometry`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cd3c8b859123ca43114b27f193282df325020baa3dfddc0924fe52b6cc96a77f`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (Q : Fin m → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} Q =>
  ∀ (x : Fin n → Real), Eq (HighamBench.p07VecNorm2 (HighamBench.p07MatVec Q x)) (HighamBench.p07VecNorm2 x)
```

### D032: `HighamBench.p07RectAdd`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e262c845cb19d34554377f167a619cfb5344fc89b294f70c0e3b0b624865a3a8`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin m → Fin n → Real) → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A B : Fin m → Fin n → Real) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A B i j => instHAdd.hAdd (A i j) (B i j)
```

### D033: `HighamBench.p07RectLowerBound`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `38a8bc211a42236d4a3455506ab1ec2bba575231f5d27ba4d69e6ba6d80f6d03`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (c : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A c =>
  ∀ (x : Fin n → Real),
    Real.instLE.le (instHMul.hMul c (HighamBench.p07VecNorm2 x)) (HighamBench.p07VecNorm2 (HighamBench.p07MatVec A x))
```

### D034: `HighamBench.p07RectOpNorm2Le`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3bc11a5a31a6cc30e603ebb4db699976fe20c2ba6cf962c97a349a0d3defc334`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (c : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A c =>
  ∀ (x : Fin n → Real),
    Real.instLE.le (HighamBench.p07VecNorm2 (HighamBench.p07MatVec A x)) (instHMul.hMul c (HighamBench.p07VecNorm2 x))
```

### D035: `HighamBench.p07RectSub`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a103606f80f2aa360edb97e12cd2187222b7e391268623e89d260202016d9fd0`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin m → Fin n → Real) → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A B : Fin m → Fin n → Real) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A B i j => instHSub.hSub (A i j) (B i j)
```

### D036: `HighamBench.p07UpperTriangular`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `76a5673c0e7633216d0cdf7fc2435d04d7d26e29f7f698942da03aca60acb7dd`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (R : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} R => ∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (R i j) 0
```

### D037: `HighamBench.p07VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9ab663fe9a74061006c9976250ea5e93003df8c9f220f04dff6f950bb66a0ff4`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D038: `HighamBench.P07MoorePenrosePseudoinverse.mk`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `ee3bfb12ae79b327abe3babe78900bceedf4658cefbea7039a27c7346ee44a9d`

Type:

```lean
∀ {m n : Nat} {A : Fin m → Fin n → Real} {Aplus : Fin n → Fin m → Real},
  Eq (HighamBench.p07RectMatMul (HighamBench.p07RectMatMul A Aplus) A) A →
    Eq (HighamBench.p07RectMatMul (HighamBench.p07RectMatMul Aplus A) Aplus) Aplus →
      Eq (Matrix.transpose (HighamBench.p07RectMatMul A Aplus)) (HighamBench.p07RectMatMul A Aplus) →
        Eq (Matrix.transpose (HighamBench.p07RectMatMul Aplus A)) (HighamBench.p07RectMatMul Aplus A) →
          HighamBench.P07MoorePenrosePseudoinverse A Aplus
```

Fully explicit type:

```lean
∀ {m n : Nat} {A : Fin m → Fin n → Real} {Aplus : Fin n → Fin m → Real}
  (reproduces_matrix :
    @Eq.{1} (Fin m → Fin n → Real) (@HighamBench.p07RectMatMul m m n (@HighamBench.p07RectMatMul m n m A Aplus) A) A)
  (reproduces_pseudoinverse :
    @Eq.{1} (Fin n → Fin m → Real) (@HighamBench.p07RectMatMul n n m (@HighamBench.p07RectMatMul n m n Aplus A) Aplus)
      Aplus)
  (range_projection_symmetric :
    @Eq.{1} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
      (@Matrix.transpose.{0, 0, 0} (Fin m) (Fin m) Real (@HighamBench.p07RectMatMul m n m A Aplus))
      (@HighamBench.p07RectMatMul m n m A Aplus))
  (domain_projection_symmetric :
    @Eq.{1} (Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
      (@Matrix.transpose.{0, 0, 0} (Fin n) (Fin n) Real (@HighamBench.p07RectMatMul n m n Aplus A))
      (@HighamBench.p07RectMatMul n m n Aplus A)),
  @HighamBench.P07MoorePenrosePseudoinverse m n A Aplus
```

### D039: `HighamBench.P07ScalarArithmeticModel.flDiv`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `cee411d47b0ded901cc117d6e97de4e26c813dd2c397d1e0b8dbfb1a1f1d9a02`

Type:

```lean
HighamBench.P07ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P07ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D040: `HighamBench.P07ScalarArithmeticModel.flSub`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `c363ad70f6bfa8621366a7328d95c519cca8070de50f628457812df90418bf14`

Type:

```lean
HighamBench.P07ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P07ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D041: `HighamBench.p07RoundedPrefixDot`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7f114fb07f30fe448eb213171e9baf582daf13901a4d74f6cb61c3d68c7c7055`

Type:

```lean
HighamBench.P07ScalarArithmeticModel →
  {m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Real
```

Fully explicit type:

```lean
(model : HighamBench.P07ScalarArithmeticModel) →
  {m n : Nat} → (Y : Fin m → Fin n → Real) → (R : Fin n → Fin n → Real) → (i : Fin m) → (j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model {m n} Y R i j =>
  HighamBench.recursiveSum model.flAdd j.val fun k =>
    have k' := ⟨k.val, ⋯⟩;
    model.flMul (Y i k') (R k' j)
```

### D042: `HighamBench.P07ScalarArithmeticModel.flAdd`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `7080f2573a445b7d57f13a49e09ff6bd5af7e8b70325271e8f9d81eeb67baabb`

Type:

```lean
HighamBench.P07ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P07ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D043: `HighamBench.P07ScalarArithmeticModel.flMul`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `63ced2571da783f33feeee3b014069f07b49bc8f92044041b4a9b0a16997d497`

Type:

```lean
HighamBench.P07ScalarArithmeticModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P07ScalarArithmeticModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D044: `HighamBench.p07RoundedPrefixDot._proof_1`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `a6cae81fc7c81927dc33042e4f435df41a9c09f2fff0b0e90f13786239d818a2`

Type:

```lean
∀ {n : Nat} (j : Fin n) (k : Fin j.val), Nat.instPreorder.lt k.val n
```

Fully explicit type:

```lean
∀ {n : Nat} (j : Fin n) (k : Fin (@Fin.val n j)),
  @LT.lt.{0} Nat (@Preorder.toLT.{0} Nat Nat.instPreorder) (@Fin.val (@Fin.val n j) k) n
```

### D045: `HighamBench.recursiveSum`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D046: `HighamBench.recursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `theorem`
- Distance from target type: `6`
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

### D047: `HighamBench.recursiveSum.match_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D048: `And`

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

### D049: `DivInvMonoid.toDiv`

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

### D050: `Fin`

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

### D051: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d947e6344cfd1327deca4c84f2eba89bf752b6e852fc0c680177dfaae4418776`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (f : α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, Eq (f a₁) (f a₂) → Eq a₁ a₂
```

### D052: `HAdd.hAdd`

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

### D053: `HDiv.hDiv`

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

### D054: `HSub.hSub`

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

### D055: `LE.le`

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

### D056: `LT.lt`

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

### D057: `Nat`

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

### D058: `OfNat.ofNat`

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

### D059: `One.toOfNat1`

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

### D060: `Real`

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

### D061: `Real.instAdd`

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

### D062: `Real.instDivInvMonoid`

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

### D063: `Real.instLE`

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

### D064: `Real.instLT`

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

### D065: `Real.instOne`

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

### D066: `Real.instSub`

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

### D067: `instHAdd`

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

### D068: `instHDiv`

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

### D069: `instHSub`

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

### D070: `Fin.fintype`

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

### D071: `Finset.sum`

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

### D072: `Finset.univ`

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

### D073: `HMul.hMul`

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

### D074: `Real.instAddCommMonoid`

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

### D075: `Real.instMul`

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

### D076: `instHMul`

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

### D077: `Eq`

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

### D078: `Exists`

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

### D079: `Inv.inv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c3aea3c6e2edd31a7b2cf071814315808ef7d84fd01d8c9b719313846ebca438`

Type:

```lean
{α : Type u} → [self : Inv α] → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Inv.{u} α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Inv α] => self.1
```

### D080: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D081: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D082: `Real.instInv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8996fd673a1e2289aaf761085a60a161bdafebda8cdd48d1efb3c89da1382980`

Type:

```lean
Inv Real
```

Fully explicit type:

```lean
Inv.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ inv := Real.inv'✝ }
```

### D083: `Real.instZero`

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

### D084: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D085: `Zero.toOfNat0`

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

### D086: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D087: `instLTNat`

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

### D088: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D089: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D090: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D091: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D092: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D093: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D094: `instDecidableEqFin`

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

### D095: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D096: `ite`

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

### D097: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D098: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D099: `Matrix.transpose`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `a0ee2c3649fa412f4b56ce3f375ef2f2d84b6b21507e1c4a93e90d3b9562973e`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Matrix m n α → Matrix n m α
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → (M : Matrix.{u_2, u_3, v} m n α) → Matrix.{u_3, u_2, v} n m α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} M => EquivLike.toFunLike.coe Matrix.of fun x y => M y x
```

### D100: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D101: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D102: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D103: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D104: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D105: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D106: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D107: `Preorder.toLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D108: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D109: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D110: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D111: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
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

### D112: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`

Type:

```lean
Nat
```

Fully explicit type:

```lean
Nat
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

### `HighamBench.P07Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P07Definitions.lean`
SHA-256: `6f0bad7f110b187ab3e04a0d3be457997ab16edb9414280f2f92ad2f12a059c8`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P07. -/
noncomputable def p07VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p07MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Product of two compatible finite rectangular matrices. -/
noncomputable def p07RectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Homogeneous rectangular operator-2 upper-bound certificate. -/
def p07RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec A x) ≤ c * p07VecNorm2 x

/-- Homogeneous lower singular-value certificate. -/
def p07RectLowerBound {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, c * p07VecNorm2 x ≤ p07VecNorm2 (p07MatVec A x)

/-- A rectangular matrix acts isometrically on Euclidean vectors. -/
def p07Isometry {m n : ℕ} (Q : Fin m → Fin n → ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec Q x) = p07VecNorm2 x

/-- Paired lower/upper singular-value certificate used to express the
condition-number identity in P07 Lemma 2.1 without choosing singular values. -/
def p07ConditionCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (lower upper : ℝ) : Prop :=
  p07RectLowerBound A lower ∧ p07RectOpNorm2Le A upper

/-- Identity matrix in P07's finite real-matrix notation. -/
noncomputable def p07FiniteId {n : ℕ} : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Pointwise addition of rectangular matrices. -/
def p07RectAdd {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ A i j + B i j

/-- Pointwise subtraction of rectangular matrices. -/
def p07RectSub {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ A i j - B i j

/-- Upper-triangularity of the computed factor inherited from Lemma 3.1. -/
def p07UpperTriangular {n : ℕ} (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

/-- Scalar floating-point operations used by the forward-substitution trace.
Each operation has the standard relative-error semantics used in section 2. -/
structure P07ScalarArithmeticModel where
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

/-- Rounded dot product over the entries preceding column `j`. -/
noncomputable def p07RoundedPrefixDot
    (model : P07ScalarArithmeticModel) {m n : ℕ}
    (Y : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  recursiveSum model.flAdd j.val fun k : Fin j.val ↦
    let k' : Fin n := ⟨k.val, lt_trans k.isLt j.isLt⟩
    model.flMul (Y i k') (R k' j)

/-- A row-wise finite-precision forward-substitution execution for `Y R = A`.
For upper triangular `R`, each output entry uses only earlier columns. -/
structure P07ForwardSubstitutionTrace
    (model : P07ScalarArithmeticModel) {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ) where
  output : Fin m → Fin n → ℝ
  diagonal_nonzero : ∀ j, R j j ≠ 0
  recurrence : ∀ i j,
    output i j =
      model.flDiv
        (model.flSub (A i j) (p07RoundedPrefixDot model output R i j))
        (R j j)

/-- The finite-precision sketch multiplication and Householder QR output from
Lemma 3.1 whose computed inverse is used in Lemma 3.2. -/
structure P07Lemma31ComputedPreconditioner (m s n : ℕ) where
  columns_pos : 0 < n
  sketch_gt_columns : n < s
  rows_gt_sketch : s < m
  A : Fin m → Fin n → ℝ
  S : Fin s → Fin m → ℝ
  computedSketch : Fin s → Fin n → ℝ
  sketchError : Fin s → Fin n → ℝ
  qrError : Fin s → Fin n → ℝ
  Qtilde : Fin s → Fin n → ℝ
  RHat : Fin n → Fin n → ℝ
  RHatInv : Fin n → Fin n → ℝ
  A_full_column_rank : Function.Injective (p07MatVec A)
  sketch_full_column_rank :
    Function.Injective (p07MatVec (p07RectMatMul S A))
  sketch_multiplication :
    computedSketch = p07RectAdd (p07RectMatMul S A) sketchError
  computed_householder_qr :
    p07RectMatMul Qtilde RHat = p07RectAdd computedSketch qrError
  qtilde_isometry : p07Isometry Qtilde
  rhat_upper_triangular : p07UpperTriangular RHat
  rhat_inverse_left : p07RectMatMul RHat RHatInv = p07FiniteId
  rhat_inverse_right : p07RectMatMul RHatInv RHat = p07FiniteId

/-- The exact preconditioned matrix `A RHat^{-1}` in Lemma 3.2. -/
noncomputable def p07ExactPreconditionedMatrix {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n) :
    Fin m → Fin n → ℝ :=
  p07RectMatMul pre.A pre.RHatInv

/-- The finite-precision forward-substitution output and its exact additive
error `DeltaY = YHat - A RHat^{-1}` from Lemma 3.2. -/
structure P07Lemma32ForwardRun {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel) where
  forwardSubstitution : P07ForwardSubstitutionTrace model pre.A pre.RHat
  DeltaY : Fin m → Fin n → ℝ
  deltaY_definition :
    DeltaY = p07RectSub forwardSubstitution.output
      (p07ExactPreconditionedMatrix pre)

/-- Exact attained largest and smallest singular-value data for a finite
rectangular matrix. The bound-plus-attainment pairs prevent the values from
being arbitrary loose certificates. -/
structure P07RectSpectralExtrema {m n : ℕ}
    (A : Fin m → Fin n → ℝ) where
  upper : ℝ
  lower : ℝ
  upper_nonneg : 0 ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_bound : p07RectOpNorm2Le A upper
  lower_bound : p07RectLowerBound A lower
  upper_attained : ∃ x : Fin n → ℝ,
    p07VecNorm2 x = 1 ∧ p07VecNorm2 (p07MatVec A x) = upper
  lower_attained : ∃ x : Fin n → ℝ,
    p07VecNorm2 x = 1 ∧ p07VecNorm2 (p07MatVec A x) = lower

/-- The four Penrose equations identifying an actual Moore--Penrose
pseudoinverse, rather than an arbitrary left inverse. -/
structure P07MoorePenrosePseudoinverse {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ) : Prop where
  reproduces_matrix :
    p07RectMatMul (p07RectMatMul A Aplus) A = A
  reproduces_pseudoinverse :
    p07RectMatMul (p07RectMatMul Aplus A) Aplus = Aplus
  range_projection_symmetric :
    Matrix.transpose (p07RectMatMul A Aplus) = p07RectMatMul A Aplus
  domain_projection_symmetric :
    Matrix.transpose (p07RectMatMul Aplus A) = p07RectMatMul Aplus A

/-- Exact spectral data for a matrix and its Moore--Penrose pseudoinverse.
When the smallest singular value is nonzero, the final field records the
standard identity `||A^dagger||_2 = 1 / sigma_min(A)`. -/
structure P07MatrixPseudoinverseSpectralData {m n : ℕ}
    (A : Fin m → Fin n → ℝ) where
  matrixSpectrum : P07RectSpectralExtrema A
  pseudoinverse : Fin n → Fin m → ℝ
  pseudoinverse_penrose :
    P07MoorePenrosePseudoinverse A pseudoinverse
  pseudoinverseSpectrum : P07RectSpectralExtrema pseudoinverse
  pseudoinverse_norm_eq_reciprocal :
    matrixSpectrum.lower ≠ 0 →
      pseudoinverseSpectrum.upper = matrixSpectrum.lower⁻¹

/-- Spectral 2-norm condition number represented using the actual
Moore--Penrose pseudoinverse. -/
noncomputable def p07ConditionNumber2 {m n : ℕ}
    {A : Fin m → Fin n → ℝ}
    (data : P07MatrixPseudoinverseSpectralData A) : ℝ :=
  data.matrixSpectrum.upper * data.pseudoinverseSpectrum.upper

/-- The exact perturbation parameter
`epsilon_2 = ||DeltaY||_2 ||(A RHat^{-1})^dagger||_2`. -/
noncomputable def p07Lemma32Epsilon {m n : ℕ}
    {A : Fin m → Fin n → ℝ}
    (exactData : P07MatrixPseudoinverseSpectralData A)
    {DeltaY : Fin m → Fin n → ℝ}
    (errorSpectrum : P07RectSpectralExtrema DeltaY) : ℝ :=
  errorSpectrum.upper * exactData.pseudoinverseSpectrum.upper

/-- Exact error matrix expanded in the proof of P07 Theorem 3.5. -/
noncomputable def p07BackwardError {m n : ℕ}
    (Y ΔY : Fin m → Fin n → ℝ)
    (R ΔR : Fin n → Fin n → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦
    (p07RectMatMul Y R i j - A i j) +
      (p07RectMatMul ΔY R i j +
        (p07RectMatMul Y ΔR i j + p07RectMatMul ΔY ΔR i j))

/-- Pointwise vector addition for the perturbed right-hand side in P07
Theorem 3.5. -/
def p07VecAdd {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i + y i

/-- The normal equation characterizing a least-squares solution. This is the
well-defined perturbed-data relation used for Theorem 3.5's tall system. -/
def p07LeastSquaresNormalEquation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin n,
    ∑ i : Fin m, A i j * (p07MatVec A x i - b i) = 0

/-- The backward-error witness assumed for unpreconditioned LSQR in equation
(3.9). `DeltaYHat` is distinct from the forward-substitution error in
`P07Lemma32ForwardRun`. -/
structure P07LSQRBackwardWitness {m n : ℕ}
    (YHat : Fin m → Fin n → ℝ) (b : Fin m → ℝ) where
  DeltaYHat : Fin m → Fin n → ℝ
  deltaB : Fin m → ℝ
  zHat : Fin n → ℝ
  perturbedPseudoinverse : Fin n → Fin m → ℝ
  pseudoinverse_penrose :
    P07MoorePenrosePseudoinverse
      (p07RectAdd YHat DeltaYHat) perturbedPseudoinverse
  iterate_relation :
    zHat = p07MatVec perturbedPseudoinverse (p07VecAdd b deltaB)

/-- Equation (2.6) for the final back substitution in Algorithm 1.3. -/
structure P07Equation26BackSubstitution {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (u : ℝ) (rSpectrum : P07RectSpectralExtrema pre.RHat)
    (zHat : Fin n → ℝ) where
  DeltaRHat : Fin n → Fin n → ℝ
  xHat : Fin n → ℝ
  perturbedRInv : Fin n → Fin n → ℝ
  inverse_left :
    p07RectMatMul (p07RectAdd pre.RHat DeltaRHat) perturbedRInv =
      p07FiniteId
  inverse_right :
    p07RectMatMul perturbedRInv (p07RectAdd pre.RHat DeltaRHat) =
      p07FiniteId
  backward_equation :
    p07MatVec (p07RectAdd pre.RHat DeltaRHat) xHat = zHat
  deltaR_bound :
    p07RectOpNorm2Le DeltaRHat
      (Real.sqrt n * gamma u n * rSpectrum.upper)

/-- Rowwise forward-substitution error used in the proof of Theorem 3.5,
including the exact spectral consequence stated immediately after it. -/
structure P07ForwardFormationError {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    {model : P07ScalarArithmeticModel}
    (forwardRun : P07Lemma32ForwardRun pre model)
    (u : ℝ) (rSpectrum : P07RectSpectralExtrema pre.RHat)
    (ySpectrum : P07RectSpectralExtrema
      forwardRun.forwardSubstitution.output) where
  rowPerturbation : Fin m → Fin n → Fin n → ℝ
  row_relation : ∀ i j,
    p07RectMatMul forwardRun.forwardSubstitution.output pre.RHat i j -
        pre.A i j =
      -∑ k : Fin n,
        forwardRun.forwardSubstitution.output i k * rowPerturbation i k j
  componentwise_bound : ∀ i j k,
    |rowPerturbation i j k| ≤ gamma u n * |pre.RHat j k|
  residual_bound :
    p07RectOpNorm2Le
      (fun i j ↦
        p07RectMatMul forwardRun.forwardSubstitution.output pre.RHat i j -
          pre.A i j)
      ((n : ℝ) * gamma u n * rSpectrum.upper * ySpectrum.upper)

/-- The Algorithm 1.3 execution data needed by the unnumbered backward-error
result in the proof of Theorem 3.5. LSQR is applied directly to the explicitly
formed `YHat`; no SAS initialization is represented. -/
structure P07SAABlendenpikRun {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel)
    (forwardRun : P07Lemma32ForwardRun pre model)
    (u : ℝ) where
  unit_roundoff : model.unitRoundoff = u
  gamma_valid : GammaValid u n
  b : Fin m → ℝ
  rSpectrum : P07RectSpectralExtrema pre.RHat
  ySpectrum : P07RectSpectralExtrema forwardRun.forwardSubstitution.output
  formationError :
    P07ForwardFormationError pre forwardRun u rSpectrum ySpectrum
  lsqr : P07LSQRBackwardWitness forwardRun.forwardSubstitution.output b
  lsqrDeltaSpectrum : P07RectSpectralExtrema lsqr.DeltaYHat
  backSubstitution :
    P07Equation26BackSubstitution pre u rSpectrum lsqr.zHat

/-- The exact four-term `DeltaA` in the proof of P07 Theorem 3.5. -/
noncomputable def p07Theorem35DeltaA {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin m → Fin n → ℝ :=
  p07BackwardError forwardRun.forwardSubstitution.output
    run.lsqr.DeltaYHat pre.RHat run.backSubstitution.DeltaRHat pre.A

/-- The perturbed matrix `A + DeltaA` associated with the SAA output. -/
noncomputable def p07Theorem35PerturbedA {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin m → Fin n → ℝ :=
  p07RectAdd pre.A (p07Theorem35DeltaA run)

/-- The matrix `YHat + DeltaYHat` in the assumed LSQR backward error. -/
def p07Theorem35PerturbedY {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin m → Fin n → ℝ :=
  p07RectAdd forwardRun.forwardSubstitution.output run.lsqr.DeltaYHat

/-- The matrix `RHat + DeltaRHat` in the final back substitution. -/
def p07Theorem35PerturbedR {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) :
    Fin n → Fin n → ℝ :=
  p07RectAdd pre.RHat run.backSubstitution.DeltaRHat

/-- The perturbed right-hand side `b + deltaB` retained by Theorem 3.5. -/
def p07Theorem35PerturbedB {m s n : ℕ}
    {pre : P07Lemma31ComputedPreconditioner m s n}
    {model : P07ScalarArithmeticModel}
    {forwardRun : P07Lemma32ForwardRun pre model} {u : ℝ}
    (run : P07SAABlendenpikRun pre model forwardRun u) : Fin m → ℝ :=
  p07VecAdd run.b run.lsqr.deltaB

end HighamBench
```
