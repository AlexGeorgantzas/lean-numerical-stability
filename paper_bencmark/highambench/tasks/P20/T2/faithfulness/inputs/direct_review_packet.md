# Declaration dossier for P20-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p20_t2_scaled_input_error {n : ℕ} {ι : Type*}
    (model : P20Model1 ι) (t : ι) (x y : Fin n → ℝ)
    (lambda mu : ℝ) (hn : 0 < n)
    (hx : 0 < p20InfNormVec x) (hy : 0 < p20InfNormVec y)
    (hlambda : p20MaximalPowerTwoScale
      (p20ModelScalingThreshold n model t) (p20InfNormVec x) lambda)
    (hmu : p20MaximalPowerTwoScale
      (p20ModelScalingThreshold n model t) (p20InfNormVec y) mu) :
    |p20InputStageError model t lambda mu x y| ≤
      p20InputStageErrorEnvelope
        (p20InputUnitRoundoff model t)
        (p20InputUnderflowEnvelope model t)
        (p20ModelScalingThreshold n model t) x y
```

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} (model : HighamBench.P20Model1 ι) (t : ι) (x y : Fin n → Real) (lambda mu : Real),
  instLTNat.lt 0 n →
    Real.instLT.lt 0 (HighamBench.p20InfNormVec x) →
      Real.instLT.lt 0 (HighamBench.p20InfNormVec y) →
        HighamBench.p20MaximalPowerTwoScale (HighamBench.p20ModelScalingThreshold n model t)
            (HighamBench.p20InfNormVec x) lambda →
          HighamBench.p20MaximalPowerTwoScale (HighamBench.p20ModelScalingThreshold n model t)
              (HighamBench.p20InfNormVec y) mu →
            Real.instLE.le (abs (HighamBench.p20InputStageError model t lambda mu x y))
              (HighamBench.p20InputStageErrorEnvelope (HighamBench.p20InputUnitRoundoff model t)
                (HighamBench.p20InputUnderflowEnvelope model t) (HighamBench.p20ModelScalingThreshold n model t) x y)
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} (model : HighamBench.P20Model1.{u_1} ι) (t : ι) (x y : Fin n → Real) (lambda mu : Real)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hx :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HighamBench.p20InfNormVec n x))
  (hy :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HighamBench.p20InfNormVec n y))
  (hlambda :
    HighamBench.p20MaximalPowerTwoScale (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)
      (@HighamBench.p20InfNormVec n x) lambda)
  (hmu :
    HighamBench.p20MaximalPowerTwoScale (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)
      (@HighamBench.p20InfNormVec n y) mu),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p20InputStageError.{u_1} n ι model t lambda mu x y))
    (@HighamBench.p20InputStageErrorEnvelope n (@HighamBench.p20InputUnitRoundoff.{u_1} ι model t)
      (@HighamBench.p20InputUnderflowEnvelope.{u_1} ι model t) (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)
      x y)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P20Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P20Definitions` imports: `HighamBench.Core`, `Mathlib.Algebra.Order.Archimedean.Basic`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Data.Matrix.Mul`, `Mathlib.Data.Real.Sqrt`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P20Model1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `e061b0ae3b92688463023faf203412bd4115dc0ed0667840f7767652f00b9019`

Type:

```lean
Type u_1 → Type u_1
```

Fully explicit type:

```lean
(ι : Type u_1) → Type u_1
```

### D002: `HighamBench.p20InfNormVec`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `87f59ddda7d28f2342745750052393a1a7f8e6da20099629ce901b53ae3a06a8`

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
fun {n} x => (Finset.univ.sup fun i => (abs (x i)).toNNReal).toReal
```

### D003: `HighamBench.p20InputStageError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `54394c0c5e5d3f5a9530690f86ad7003f9e452d266e18e730f097b0b38413347`

Type:

```lean
{n : Nat} → {ι : Type u_1} → HighamBench.P20Model1 ι → ι → Real → Real → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → (model : HighamBench.P20Model1.{u_1} ι) → (t : ι) → (lambda mu : Real) → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} model t lambda mu x y =>
  instHSub.hSub (HighamBench.p20ScaledInputInnerProduct model t lambda mu x y)
    (Finset.univ.sum fun i => instHMul.hMul (x i) (y i))
```

### D004: `HighamBench.p20InputStageErrorEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7a64a641f48b866e0186df55f97c7fcb6d9ef00c7cc39609f5ed9fb597e33bea`

Type:

```lean
{n : Nat} → Real → Real → Real → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (u gmin theta : Real) → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} u gmin theta x y =>
  instHAdd.hAdd
    (instHMul.hMul (instHAdd.hAdd (instHMul.hMul 2 u) (instHPow.hPow u 2)) (HighamBench.p20AbsInnerProduct x y))
    (instHMul.hMul
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 n.cast) (Real.instInv.inv theta)) gmin)
          (instHAdd.hAdd (instHAdd.hAdd 1 u) (instHMul.hMul (Real.instInv.inv theta) gmin)))
        (HighamBench.p20InfNormVec x))
      (HighamBench.p20InfNormVec y))
```

### D005: `HighamBench.p20InputUnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `65fb848ac68b350b4c5f345e1b63f3818de1dfd55b1441c386210576f85e7701`

Type:

```lean
{ι : Type u_1} → HighamBench.P20Model1 ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (model : HighamBench.P20Model1.{u_1} ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} model t => HighamBench.p20FormatUnderflowEnvelope model.inputFormat t
```

### D006: `HighamBench.p20InputUnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c8ca83340edf9709c9e3394a10d383e421ce4db7c464585c7c881bc878956a32`

Type:

```lean
{ι : Type u_1} → HighamBench.P20Model1 ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (model : HighamBench.P20Model1.{u_1} ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} model t => HighamBench.p20FormatUnitRoundoff model.inputFormat t
```

### D007: `HighamBench.p20MaximalPowerTwoScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fb4c39249333a2b6fcc41db880a13b76bb70b92044a24ec0042af3b1053ddfc8`

Type:

```lean
Real → Real → Real → Prop
```

Fully explicit type:

```lean
(theta vectorNorm lambda : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun theta vectorNorm lambda =>
  And (HighamBench.p20IsPowerOfTwo lambda)
    (And (Real.instLT.lt 0 lambda)
      (Or (And (Eq vectorNorm 0) (Eq lambda 1))
        (And (Real.instLT.lt 0 vectorNorm)
          (And (Real.instLT.lt (instHDiv.hDiv theta (instHMul.hMul 2 vectorNorm)) lambda)
            (Real.instLE.le lambda (instHDiv.hDiv theta vectorNorm))))))
```

### D008: `HighamBench.p20ModelScalingThreshold`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8177b50be99c15b398f8f4378f9be576d43e18ba542f985b3c11aa1737057c8e`

Type:

```lean
{ι : Type u_1} → Nat → HighamBench.P20Model1 ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (n : Nat) → (model : HighamBench.P20Model1.{u_1} ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} n model t =>
  HighamBench.p20ScalingThreshold n (HighamBench.p20FormatMaxFinite model.inputFormat t)
    (HighamBench.p20FormatMaxFinite model.accumulationFormat t)
```

### D009: `HighamBench.P20Model1.accumulationFormat`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `019580b5dca9b3907a64545ee2b700984d557fbd9c0f2dafd17bf6484dfc7e63`

Type:

```lean
{ι : Type u_1} → HighamBench.P20Model1 ι → HighamBench.P20BinaryFormatFamily ι
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20Model1.{u_1} ι) → HighamBench.P20BinaryFormatFamily.{u_1} ι
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.2
```

### D010: `HighamBench.P20Model1.inputFormat`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fdc85d76dfd8fdfe7bfc27ffd0f7e0b055310bbd4409c607e4b5b0b7d5b9272d`

Type:

```lean
{ι : Type u_1} → HighamBench.P20Model1 ι → HighamBench.P20BinaryFormatFamily ι
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20Model1.{u_1} ι) → HighamBench.P20BinaryFormatFamily.{u_1} ι
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.1
```

### D011: `HighamBench.P20Model1.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `7546b5e58afb9aa467efb29e321d522aa2044aee6b5571587488bc68eaed388c`

Type:

```lean
{ι : Type u_1} →
  (inputFormat accumulationFormat : HighamBench.P20BinaryFormatFamily ι) →
    (∀ (t : ι), instLENat.le (inputFormat.precision t) (accumulationFormat.precision t)) →
      (∀ (t : ι),
          And (Int.instLEInt.le (accumulationFormat.minExponent t) (inputFormat.minExponent t))
            (Int.instLEInt.le (inputFormat.maxExponent t) (accumulationFormat.maxExponent t))) →
        (inputRound inputDelta inputEta : ι → Real → Real) →
          (∀ (t : ι) (x : Real),
              Eq (inputRound t x) (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (inputDelta t x))) (inputEta t x))) →
            (∀ (t : ι) (x : Real),
                Real.instLE.le (abs (inputDelta t x)) (HighamBench.p20FormatUnitRoundoff inputFormat t)) →
              (∀ (t : ι) (x : Real),
                  Real.instLE.le (abs (inputEta t x)) (HighamBench.p20FormatUnderflowEnvelope inputFormat t)) →
                (∀ (t : ι) (x : Real), Eq (instHMul.hMul (inputEta t x) (inputDelta t x)) 0) →
                  (accumulationRound accumulationDelta accumulationEta : ι → Real → Real) →
                    (∀ (t : ι) (x : Real),
                        Eq (accumulationRound t x)
                          (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (accumulationDelta t x)))
                            (accumulationEta t x))) →
                      (∀ (t : ι) (x : Real),
                          Real.instLE.le (abs (accumulationDelta t x))
                            (HighamBench.p20FormatUnitRoundoff accumulationFormat t)) →
                        (∀ (t : ι) (x : Real),
                            Real.instLE.le (abs (accumulationEta t x))
                              (HighamBench.p20FormatUnderflowEnvelope accumulationFormat t)) →
                          (∀ (t : ι) (x : Real), Eq (instHMul.hMul (accumulationEta t x) (accumulationDelta t x)) 0) →
                            HighamBench.P20Model1 ι
```

Fully explicit type:

```lean
{ι : Type u_1} →
  (inputFormat accumulationFormat : HighamBench.P20BinaryFormatFamily.{u_1} ι) →
    (accumulation_precision :
        ∀ (t : ι),
          @LE.le.{0} Nat instLENat (@HighamBench.P20BinaryFormatFamily.precision.{u_1} ι inputFormat t)
            (@HighamBench.P20BinaryFormatFamily.precision.{u_1} ι accumulationFormat t)) →
      (accumulation_range :
          ∀ (t : ι),
            And
              (@LE.le.{0} Int Int.instLEInt
                (@HighamBench.P20BinaryFormatFamily.minExponent.{u_1} ι accumulationFormat t)
                (@HighamBench.P20BinaryFormatFamily.minExponent.{u_1} ι inputFormat t))
              (@LE.le.{0} Int Int.instLEInt (@HighamBench.P20BinaryFormatFamily.maxExponent.{u_1} ι inputFormat t)
                (@HighamBench.P20BinaryFormatFamily.maxExponent.{u_1} ι accumulationFormat t))) →
        (inputRound inputDelta inputEta : ι → Real → Real) →
          (input_rounding_equation :
              ∀ (t : ι) (x : Real),
                @Eq.{1} Real (inputRound t x)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (inputDelta t x)))
                    (inputEta t x))) →
            (input_delta_bound :
                ∀ (t : ι) (x : Real),
                  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (inputDelta t x))
                    (@HighamBench.p20FormatUnitRoundoff.{u_1} ι inputFormat t)) →
              (input_eta_bound :
                  ∀ (t : ι) (x : Real),
                    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (inputEta t x))
                      (@HighamBench.p20FormatUnderflowEnvelope.{u_1} ι inputFormat t)) →
                (input_error_exclusive :
                    ∀ (t : ι) (x : Real),
                      @Eq.{1} Real
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (inputEta t x)
                          (inputDelta t x))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                  (accumulationRound accumulationDelta accumulationEta : ι → Real → Real) →
                    (accumulation_rounding_equation :
                        ∀ (t : ι) (x : Real),
                          @Eq.{1} Real (accumulationRound t x)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                  (accumulationDelta t x)))
                              (accumulationEta t x))) →
                      (accumulation_delta_bound :
                          ∀ (t : ι) (x : Real),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup (accumulationDelta t x))
                              (@HighamBench.p20FormatUnitRoundoff.{u_1} ι accumulationFormat t)) →
                        (accumulation_eta_bound :
                            ∀ (t : ι) (x : Real),
                              @LE.le.{0} Real Real.instLE
                                (@abs.{0} Real Real.lattice Real.instAddGroup (accumulationEta t x))
                                (@HighamBench.p20FormatUnderflowEnvelope.{u_1} ι accumulationFormat t)) →
                          (accumulation_error_exclusive :
                              ∀ (t : ι) (x : Real),
                                @Eq.{1} Real
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (accumulationEta t x) (accumulationDelta t x))
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                            HighamBench.P20Model1.{u_1} ι
```

### D012: `HighamBench.p20AbsInnerProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8407e3241488a2b0b4b3fc86e53687702593568f1a8280d97751a44a1a005fd8`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (abs (x i)) (abs (y i))
```

### D013: `HighamBench.p20FormatMaxFinite`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e247b0fabe551e796b6da7ea178c4d700c64dbf29a01abedbf0725f497a97ff1`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (format : HighamBench.P20BinaryFormatFamily.{u_1} ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} format t => HighamBench.p20MaxFinite (format.precision t) (format.maxExponent t)
```

### D014: `HighamBench.p20FormatUnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2c81bbdf95763d3fa04a1c4ccaa3cac2e1320e447cb84541092ab38dbd2b83e0`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (format : HighamBench.P20BinaryFormatFamily.{u_1} ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} format t =>
  HighamBench.p20UnderflowEnvelope (format.precision t) (format.minExponent t) (format.hasSubnormals t)
```

### D015: `HighamBench.p20FormatUnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9e812a87b4db8426019cf32b6a1ced30d8bceb7427e394157773672a06514e80`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (format : HighamBench.P20BinaryFormatFamily.{u_1} ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} format t => HighamBench.p20UnitRoundoff (format.precision t)
```

### D016: `HighamBench.p20IsPowerOfTwo`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cdbc02ca950134eb20d94e5488f66c176cc912c7aa24e523ded6bd5ee37e98e5`

Type:

```lean
Real → Prop
```

Fully explicit type:

```lean
(lambda : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun lambda => Exists fun exponent => Eq lambda (instHPow.hPow 2 exponent)
```

### D017: `HighamBench.p20IsPowerOfTwo._proof_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `2ce92de675040573a86bb56eb1810ec5f97d8bfda24fdbdb86d7ca409b945411`

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

### D018: `HighamBench.p20ScaledInputInnerProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9bb3d1dd7e19b5f65b7c8f9a9c50446c58b6d77382347306c062f6ab85c40c00`

Type:

```lean
{n : Nat} → {ι : Type u_1} → HighamBench.P20Model1 ι → ι → Real → Real → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → (model : HighamBench.P20Model1.{u_1} ι) → (t : ι) → (lambda mu : Real) → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} model t lambda mu x y =>
  instHMul.hMul (instHMul.hMul (Real.instInv.inv lambda) (Real.instInv.inv mu))
    (Finset.univ.sum fun i =>
      instHMul.hMul (model.inputRound t (instHMul.hMul lambda (x i))) (model.inputRound t (instHMul.hMul mu (y i))))
```

### D019: `HighamBench.p20ScalingThreshold`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9f68c8a231e4cea47898d3834d4362c543f7e7455dc046f54bb660b2dff27910`

Type:

```lean
Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n : Nat) → (fmax Fmax : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n fmax Fmax => Real.instMin.min fmax (instHDiv.hDiv Fmax n.cast).sqrt
```

### D020: `HighamBench.p20SingleInputUnderflowBound._proof_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `8a85a65264d1eaf6bf92eb9238ef21e86787b07b20e078bcd23e3fd0e91d4fbb`

Type:

```lean
(instHAdd.hAdd 3 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D021: `HighamBench.P20BinaryFormatFamily`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `f68a172410c9f21a3e85a3437dc6a91f7d8b7987bb2bc0e88a508c3382845171`

Type:

```lean
Type u_1 → Type u_1
```

Fully explicit type:

```lean
(ι : Type u_1) → Type u_1
```

### D022: `HighamBench.P20BinaryFormatFamily.hasSubnormals`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `390b0a085aaf97e51cd4cf35d7860d38ac05963d49604a5558ee81436c840d6a`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Bool
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20BinaryFormatFamily.{u_1} ι) → ι → Bool
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.4
```

### D023: `HighamBench.P20BinaryFormatFamily.maxExponent`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3b81919890027c1e8a089b64312b036157e0406024d90701758eac7df5f53065`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Int
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20BinaryFormatFamily.{u_1} ι) → ι → Int
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.3
```

### D024: `HighamBench.P20BinaryFormatFamily.minExponent`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d423cdf3493e923735f83da736f28a3fe9781ed8df32e051de3dc5ebf4263509`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Int
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20BinaryFormatFamily.{u_1} ι) → ι → Int
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.2
```

### D025: `HighamBench.P20BinaryFormatFamily.precision`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `15283c4649b8a2eb8dbea073396ef2096b142fffdad25db29fc18bd95e90d37f`

Type:

```lean
{ι : Type u_1} → HighamBench.P20BinaryFormatFamily ι → ι → Nat
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20BinaryFormatFamily.{u_1} ι) → ι → Nat
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.1
```

### D026: `HighamBench.P20Model1.inputRound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c05f813d78781714c9102a1b87725dd0a5f46a457ef122cd45049ea09beb2fae`

Type:

```lean
{ι : Type u_1} → HighamBench.P20Model1 ι → ι → Real → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → (self : HighamBench.P20Model1.{u_1} ι) → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.5
```

### D027: `HighamBench.p20MaxFinite`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e812122843a7693eb9da20df127bdfd0b036f7eb87b5291df77467d35da85027`

Type:

```lean
Nat → Int → Real
```

Fully explicit type:

```lean
(precision : Nat) → (maxExponent : Int) → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision maxExponent =>
  instHMul.hMul (instHPow.hPow 2 maxExponent)
    (instHSub.hSub 2 (instHMul.hMul 2 (HighamBench.p20UnitRoundoff precision)))
```

### D028: `HighamBench.p20UnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `98e39d9e9f622feb1800dc6ed026db533af44c2455719d25e42c991fb6e6b98f`

Type:

```lean
Nat → Int → Bool → Real
```

Fully explicit type:

```lean
(precision : Nat) → (minExponent : Int) → (hasSubnormals : Bool) → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision minExponent hasSubnormals =>
  HighamBench.p20UnderflowEnvelope.match_1 (fun hasSubnormals => Real) hasSubnormals
    (fun _ => instHDiv.hDiv (HighamBench.p20MinNormal minExponent) 2) fun _ =>
    instHMul.hMul (HighamBench.p20UnitRoundoff precision) (HighamBench.p20MinNormal minExponent)
```

### D029: `HighamBench.p20UnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `374e1e67fe075ea077dd0ca7e1b7b13a7719c0f4c5d32224c3e123b307030749`

Type:

```lean
Nat → Real
```

Fully explicit type:

```lean
(precision : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision => instHPow.hPow (Real.instInv.inv 2) precision
```

### D030: `HighamBench.P20BinaryFormatFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `bfbe55aaba8cae1c8051b14d53b97fb80661056589ec88edfc2175227423ba98`

Type:

```lean
{ι : Type u_1} →
  (precision : ι → Nat) →
    (minExponent maxExponent : ι → Int) →
      (ι → Bool) →
        (∀ (t : ι), instLTNat.lt 0 (precision t)) →
          (∀ (t : ι), Int.instLEInt.le (minExponent t) (maxExponent t)) → HighamBench.P20BinaryFormatFamily ι
```

Fully explicit type:

```lean
{ι : Type u_1} →
  (precision : ι → Nat) →
    (minExponent maxExponent : ι → Int) →
      (hasSubnormals : ι → Bool) →
        (precision_pos :
            ∀ (t : ι),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (precision t)) →
          (exponent_range_nonempty : ∀ (t : ι), @LE.le.{0} Int Int.instLEInt (minExponent t) (maxExponent t)) →
            HighamBench.P20BinaryFormatFamily.{u_1} ι
```

### D031: `HighamBench.p20MinNormal`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `a1ea1d99687f61140e8592b6154c5c66bbde2de8d842aa90e456007cea8d43fd`

Type:

```lean
Int → Real
```

Fully explicit type:

```lean
(minExponent : Int) → Real
```

Definition body (one-level semantic boundary):

```lean
fun minExponent => instHPow.hPow 2 minExponent
```

### D032: `HighamBench.p20UnderflowEnvelope.match_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `58f84c67586c398171db7adf3049e575348ae8be9cfe7a764f1cdbe2eb2944fa`

Type:

```lean
(motive : Bool → Sort u_1) →
  (hasSubnormals : Bool) → (Unit → motive Bool.false) → (Unit → motive Bool.true) → motive hasSubnormals
```

Fully explicit type:

```lean
(motive : Bool → Sort u_1) →
  (hasSubnormals : Bool) →
    (h_1 : (a : Unit) → motive Bool.false) → (h_2 : (a : Unit) → motive Bool.true) → motive hasSubnormals
```

Definition body (one-level semantic boundary):

```lean
fun motive hasSubnormals h_1 h_2 => Bool.casesOn hasSubnormals (h_1 Unit.unit) (h_2 Unit.unit)
```

### D033: `Fin`

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

### D034: `LE.le`

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

### D035: `LT.lt`

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

### D036: `Nat`

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

### D037: `OfNat.ofNat`

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

### D038: `Real`

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

### D039: `Real.instAddGroup`

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

### D040: `Real.instLE`

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

### D041: `Real.instLT`

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

### D042: `Real.instZero`

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

### D043: `Real.lattice`

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

### D044: `Zero.toOfNat0`

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

### D045: `abs`

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

### D046: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D047: `instOfNatNat`

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

### D048: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D049: `ConditionallyCompleteLinearOrderBot.toOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.ConditionallyCompleteLattice.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8d4bfb1cedb616878ecbd86e2180bc7ca93b21716425a9954eeab125e930003f`

Type:

```lean
{α : Type u_5} → [self : ConditionallyCompleteLinearOrderBot α] → OrderBot α
```

Fully explicit type:

```lean
{α : Type u_5} →
  [self : ConditionallyCompleteLinearOrderBot.{u_5} α] →
    @OrderBot.{u_5} α
      (@Preorder.toLE.{u_5} α
        (@PartialOrder.toPreorder.{u_5} α
          (@SemilatticeSup.toPartialOrder.{u_5} α
            (@Lattice.toSemilatticeSup.{u_5} α
              (@ConditionallyCompleteLattice.toLattice.{u_5} α
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u_5} α
                  (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u_5} α self)))))))
```

Definition body (one-level semantic boundary):

```lean
fun α [self : ConditionallyCompleteLinearOrderBot α] => self.2
```

### D050: `DivInvMonoid.toDiv`

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

### D051: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D052: `Fin.fintype`

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

### D053: `Finset.sum`

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

### D054: `Finset.sup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Lattice.Fold`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dd4c14458f3cc53851b18c831b354790927e7783eeceddbd2bc8e0e17c3e5d98`

Type:

```lean
{α : Type u_2} → {β : Type u_3} → [inst : SemilatticeSup α] → [OrderBot α] → Finset β → (β → α) → α
```

Fully explicit type:

```lean
{α : Type u_2} →
  {β : Type u_3} →
    [inst : SemilatticeSup.{u_2} α] →
      [@OrderBot.{u_2} α
            (@Preorder.toLE.{u_2} α (@PartialOrder.toPreorder.{u_2} α (@SemilatticeSup.toPartialOrder.{u_2} α inst)))] →
        (s : Finset.{u_3} β) → (f : β → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [SemilatticeSup α] [inst_1 : OrderBot α] s f =>
  Finset.fold (fun x1 x2 => SemilatticeSup.toMax.max x1 x2) inst_1.bot f s
```

### D055: `Finset.univ`

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

### D056: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D057: `HDiv.hDiv`

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

### D058: `HMul.hMul`

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

### D059: `HPow.hPow`

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

### D060: `HSub.hSub`

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

### D061: `Inv.inv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D062: `Monoid.toNatPow`

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

### D063: `NNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `490ebc1f72b3ced8506e1bcbd0016d4c351adf097644509fd1dd17a93c4e950f`

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
Subtype fun r => Real.instLE.le 0 r
```

### D064: `NNReal.instConditionallyCompleteLinearOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a6df35137b7f52b464ab762b2393c5d6b5cba77a839712e58984b3a00414c3af`

Type:

```lean
ConditionallyCompleteLinearOrderBot NNReal
```

Fully explicit type:

```lean
ConditionallyCompleteLinearOrderBot.{0} NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.conditionallyCompleteLinearOrderBot 0
```

### D065: `NNReal.toReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b78a80825150cf81a49e8914dd12c5dfb7e284ed0e70b3449011ac3d3f49dc66`

Type:

```lean
NNReal → Real
```

Fully explicit type:

```lean
NNReal → Real
```

Definition body (one-level semantic boundary):

```lean
Subtype.val
```

### D066: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D067: `One.toOfNat1`

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

### D068: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D069: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D070: `Real.instAddCommMonoid`

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

### D071: `Real.instDivInvMonoid`

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

### D072: `Real.instInv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D073: `Real.instMonoid`

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

### D074: `Real.instMul`

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

### D075: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D076: `Real.instOne`

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

### D077: `Real.instSub`

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

### D078: `Real.toNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d5a5745fe197b17d74201a2db472f8ca23ff9fdb827ba67a427efe3c5468ae2e`

Type:

```lean
Real → NNReal
```

Fully explicit type:

```lean
(r : Real) → NNReal
```

Definition body (one-level semantic boundary):

```lean
fun r => ⟨Real.instMax.max r 0, ⋯⟩
```

### D079: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D080: `instHDiv`

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

### D081: `instHMul`

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

### D082: `instHPow`

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

### D083: `instHSub`

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

### D084: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D085: `instSemilatticeSupNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2a6440af851e8806e3c58934c33bb1185e865186dfb38346ffc479f2e156fbfa`

Type:

```lean
SemilatticeSup NNReal
```

Fully explicit type:

```lean
SemilatticeSup.{0} NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.semilatticeSup
```

### D086: `DivInvMonoid.toZPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1e8b6758b3a3bf88b78eeff1bb4effb1dce39e6b9e38153dab79b664d58d89b5`

Type:

```lean
{M : Type u_2} → [DivInvMonoid M] → Pow M Int
```

Fully explicit type:

```lean
{M : Type u_2} → [DivInvMonoid.{u_2} M] → Pow.{u_2, 0} M Int
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : DivInvMonoid M] => { pow := fun x n => inst.zpow n x }
```

### D087: `Exists`

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

### D088: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D089: `Int.instLEInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f51330a4994f7ae8126646c50493b06244696bcf7ecd84ee76d837ba05820e15`

Type:

```lean
LE Int
```

Fully explicit type:

```lean
LE.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ le := Int.le }
```

### D090: `Min.min`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4781b8f14117c86f8d250ccd7a9bf20c2b8b6554a48ba0b45f9010ff26a72ea7`

Type:

```lean
{α : Type u} → [self : Min α] → α → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Min.{u} α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Min α] => self.1
```

### D091: `Nat.AtLeastTwo`

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

### D092: `Real.instMin`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d2cd90660c09f0530ecb3d8bd97eb9c8e1ed4fc9eebe2650e6a65a653c99fcb0`

Type:

```lean
Min Real
```

Fully explicit type:

```lean
Min.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ min := Real.inf✝ }
```

### D093: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D094: `instAddNat`

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

### D095: `instLENat`

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

### D096: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D097: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D098: `Bool.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `98d460e4da0ec8a7ca3d02bf4c338e01aafaa4536c4a8f107307135e07b476c6`

Type:

```lean
{motive : Bool → Sort u} → (t : Bool) → motive Bool.false → motive Bool.true → motive t
```

Fully explicit type:

```lean
{motive : (t : Bool) → Sort u} → (t : Bool) → (false : motive Bool.false) → (true : motive Bool.true) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t false true => Bool.rec false true t
```

### D099: `Bool.false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `903a7293b3a1c2eca38e3f5e4346c7e732c386d96e6399ffb0cedaba068cd441`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D100: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D101: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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
