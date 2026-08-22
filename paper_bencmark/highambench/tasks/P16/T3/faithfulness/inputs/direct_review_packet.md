# Declaration dossier for P16-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p16_t3_mixed_precision_geometric_convergence
    {n : ℕ} (run : P16FixedMixedPrecisionGMRESRun n)
    (hLambda : ∀ i : ℕ,
      0 ≤ p16FixedMixedContraction run i ∧
        p16FixedMixedContraction run i < 1) :
    (∀ i : ℕ,
      p16BackwardError run.A run.b (run.xHat (i + 1)) ≤
        p16FixedMixedContraction run i *
            p16BackwardError run.A run.b (run.xHat i) +
          p16FixedBackwardFloor run i) ∧
      ∀ i : ℕ,
        p16ForwardError run.xExact (run.xHat (i + 1)) ≤
          p16FixedMixedContraction run i *
              p16ForwardError run.xExact (run.xHat i) +
            p16FixedForwardFloor run i
```

## Elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P16FixedMixedPrecisionGMRESRun n),
  (∀ (i : Nat),
      And (Real.instLE.le 0 (HighamBench.p16FixedMixedContraction run i))
        (Real.instLT.lt (HighamBench.p16FixedMixedContraction run i) 1)) →
    And
      (∀ (i : Nat),
        Real.instLE.le (HighamBench.p16BackwardError run.A run.b (run.xHat (instHAdd.hAdd i 1)))
          (instHAdd.hAdd
            (instHMul.hMul (HighamBench.p16FixedMixedContraction run i)
              (HighamBench.p16BackwardError run.A run.b (run.xHat i)))
            (HighamBench.p16FixedBackwardFloor run i)))
      (∀ (i : Nat),
        Real.instLE.le (HighamBench.p16ForwardError run.xExact (run.xHat (instHAdd.hAdd i 1)))
          (instHAdd.hAdd
            (instHMul.hMul (HighamBench.p16FixedMixedContraction run i)
              (HighamBench.p16ForwardError run.xExact (run.xHat i)))
            (HighamBench.p16FixedForwardFloor run i)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P16FixedMixedPrecisionGMRESRun n)
  (hLambda :
    ∀ (i : Nat),
      And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HighamBench.p16FixedMixedContraction n run i))
        (@LT.lt.{0} Real Real.instLT (@HighamBench.p16FixedMixedContraction n run i)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  And
    (∀ (i : Nat),
      @LE.le.{0} Real Real.instLE
        (@HighamBench.p16BackwardError n (@HighamBench.P16FixedMixedPrecisionGMRESRun.A n run)
          (@HighamBench.P16FixedMixedPrecisionGMRESRun.b n run)
          (@HighamBench.P16FixedMixedPrecisionGMRESRun.xHat n run
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p16FixedMixedContraction n run i)
            (@HighamBench.p16BackwardError n (@HighamBench.P16FixedMixedPrecisionGMRESRun.A n run)
              (@HighamBench.P16FixedMixedPrecisionGMRESRun.b n run)
              (@HighamBench.P16FixedMixedPrecisionGMRESRun.xHat n run i)))
          (@HighamBench.p16FixedBackwardFloor n run i)))
    (∀ (i : Nat),
      @LE.le.{0} Real Real.instLE
        (@HighamBench.p16ForwardError n (@HighamBench.P16FixedMixedPrecisionGMRESRun.xExact n run)
          (@HighamBench.P16FixedMixedPrecisionGMRESRun.xHat n run
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p16FixedMixedContraction n run i)
            (@HighamBench.p16ForwardError n (@HighamBench.P16FixedMixedPrecisionGMRESRun.xExact n run)
              (@HighamBench.P16FixedMixedPrecisionGMRESRun.xHat n run i)))
          (@HighamBench.p16FixedForwardFloor n run i)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P16Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P16Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P16FixedMixedPrecisionGMRESRun`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `55036cd282f86279334ebb1a10162482fa61b9f352a4a8453759143a45c0fe7b`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D002: `HighamBench.P16FixedMixedPrecisionGMRESRun.A`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `84464cc71c0fd1a362e81b05cab85669d9eb3a9507de46b49c9701b8a07df37a`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → HighamBench.P16Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → HighamBench.P16Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D003: `HighamBench.P16FixedMixedPrecisionGMRESRun.b`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c3218555d4b8c371a555c60c671d8f5b1eebe37e0018715ce24bb4807b9824e4`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D004: `HighamBench.P16FixedMixedPrecisionGMRESRun.xExact`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8cd1649b7fdb35e870a6d9f4b671662fb75051335be59c09047c8c6078123b75`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D005: `HighamBench.P16FixedMixedPrecisionGMRESRun.xHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ea45c0013c483a71dc307e984639752349c207a45d9bb0f356df067685086662`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Nat → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → Nat → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D006: `HighamBench.p16BackwardError`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f393da23f12434756d498c11e9e2ae4d991fc118a94873a36622b66697bd62ec`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (b xHat : HighamBench.P16Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat => HighamBench.p16NormalizedResidual A b xHat
```

### D007: `HighamBench.p16FixedBackwardFloor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6b6cba98f3ba81af9a2d606d6677d385e395ac9c15f4b8aa6c0f608c853e56a8`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P16FixedMixedPrecisionGMRESRun n) → (i : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i =>
  instHMul.hMul (HighamBench.p16PolynomialFactorValue run.dimensionFactor n (run.restart i).keyDimension) run.uHigh
```

### D008: `HighamBench.p16FixedForwardFloor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `33fa7f257832589b13de1acee9b711fd5615e9facf232c1b09ecc32283d80c64`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P16FixedMixedPrecisionGMRESRun n) → (i : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i =>
  instHMul.hMul
    (instHMul.hMul (HighamBench.p16PolynomialFactorValue run.dimensionFactor n (run.restart i).keyDimension) run.uHigh)
    (HighamBench.p16ConditionNumberF run.A run.Ainv)
```

### D009: `HighamBench.p16FixedMixedContraction`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `316c3a59e0189267214c1da75abdacad1f1605372ef86af17e95e797fe1c5047`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P16FixedMixedPrecisionGMRESRun n) → (i : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i =>
  instHMul.hMul
    (instHMul.hMul (HighamBench.p16PolynomialFactorValue run.dimensionFactor n (run.restart i).keyDimension) run.uLow)
    (HighamBench.p16ConditionNumberF run.A run.Ainv)
```

### D010: `HighamBench.p16ForwardError`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7ae31da5e50aa0dd2d17a75257cdee20c66bc769f6b0c93726fb999724b14518`

Type:

```lean
{n : Nat} → HighamBench.P16Vector n → HighamBench.P16Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x xHat : HighamBench.P16Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (HighamBench.p16VecNorm (instHSub.hSub xHat x)) (HighamBench.p16VecNorm x)
```

### D011: `HighamBench.P16FixedLowPrecisionMGSRestart.keyDimension`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b6d24b2924a893dca63fabb861a270154f5da47f8ee6df6534d493208656d336`

Type:

```lean
{n : Nat} →
  {A Ainv : HighamBench.P16Matrix n} →
    {b xExact xCurrent xNext residualHat correctionHat : HighamBench.P16Vector n} →
      {uLow : Real} →
        {dimensionFactor : HighamBench.P16PolynomialFactor} →
          HighamBench.P16FixedLowPrecisionMGSRestart A Ainv b xExact xCurrent xNext residualHat correctionHat uLow
              dimensionFactor →
            Nat
```

Fully explicit type:

```lean
{n : Nat} →
  {A Ainv : HighamBench.P16Matrix n} →
    {b xExact xCurrent xNext residualHat correctionHat : HighamBench.P16Vector n} →
      {uLow : Real} →
        {dimensionFactor : HighamBench.P16PolynomialFactor} →
          (self :
              @HighamBench.P16FixedLowPrecisionMGSRestart n A Ainv b xExact xCurrent xNext residualHat correctionHat
                uLow dimensionFactor) →
            Nat
```

Definition body (one-level semantic boundary):

```lean
fun n A Ainv b xExact xCurrent xNext residualHat correctionHat uLow dimensionFactor self => self.1
```

### D012: `HighamBench.P16FixedMixedPrecisionGMRESRun.Ainv`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d07c0f63ae9a843539c1635ea39da348fcc0c4fc74862aa8440c2324b850b7f8`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → HighamBench.P16Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → HighamBench.P16Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D013: `HighamBench.P16FixedMixedPrecisionGMRESRun.correctionHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `bb3cc0c11a9d0b31371bde7eb9f89e63d46dee6ca8de94a7b26ff816dc3ef679`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Nat → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → Nat → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.8
```

### D014: `HighamBench.P16FixedMixedPrecisionGMRESRun.dimensionFactor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `071586e1ccfd1074831c4f7fc30965b71c6d9978d86013ed6233eac3633f6b1f`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → HighamBench.P16PolynomialFactor
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → HighamBench.P16PolynomialFactor
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.13
```

### D015: `HighamBench.P16FixedMixedPrecisionGMRESRun.mk`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `a4f7700cb5a7a147f8ef1977d4e87ec0a7dc93a37c2a97744cc6bb497481d1e2`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv : HighamBench.P16Matrix n) →
      (b xExact : HighamBench.P16Vector n) →
        (xHat residualHat correctionHat residualError updateError : Nat → HighamBench.P16Vector n) →
          (uHigh uLow : Real) →
            (dimensionFactor : HighamBench.P16PolynomialFactor) →
              Ne b 0 →
                HighamBench.p16IsNonsingular A →
                  (∀ (z : HighamBench.P16Vector n), Eq (HighamBench.p16MatVec Ainv (HighamBench.p16MatVec A z)) z) →
                    (∀ (z : HighamBench.P16Vector n), Eq (HighamBench.p16MatVec A (HighamBench.p16MatVec Ainv z)) z) →
                      Eq (HighamBench.p16MatVec A xExact) b →
                        Real.instLT.lt 0 uHigh →
                          Real.instLT.lt 0 uLow →
                            (∀ (i : Nat),
                                Eq (residualHat i)
                                  (instHAdd.hAdd (HighamBench.p16Residual A b (xHat i)) (residualError i))) →
                              (∀ (i : Nat) (j : Fin n),
                                  Real.instLE.le (abs (residualError i j))
                                    (instHMul.hMul (HighamBench.gamma uHigh n)
                                      (instHAdd.hAdd (abs (b j))
                                        (HighamBench.p16MatVec (fun row col => abs (A row col))
                                          (fun col => abs (xHat i col)) j)))) →
                                (∀ (i : Nat),
                                    Eq (xHat (instHAdd.hAdd i 1))
                                      (instHAdd.hAdd (instHAdd.hAdd (xHat i) (correctionHat i)) (updateError i))) →
                                  (∀ (i : Nat) (j : Fin n),
                                      Real.instLE.le (abs (updateError i j))
                                        (instHMul.hMul uHigh (abs (xHat (instHAdd.hAdd i 1) j)))) →
                                    (restart :
                                        (i : Nat) →
                                          HighamBench.P16FixedLowPrecisionMGSRestart A Ainv b xExact (xHat i)
                                            (xHat (instHAdd.hAdd i 1)) (residualHat i) (correctionHat i) uLow
                                            dimensionFactor) →
                                      (∀ (i : Nat),
                                          Real.instLE.le
                                            (instHDiv.hDiv
                                              (instHAdd.hAdd (HighamBench.p16VecNorm (residualError i))
                                                (HighamBench.p16VecNorm (HighamBench.p16MatVec A (updateError i))))
                                              (instHAdd.hAdd (HighamBench.p16VecNorm b)
                                                (instHMul.hMul (HighamBench.p16FrobNorm A)
                                                  (HighamBench.p16VecNorm (xHat (instHAdd.hAdd i 1))))))
                                            (instHMul.hMul
                                              (HighamBench.p16PolynomialFactorValue dimensionFactor n
                                                (restart i).keyDimension)
                                              uHigh)) →
                                        (∀ (i : Nat),
                                            Real.instLE.le
                                              (instHDiv.hDiv (HighamBench.p16VecNorm (updateError i))
                                                (HighamBench.p16VecNorm xExact))
                                              (instHMul.hMul
                                                (instHMul.hMul
                                                  (HighamBench.p16PolynomialFactorValue dimensionFactor n
                                                    (restart i).keyDimension)
                                                  uHigh)
                                                (HighamBench.p16ConditionNumberF A Ainv))) →
                                          HighamBench.P16FixedMixedPrecisionGMRESRun n
```

Fully explicit type:

```lean
{n : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (A Ainv : HighamBench.P16Matrix n) →
      (b xExact : HighamBench.P16Vector n) →
        (xHat residualHat correctionHat residualError updateError : Nat → HighamBench.P16Vector n) →
          (uHigh uLow : Real) →
            (dimensionFactor : HighamBench.P16PolynomialFactor) →
              (b_nonzero :
                  @Ne.{1} (HighamBench.P16Vector n) b
                    (@OfNat.ofNat.{0} (HighamBench.P16Vector n) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (HighamBench.P16Vector n)
                        (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero)))) →
                (nonsingular : @HighamBench.p16IsNonsingular n A) →
                  (left_inverse_action :
                      ∀ (z : HighamBench.P16Vector n),
                        @Eq.{1} (HighamBench.P16Vector n) (@HighamBench.p16MatVec n Ainv (@HighamBench.p16MatVec n A z))
                          z) →
                    (right_inverse_action :
                        ∀ (z : HighamBench.P16Vector n),
                          @Eq.{1} (HighamBench.P16Vector n)
                            (@HighamBench.p16MatVec n A (@HighamBench.p16MatVec n Ainv z)) z) →
                      (exact_solution : @Eq.{1} (HighamBench.P16Vector n) (@HighamBench.p16MatVec n A xExact) b) →
                        (uHigh_pos :
                            @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uHigh) →
                          (uLow_pos :
                              @LT.lt.{0} Real Real.instLT
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uLow) →
                            (residual_equation :
                                ∀ (i : Nat),
                                  @Eq.{1} (HighamBench.P16Vector n) (residualHat i)
                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                      (HighamBench.P16Vector n)
                                      (@instHAdd.{0} (HighamBench.P16Vector n)
                                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                          Real.instAdd))
                                      (@HighamBench.p16Residual n A b (xHat i)) (residualError i))) →
                              (residual_error_bound :
                                  ∀ (i : Nat) (j : Fin n),
                                    @LE.le.{0} Real Real.instLE
                                      (@abs.{0} Real Real.lattice Real.instAddGroup (residualError i j))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (HighamBench.gamma uHigh n)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@abs.{0} Real Real.lattice Real.instAddGroup (b j))
                                          (@HighamBench.p16MatVec n
                                            (fun (row col : Fin n) =>
                                              @abs.{0} Real Real.lattice Real.instAddGroup (A row col))
                                            (fun (col : Fin n) =>
                                              @abs.{0} Real Real.lattice Real.instAddGroup (xHat i col))
                                            j)))) →
                                (update_equation :
                                    ∀ (i : Nat),
                                      @Eq.{1} (HighamBench.P16Vector n)
                                        (xHat
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                          (HighamBench.P16Vector n)
                                          (@instHAdd.{0} (HighamBench.P16Vector n)
                                            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                              Real.instAdd))
                                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                            (HighamBench.P16Vector n)
                                            (@instHAdd.{0} (HighamBench.P16Vector n)
                                              (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                Real.instAdd))
                                            (xHat i) (correctionHat i))
                                          (updateError i))) →
                                  (update_error_bound :
                                      ∀ (i : Nat) (j : Fin n),
                                        @LE.le.{0} Real Real.instLE
                                          (@abs.{0} Real Real.lattice Real.instAddGroup (updateError i j))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) uHigh
                                            (@abs.{0} Real Real.lattice Real.instAddGroup
                                              (xHat
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                j)))) →
                                    (restart :
                                        (i : Nat) →
                                          @HighamBench.P16FixedLowPrecisionMGSRestart n A Ainv b xExact (xHat i)
                                            (xHat
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (residualHat i) (correctionHat i) uLow dimensionFactor) →
                                      (backward_high_roundoff_bound :
                                          ∀ (i : Nat),
                                            @LE.le.{0} Real Real.instLE
                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                (@instHDiv.{0} Real
                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HighamBench.p16VecNorm n (residualError i))
                                                  (@HighamBench.p16VecNorm n
                                                    (@HighamBench.p16MatVec n A (updateError i))))
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HighamBench.p16VecNorm n b)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HighamBench.p16FrobNorm n A)
                                                    (@HighamBench.p16VecNorm n
                                                      (xHat
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          i
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))))))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (HighamBench.p16PolynomialFactorValue dimensionFactor n
                                                  (@HighamBench.P16FixedLowPrecisionMGSRestart.keyDimension n A Ainv b
                                                    xExact (xHat i)
                                                    (xHat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (residualHat i) (correctionHat i) uLow dimensionFactor (restart i)))
                                                uHigh)) →
                                        (forward_high_roundoff_bound :
                                            ∀ (i : Nat),
                                              @LE.le.{0} Real Real.instLE
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@HighamBench.p16VecNorm n (updateError i))
                                                  (@HighamBench.p16VecNorm n xExact))
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (HighamBench.p16PolynomialFactorValue dimensionFactor n
                                                      (@HighamBench.P16FixedLowPrecisionMGSRestart.keyDimension n A Ainv
                                                        b xExact (xHat i)
                                                        (xHat
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) i
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (residualHat i) (correctionHat i) uLow dimensionFactor
                                                        (restart i)))
                                                    uHigh)
                                                  (@HighamBench.p16ConditionNumberF n A Ainv))) →
                                          HighamBench.P16FixedMixedPrecisionGMRESRun n
```

### D016: `HighamBench.P16FixedMixedPrecisionGMRESRun.residualHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `01dc025f8feb9aaf3fff835b4bf492e284251a0ee8037e7f3454275d3a2f172c`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Nat → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → Nat → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D017: `HighamBench.P16FixedMixedPrecisionGMRESRun.restart`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5a4a27017683ac836401a6e45b02b40a61dcd7039e2bb5765c500a6cd9681cf3`

Type:

```lean
{n : Nat} →
  (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) →
    (i : Nat) →
      HighamBench.P16FixedLowPrecisionMGSRestart self.A self.Ainv self.b self.xExact (self.xHat i)
        (self.xHat (instHAdd.hAdd i 1)) (self.residualHat i) (self.correctionHat i) self.uLow self.dimensionFactor
```

Fully explicit type:

```lean
{n : Nat} →
  (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) →
    (i : Nat) →
      @HighamBench.P16FixedLowPrecisionMGSRestart n (@HighamBench.P16FixedMixedPrecisionGMRESRun.A n self)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.Ainv n self) (@HighamBench.P16FixedMixedPrecisionGMRESRun.b n self)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.xExact n self)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.xHat n self i)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.xHat n self
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.residualHat n self i)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.correctionHat n self i)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.uLow n self)
        (@HighamBench.P16FixedMixedPrecisionGMRESRun.dimensionFactor n self)
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.25
```

### D018: `HighamBench.P16FixedMixedPrecisionGMRESRun.uHigh`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cd2ac4d493bb1bd1edb37aa4f91b6d7f69ccecfc8b787056575f25ba026d51d4`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.11
```

### D019: `HighamBench.P16FixedMixedPrecisionGMRESRun.uLow`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c1aeef9945c0840f4393dbb63df4e40b51a227703ebb844878da8252c84a3753`

Type:

```lean
{n : Nat} → HighamBench.P16FixedMixedPrecisionGMRESRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P16FixedMixedPrecisionGMRESRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.12
```

### D020: `HighamBench.P16Matrix`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `36b086346c3347b53ec18d195e2ddb2540e7ae44e2039744f1587ecb712cd8f4`

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

### D021: `HighamBench.P16Vector`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b643f0f6e4b56118846938b88a1ae79ef2b1849df9e9a3440a9ac88a10e94782`

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

### D022: `HighamBench.p16ConditionNumberF`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aad128e1ff242bef74849f83be7b08fd1b3bf6883dc807497f55a0fff18e7456`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : HighamBench.P16Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (HighamBench.p16FrobNorm Ainv) (HighamBench.p16FrobNorm A)
```

### D023: `HighamBench.p16NormalizedResidual`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fcb08c14cdc1ff672554092cd5e6a93c5458a19a318e4c8f88e0e1ba2906b439`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (b xHat : HighamBench.P16Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat =>
  instHDiv.hDiv (HighamBench.p16VecNorm (HighamBench.p16Residual A b xHat))
    (instHAdd.hAdd (instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16VecNorm xHat)) (HighamBench.p16VecNorm b))
```

### D024: `HighamBench.p16PolynomialFactorValue`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `760fbb54d1bbc51a3cb9ef42d3d96bd053f7f673cb6af6cf627e47cd48d589c8`

Type:

```lean
HighamBench.P16PolynomialFactor → Nat → Nat → Real
```

Fully explicit type:

```lean
(c : HighamBench.P16PolynomialFactor) → (n k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun c n k =>
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      instHMul.hMul (instHMul.hMul (c.coefficient i j) (instHPow.hPow n.cast i.val)) (instHPow.hPow k.cast j.val)
```

### D025: `HighamBench.p16VecNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `bd8e44de2b8f8d577e4ee9f3b2ffb202461eebd6324f041a2f505422a111cd66`

Type:

```lean
{n : Nat} → HighamBench.P16Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : HighamBench.P16Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D026: `HighamBench.P16FixedLowPrecisionMGSRestart`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `ef96102c5a351e15c93f9f3b2615d84519d59e8df25f12207ed9f0dd8d033a2b`

Type:

```lean
{n : Nat} →
  HighamBench.P16Matrix n →
    HighamBench.P16Matrix n →
      HighamBench.P16Vector n →
        HighamBench.P16Vector n →
          HighamBench.P16Vector n →
            HighamBench.P16Vector n →
              HighamBench.P16Vector n → HighamBench.P16Vector n → Real → HighamBench.P16PolynomialFactor → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (A Ainv : HighamBench.P16Matrix n) →
    (b xExact xCurrent xNext residualHat correctionHat : HighamBench.P16Vector n) →
      (uLow : Real) → (dimensionFactor : HighamBench.P16PolynomialFactor) → Type
```

### D027: `HighamBench.P16PolynomialFactor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `0433df59d966012b968702b4ffc0dcd8fdc1b3177eecb14ee31bad2fde29f36b`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D028: `HighamBench.P16PolynomialFactor.coefficient`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `eda434f64be08a0d479423cd695893c35f43716004402939d12da0a364fa58e8`

Type:

```lean
(self : HighamBench.P16PolynomialFactor) →
  Fin (instHAdd.hAdd self.degreeN 1) → Fin (instHAdd.hAdd self.degreeK 1) → Real
```

Fully explicit type:

```lean
(self : HighamBench.P16PolynomialFactor) →
  Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (HighamBench.P16PolynomialFactor.degreeN self)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (HighamBench.P16PolynomialFactor.degreeK self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D029: `HighamBench.P16PolynomialFactor.degreeK`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `df1d28debd8bd57641958e5b2f067565cdd35a656575ec77fff53a44cad5cf95`

Type:

```lean
HighamBench.P16PolynomialFactor → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P16PolynomialFactor) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D030: `HighamBench.P16PolynomialFactor.degreeN`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7535abaa99860d41d600e1a9051ecb7967df3e56b9a83219b1c10ca2f6988dea`

Type:

```lean
HighamBench.P16PolynomialFactor → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P16PolynomialFactor) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D031: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f15d03b13b3e456f86c0d1afbecf5720b016231e8755a130fe4ff7bf44902bf0`

Type:

```lean
Real → Nat → Real
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n => instHDiv.hDiv (instHMul.hMul n.cast u) (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D032: `HighamBench.p16FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8d9bc1fb5d3aea537c8f14c86cc475e387a8c8a49dd453f1e630adb1f5aff2bd`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.frobeniusNormedRing.norm A
```

### D033: `HighamBench.p16IsNonsingular`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `85b5f4df299401a78ff2042ddbaff615a4f2e4dd7ac6d5eeddc8091ccb86d714`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Function.Bijective (HighamBench.p16MatVec A)
```

### D034: `HighamBench.p16MatVec`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `633fcb3583fab70e7665e594e28a11707a692d4c14a396ea9eeda2a3724f56b9`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (x : HighamBench.P16Vector n) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D035: `HighamBench.p16Residual`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b6efd2406b4d95a62ec33a870000fff88d929437b9b4152b36fbbe02063a3602`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (b x : HighamBench.P16Vector n) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b x => instHSub.hSub b (HighamBench.p16MatVec A x)
```

### D036: `HighamBench.P16FixedLowPrecisionMGSRestart.mk`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `07bacd38e362571eb077eebfe28d72a7443e868d3cfd169ed07d43617fdf5172`

Type:

```lean
{n : Nat} →
  {A Ainv : HighamBench.P16Matrix n} →
    {b xExact xCurrent xNext residualHat correctionHat : HighamBench.P16Vector n} →
      {uLow : Real} →
        {dimensionFactor : HighamBench.P16PolynomialFactor} →
          (keyDimension : Nat) →
            instLTNat.lt 0 keyDimension →
              instLENat.le keyDimension n →
                (basis : HighamBench.P16RectMatrix n keyDimension) →
                  (basisNext : HighamBench.P16RectMatrix n (instHAdd.hAdd keyDimension 1)) →
                    (hessenberg : HighamBench.P16RectMatrix (instHAdd.hAdd keyDimension 1) keyDimension) →
                      (arnoldiProduct arnoldiProductError : HighamBench.P16RectMatrix n keyDimension) →
                        Eq arnoldiProduct (instHAdd.hAdd (HighamBench.p16SquareRectMul A basis) arnoldiProductError) →
                          (∀ (row : Fin n) (col : Fin keyDimension), Eq (basis row col) (basisNext row col.castSucc)) →
                            (mgsWork : Fin keyDimension → Nat → HighamBench.P16Vector n) →
                              (mgsProjectionError : Fin keyDimension → Fin keyDimension → Real) →
                                (mgsUpdateError : Fin keyDimension → Fin keyDimension → HighamBench.P16Vector n) →
                                  (mgsNormalizationError : Fin keyDimension → HighamBench.P16Vector n) →
                                    (∀ (j : Fin keyDimension) (row : Fin n),
                                        Eq (mgsWork j 0 row) (arnoldiProduct row j)) →
                                      (∀ (j q : Fin keyDimension),
                                          instLENat.le q.val j.val →
                                            Eq (hessenberg q.castSucc j)
                                              (instHAdd.hAdd
                                                (Finset.univ.sum fun row =>
                                                  instHMul.hMul (basisNext row q.castSucc) (mgsWork j q.val row))
                                                (mgsProjectionError j q))) →
                                        (∀ (j q : Fin keyDimension),
                                            instLENat.le q.val j.val →
                                              Real.instLE.le (abs (mgsProjectionError j q))
                                                (instHMul.hMul (HighamBench.gamma uLow n)
                                                  (Finset.univ.sum fun row =>
                                                    abs
                                                      (instHMul.hMul (basisNext row q.castSucc)
                                                        (mgsWork j q.val row))))) →
                                          (∀ (j q : Fin keyDimension),
                                              instLENat.le q.val j.val →
                                                Eq (mgsWork j (instHAdd.hAdd q.val 1))
                                                  (instHAdd.hAdd
                                                    (instHSub.hSub (mgsWork j q.val) fun row =>
                                                      instHMul.hMul (hessenberg q.castSucc j)
                                                        (basisNext row q.castSucc))
                                                    (mgsUpdateError j q))) →
                                            (∀ (j q : Fin keyDimension),
                                                instLENat.le q.val j.val →
                                                  Real.instLE.le (HighamBench.p16VecNorm (mgsUpdateError j q))
                                                    (instHMul.hMul uLow
                                                      (instHAdd.hAdd (HighamBench.p16VecNorm (mgsWork j q.val))
                                                        (instHMul.hMul (abs (hessenberg q.castSucc j))
                                                          (HighamBench.p16VecNorm fun row =>
                                                            basisNext row q.castSucc))))) →
                                              (∀ (j : Fin keyDimension),
                                                  Eq
                                                    (fun row =>
                                                      instHMul.hMul (hessenberg j.succ j) (basisNext row j.succ))
                                                    (instHAdd.hAdd (mgsWork j (instHAdd.hAdd j.val 1))
                                                      (mgsNormalizationError j))) →
                                                (∀ (j : Fin keyDimension),
                                                    Real.instLE.le (HighamBench.p16VecNorm (mgsNormalizationError j))
                                                      (instHMul.hMul uLow
                                                        (HighamBench.p16VecNorm (mgsWork j (instHAdd.hAdd j.val 1))))) →
                                                  (epsilonC epsilonB epsilonLS epsilonX : Real) →
                                                    (residualLow residualCastError : HighamBench.P16Vector n) →
                                                      Eq residualLow (instHAdd.hAdd residualHat residualCastError) →
                                                        Real.instLE.le (HighamBench.p16VecNorm residualCastError)
                                                            (instHMul.hMul uLow (HighamBench.p16VecNorm residualHat)) →
                                                          (residualNorm : Real) →
                                                            Eq residualNorm (HighamBench.p16VecNorm residualLow) →
                                                              (∀ (row : Fin n),
                                                                  Eq (residualLow row)
                                                                    (instHMul.hMul residualNorm (basisNext row 0))) →
                                                                Eq epsilonB uLow →
                                                                  Real.instLE.le
                                                                      (HighamBench.p16RectFrobNorm arnoldiProductError)
                                                                      (instHMul.hMul epsilonC
                                                                        (HighamBench.p16RectFrobNorm
                                                                          (HighamBench.p16SquareRectMul A basis))) →
                                                                    (leastSquaresRhsError : HighamBench.P16Vector n) →
                                                                      (leastSquaresMatrixError :
                                                                          HighamBench.P16RectMatrix n keyDimension) →
                                                                        (leastSquaresY :
                                                                            HighamBench.P16Vector keyDimension) →
                                                                          HighamBench.p16IsLeastSquaresSolution
                                                                              (instHAdd.hAdd arnoldiProduct
                                                                                leastSquaresMatrixError)
                                                                              (instHAdd.hAdd residualLow
                                                                                leastSquaresRhsError)
                                                                              leastSquaresY →
                                                                            (∀ (j : Fin (instHAdd.hAdd keyDimension 1)),
                                                                                Real.instLE.le
                                                                                  (HighamBench.p16VecNorm
                                                                                    (HighamBench.p16AugmentedColumn
                                                                                      leastSquaresRhsError
                                                                                      leastSquaresMatrixError j))
                                                                                  (instHMul.hMul epsilonLS
                                                                                    (HighamBench.p16VecNorm
                                                                                      (HighamBench.p16AugmentedColumn
                                                                                        residualLow arnoldiProduct
                                                                                        j)))) →
                                                                              (correctionFormationError :
                                                                                  HighamBench.P16Vector n) →
                                                                                Eq correctionHat
                                                                                    (instHAdd.hAdd
                                                                                      (HighamBench.p16RectMatVec basis
                                                                                        leastSquaresY)
                                                                                      correctionFormationError) →
                                                                                  Real.instLE.le
                                                                                      (HighamBench.p16VecNorm
                                                                                        correctionFormationError)
                                                                                      (instHMul.hMul
                                                                                        (instHMul.hMul epsilonX
                                                                                          (HighamBench.p16RectFrobNorm
                                                                                            basis))
                                                                                        (HighamBench.p16VecNorm
                                                                                          leastSquaresY)) →
                                                                                    And (Real.instLE.le 0 epsilonC)
                                                                                        (And (Real.instLE.le 0 epsilonB)
                                                                                          (And
                                                                                            (Real.instLE.le 0 epsilonLS)
                                                                                            (Real.instLE.le 0
                                                                                              epsilonX))) →
                                                                                      (productWeight leastSquaresWeight
                                                                                          correctionWeight : Real) →
                                                                                        And
                                                                                            (Real.instLE.le 0
                                                                                              productWeight)
                                                                                            (And
                                                                                              (Real.instLE.le 0
                                                                                                leastSquaresWeight)
                                                                                              (Real.instLE.le 0
                                                                                                correctionWeight)) →
                                                                                          Real.instLE.le epsilonC
                                                                                              (instHMul.hMul
                                                                                                productWeight uLow) →
                                                                                            Real.instLE.le epsilonLS
                                                                                                (instHMul.hMul
                                                                                                  leastSquaresWeight
                                                                                                  uLow) →
                                                                                              Real.instLE.le epsilonX
                                                                                                  (instHMul.hMul
                                                                                                    correctionWeight
                                                                                                    uLow) →
                                                                                                (basisLowerGain
                                                                                                    imageLowerGain :
                                                                                                    Real) →
                                                                                                  Real.instLT.lt 0
                                                                                                      basisLowerGain →
                                                                                                    HighamBench.p16MinGainAtLeast
                                                                                                        basis
                                                                                                        basisLowerGain →
                                                                                                      ⋯
```

Fully explicit type:

```lean
{n : Nat} →
  {A Ainv : HighamBench.P16Matrix n} →
    {b xExact xCurrent xNext residualHat correctionHat : HighamBench.P16Vector n} →
      {uLow : Real} →
        {dimensionFactor : HighamBench.P16PolynomialFactor} →
          (keyDimension : Nat) →
            (keyDimension_pos :
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) keyDimension) →
              (keyDimension_le : @LE.le.{0} Nat instLENat keyDimension n) →
                (basis : HighamBench.P16RectMatrix n keyDimension) →
                  (basisNext :
                      HighamBench.P16RectMatrix n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    (hessenberg :
                        HighamBench.P16RectMatrix
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          keyDimension) →
                      (arnoldiProduct arnoldiProductError : HighamBench.P16RectMatrix n keyDimension) →
                        (arnoldi_product_equation :
                            @Eq.{1} (HighamBench.P16RectMatrix n keyDimension) arnoldiProduct
                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16RectMatrix n keyDimension)
                                (HighamBench.P16RectMatrix n keyDimension) (HighamBench.P16RectMatrix n keyDimension)
                                (@instHAdd.{0} (HighamBench.P16RectMatrix n keyDimension)
                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin keyDimension) Real Real.instAdd))
                                (@HighamBench.p16SquareRectMul n keyDimension A basis) arnoldiProductError)) →
                          (basis_fully_stored :
                              ∀ (row : Fin n) (col : Fin keyDimension),
                                @Eq.{1} Real (basis row col) (basisNext row (@Fin.castSucc keyDimension col))) →
                            (mgsWork : Fin keyDimension → Nat → HighamBench.P16Vector n) →
                              (mgsProjectionError : Fin keyDimension → Fin keyDimension → Real) →
                                (mgsUpdateError : Fin keyDimension → Fin keyDimension → HighamBench.P16Vector n) →
                                  (mgsNormalizationError : Fin keyDimension → HighamBench.P16Vector n) →
                                    (mgs_work_initial :
                                        ∀ (j : Fin keyDimension) (row : Fin n),
                                          @Eq.{1} Real
                                            (mgsWork j (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                              row)
                                            (arnoldiProduct row j)) →
                                      (mgs_projection :
                                          ∀ (j q : Fin keyDimension),
                                            @LE.le.{0} Nat instLENat (@Fin.val keyDimension q)
                                                (@Fin.val keyDimension j) →
                                              @Eq.{1} Real (hessenberg (@Fin.castSucc keyDimension q) j)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid
                                                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (row : Fin n) =>
                                                    @HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (basisNext row (@Fin.castSucc keyDimension q))
                                                      (mgsWork j (@Fin.val keyDimension q) row))
                                                  (mgsProjectionError j q))) →
                                        (mgs_projection_error_bound :
                                            ∀ (j q : Fin keyDimension),
                                              @LE.le.{0} Nat instLENat (@Fin.val keyDimension q)
                                                  (@Fin.val keyDimension j) →
                                                @LE.le.{0} Real Real.instLE
                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                    (mgsProjectionError j q))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (HighamBench.gamma uLow n)
                                                    (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid
                                                      (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (row : Fin n) =>
                                                      @abs.{0} Real Real.lattice Real.instAddGroup
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (basisNext row (@Fin.castSucc keyDimension q))
                                                          (mgsWork j (@Fin.val keyDimension q) row))))) →
                                          (mgs_update :
                                              ∀ (j q : Fin keyDimension),
                                                @LE.le.{0} Nat instLENat (@Fin.val keyDimension q)
                                                    (@Fin.val keyDimension j) →
                                                  @Eq.{1} (HighamBench.P16Vector n)
                                                    (mgsWork j
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Fin.val keyDimension q)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                      (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                      (@instHAdd.{0} (HighamBench.P16Vector n)
                                                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                          fun (i : Fin n) => Real.instAdd))
                                                      (@HSub.hSub.{0, 0, 0} (HighamBench.P16Vector n)
                                                        ((row : Fin n) → Real) (HighamBench.P16Vector n)
                                                        (@instHSub.{0} (HighamBench.P16Vector n)
                                                          (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                            fun (i : Fin n) => Real.instSub))
                                                        (mgsWork j (@Fin.val keyDimension q)) fun (row : Fin n) =>
                                                        @HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (hessenberg (@Fin.castSucc keyDimension q) j)
                                                          (basisNext row (@Fin.castSucc keyDimension q)))
                                                      (mgsUpdateError j q))) →
                                            (mgs_update_error_bound :
                                                ∀ (j q : Fin keyDimension),
                                                  @LE.le.{0} Nat instLENat (@Fin.val keyDimension q)
                                                      (@Fin.val keyDimension j) →
                                                    @LE.le.{0} Real Real.instLE
                                                      (@HighamBench.p16VecNorm n (mgsUpdateError j q))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) uLow
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@HighamBench.p16VecNorm n
                                                            (mgsWork j (@Fin.val keyDimension q)))
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (@abs.{0} Real Real.lattice Real.instAddGroup
                                                              (hessenberg (@Fin.castSucc keyDimension q) j))
                                                            (@HighamBench.p16VecNorm n fun (row : Fin n) =>
                                                              basisNext row (@Fin.castSucc keyDimension q)))))) →
                                              (mgs_normalization :
                                                  ∀ (j : Fin keyDimension),
                                                    @Eq.{1} ((row : Fin n) → Real)
                                                      (fun (row : Fin n) =>
                                                        @HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (hessenberg (@Fin.succ keyDimension j) j)
                                                          (basisNext row (@Fin.succ keyDimension j)))
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                        (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                        (@instHAdd.{0} (HighamBench.P16Vector n)
                                                          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                            fun (i : Fin n) => Real.instAdd))
                                                        (mgsWork j
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) (@Fin.val keyDimension j)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (mgsNormalizationError j))) →
                                                (mgs_normalization_error_bound :
                                                    ∀ (j : Fin keyDimension),
                                                      @LE.le.{0} Real Real.instLE
                                                        (@HighamBench.p16VecNorm n (mgsNormalizationError j))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) uLow
                                                          (@HighamBench.p16VecNorm n
                                                            (mgsWork j
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) (@Fin.val keyDimension j)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))))) →
                                                  (epsilonC epsilonB epsilonLS epsilonX : Real) →
                                                    (residualLow residualCastError : HighamBench.P16Vector n) →
                                                      (residual_cast_equation :
                                                          @Eq.{1} (HighamBench.P16Vector n) residualLow
                                                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                              (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                              (@instHAdd.{0} (HighamBench.P16Vector n)
                                                                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                                  fun (i : Fin n) => Real.instAdd))
                                                              residualHat residualCastError)) →
                                                        (residual_cast_bound :
                                                            @LE.le.{0} Real Real.instLE
                                                              (@HighamBench.p16VecNorm n residualCastError)
                                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                (@instHMul.{0} Real Real.instMul) uLow
                                                                (@HighamBench.p16VecNorm n residualHat))) →
                                                          (residualNorm : Real) →
                                                            (residualNorm_eq :
                                                                @Eq.{1} Real residualNorm
                                                                  (@HighamBench.p16VecNorm n residualLow)) →
                                                              (residual_starts_basis :
                                                                  ∀ (row : Fin n),
                                                                    @Eq.{1} Real (residualLow row)
                                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                        (@instHMul.{0} Real Real.instMul) residualNorm
                                                                        (basisNext row
                                                                          (@OfNat.ofNat.{0}
                                                                            (Fin
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat)
                                                                                keyDimension
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                  (instOfNatNat (nat_lit 1)))))
                                                                            (nat_lit 0)
                                                                            (@Fin.instOfNat
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat)
                                                                                keyDimension
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                  (instOfNatNat (nat_lit 1))))
                                                                              (@instNeZeroNatHAdd_1 keyDimension
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                  (instOfNatNat (nat_lit 1)))
                                                                                (@Nat.instNeZeroSucc
                                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                                    (instOfNatNat (nat_lit 0)))))
                                                                              (nat_lit 0)))))) →
                                                                (epsilonB_eq : @Eq.{1} Real epsilonB uLow) →
                                                                  (product_error_bound :
                                                                      @LE.le.{0} Real Real.instLE
                                                                        (@HighamBench.p16RectFrobNorm n keyDimension
                                                                          arnoldiProductError)
                                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                          (@instHMul.{0} Real Real.instMul) epsilonC
                                                                          (@HighamBench.p16RectFrobNorm n keyDimension
                                                                            (@HighamBench.p16SquareRectMul n
                                                                              keyDimension A basis)))) →
                                                                    (leastSquaresRhsError : HighamBench.P16Vector n) →
                                                                      (leastSquaresMatrixError :
                                                                          HighamBench.P16RectMatrix n keyDimension) →
                                                                        (leastSquaresY :
                                                                            HighamBench.P16Vector keyDimension) →
                                                                          (least_squares_solution :
                                                                              @HighamBench.p16IsLeastSquaresSolution n
                                                                                keyDimension
                                                                                (@HAdd.hAdd.{0, 0, 0}
                                                                                  (HighamBench.P16RectMatrix n
                                                                                    keyDimension)
                                                                                  (HighamBench.P16RectMatrix n
                                                                                    keyDimension)
                                                                                  (HighamBench.P16RectMatrix n
                                                                                    keyDimension)
                                                                                  (@instHAdd.{0}
                                                                                    (HighamBench.P16RectMatrix n
                                                                                      keyDimension)
                                                                                    (@Matrix.add.{0, 0, 0} (Fin n)
                                                                                      (Fin keyDimension) Real
                                                                                      Real.instAdd))
                                                                                  arnoldiProduct
                                                                                  leastSquaresMatrixError)
                                                                                (@HAdd.hAdd.{0, 0, 0}
                                                                                  (HighamBench.P16Vector n)
                                                                                  (HighamBench.P16Vector n)
                                                                                  (HighamBench.P16Vector n)
                                                                                  (@instHAdd.{0}
                                                                                    (HighamBench.P16Vector n)
                                                                                    (@Pi.instAdd.{0, 0} (Fin n)
                                                                                      (fun (a : Fin n) => Real)
                                                                                      fun (i : Fin n) => Real.instAdd))
                                                                                  residualLow leastSquaresRhsError)
                                                                                leastSquaresY) →
                                                                            (least_squares_column_bound :
                                                                                ∀
                                                                                  (j :
                                                                                    Fin
                                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                        (@instHAdd.{0} Nat instAddNat)
                                                                                        keyDimension
                                                                                        (@OfNat.ofNat.{0} Nat
                                                                                          (nat_lit 1)
                                                                                          (instOfNatNat (nat_lit 1))))),
                                                                                  @LE.le.{0} Real Real.instLE
                                                                                    (@HighamBench.p16VecNorm n
                                                                                      (@HighamBench.p16AugmentedColumn n
                                                                                        keyDimension
                                                                                        leastSquaresRhsError
                                                                                        leastSquaresMatrixError j))
                                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                      (@instHMul.{0} Real Real.instMul)
                                                                                      epsilonLS
                                                                                      (@HighamBench.p16VecNorm n
                                                                                        (@HighamBench.p16AugmentedColumn
                                                                                          n keyDimension residualLow
                                                                                          arnoldiProduct j)))) →
                                                                              (correctionFormationError :
                                                                                  HighamBench.P16Vector n) →
                                                                                (correction_formation_equation :
                                                                                    @Eq.{1} (HighamBench.P16Vector n)
                                                                                      correctionHat
                                                                                      (@HAdd.hAdd.{0, 0, 0}
                                                                                        (HighamBench.P16Vector n)
                                                                                        (HighamBench.P16Vector n)
                                                                                        (HighamBench.P16Vector n)
                                                                                        (@instHAdd.{0}
                                                                                          (HighamBench.P16Vector n)
                                                                                          (@Pi.instAdd.{0, 0} (Fin n)
                                                                                            (fun (a : Fin n) => Real)
                                                                                            fun (i : Fin n) =>
                                                                                            Real.instAdd))
                                                                                        (@HighamBench.p16RectMatVec n
                                                                                          keyDimension basis
                                                                                          leastSquaresY)
                                                                                        correctionFormationError)) →
                                                                                  (correction_formation_bound :
                                                                                      @LE.le.{0} Real Real.instLE
                                                                                        (@HighamBench.p16VecNorm n
                                                                                          correctionFormationError)
                                                                                        (@HMul.hMul.{0, 0, 0} Real Real
                                                                                          Real
                                                                                          (@instHMul.{0} Real
                                                                                            Real.instMul)
                                                                                          (@HMul.hMul.{0, 0, 0} Real
                                                                                            Real Real
                                                                                            (@instHMul.{0} Real
                                                                                              Real.instMul)
                                                                                            epsilonX
                                                                                            (@HighamBench.p16RectFrobNorm
                                                                                              n keyDimension basis))
                                                                                          (@HighamBench.p16VecNorm
                                                                                            keyDimension
                                                                                            leastSquaresY))) →
                                                                                    (accuracy_nonneg :
                                                                                        And
                                                                                          (@LE.le.{0} Real Real.instLE
                                                                                            (@OfNat.ofNat.{0} Real
                                                                                              (nat_lit 0)
                                                                                              (@Zero.toOfNat0.{0} Real
                                                                                                Real.instZero))
                                                                                            epsilonC)
                                                                                          (And
                                                                                            (@LE.le.{0} Real Real.instLE
                                                                                              (@OfNat.ofNat.{0} Real
                                                                                                (nat_lit 0)
                                                                                                (@Zero.toOfNat0.{0} Real
                                                                                                  Real.instZero))
                                                                                              epsilonB)
                                                                                            (And
                                                                                              (@LE.le.{0} Real
                                                                                                Real.instLE
                                                                                                (@OfNat.ofNat.{0} Real
                                                                                                  (nat_lit 0)
                                                                                                  (@Zero.toOfNat0.{0}
                                                                                                    Real Real.instZero))
                                                                                                epsilonLS)
                                                                                              (@LE.le.{0} Real
                                                                                                Real.instLE
                                                                                                (@OfNat.ofNat.{0} Real
                                                                                                  (nat_lit 0)
                                                                                                  (@Zero.toOfNat0.{0}
                                                                                                    Real Real.instZero))
                                                                                                epsilonX)))) →
                                                                                      (productWeight leastSquaresWeight
                                                                                          correctionWeight : Real) →
                                                                                        (weights_nonneg :
                                                                                            And
                                                                                              (@LE.le.{0} Real
                                                                                                Real.instLE
                                                                                                (@OfNat.ofNat.{0} Real
                                                                                                  (nat_lit 0)
                                                                                                  (@Zero.toOfNat0.{0}
                                                                                                    Real Real.instZero))
                                                                                                productWeight)
                                                                                              (And
                                                                                                (@LE.le.{0} Real
                                                                                                  Real.instLE
                                                                                                  (@OfNat.ofNat.{0} Real
                                                                                                    (nat_lit 0)
                                                                                                    (@Zero.toOfNat0.{0}
                                                                                                      Real
                                                                                                      Real.instZero))
                                                                                                  leastSquaresWeight)
                                                                                                (@LE.le.{0} Real
                                                                                                  Real.instLE
                                                                                                  (@OfNat.ofNat.{0} Real
                                                                                                    (nat_lit 0)
                                                                                                    (@Zero.toOfNat0.{0}
                                                                                                      Real
                                                                                                      Real.instZero))
                                                                                                  correctionWeight))) →
                                                                                          (epsilonC_le :
                                                                                              @LE.le.{0} Real
                                                                                                Real.instLE epsilonC
                                                                                                (@HMul.hMul.{0, 0, 0}
                                                                                                  Real Real Real
                                                                                                  (@instHMul.{0} Real
                                                                                                    Real.instMul)
                                                                                                  productWeight uLow)) →
                                                                                            (epsilonLS_le :
                                                                                                @LE.le.{0} Real
                                                                                                  Real.instLE epsilonLS
                                                                                                  (@HMul.hMul.{0, 0, 0}
                                                                                                    Real Real Real
                                                                                                    (@instHMul.{0} Real
                                                                                                      Real.instMul)
                                                                                                    leastSquaresWeight
                                                                                                    uLow)) →
                                                                                              (epsilonX_le :
                                                                                                  @LE.le.{0} Real
                                                                                                    Real.instLE epsilonX
                                                                                                    (@HMul.hMul.{0, 0,
                                                                                                          0}
                                                                                                      Real Real Real
                                                                                                      (@instHMul.{0}
                                                                                                        Real
                                                                                                        Real.instMul)
                                                                                                      correctionWeight
                                                                                                      uLow)) →
                                                                                                (basisLowerGain
                                                                                                    imageLowerGain :
                                                                                                    Real) →
                                                                                                  (basisLowerGain_pos :
                                                                                                      @LT.lt.{0} Real
                                                                                                        Real.instLT
                                                                                                        (@OfNat.ofNat.{0}
                                                                                                          Real
                                                                                                          (nat_lit 0)
                                                                                                          (@Zero.toOfNat0.{0}
                                                                                                            Real
                                                                                                            Real.instZero))
                                                                                                        basisLowerGain) →
                                                                                                    (basis_gain :
                                                                                                        @HighamBench.p16MinGainAtLeast
                                                                                                          n keyDimension
                                                                                                          basis
                                                                                                          basisLowerGain) →
                                                                                                      (image_gain :
                                                                                                          @HighamBench.p16MinGainAtLeast
                                                                                                            n
                                                                                                            keyDimension
                                                                                                            (@HighamBench.p16SquareRectMul
                                                                                                              n
                                                                                                              keyDimension
                                                                                                              A basis)
                                                                                                            imageLowerGain) →
                                                                                                        (basis_not_numerically_rank_deficient :
                                                                                                            @LT.lt.{0}
                                                                                                              Real
                                                                                                              Real.instLT
                                                                                                              (@HMul.hMul.{0,
                                                                                                                    0,
                                                                                                                    0}
                                                                                                                Real
                                                                                                                Real
                                                                                                                Real
                                                                                                                (@instHMul.{0}
                                                                                                                  Real
                                                                                                                  Real.instMul)
                                                                                                                epsilonX
                                                                                                                (@HighamBench.p16RectFrobNorm
                                                                                                                  n
                                                                                                                  keyDimension
                                                                                                                  basis))
                                                                                                              basisLowerGain) →
                                                                                                          (key_near_dependence :
                                                                                                              @LT.lt.{0}
                                                                                                                  Nat
                                                                                                                  instLTNat
                                                                                                                  keyDimension
                                                                                                                  n →
                                                                                                                ∀
                                                                                                                  (phi :
                                                                                                                    Real),
                                                                                                                  @LT.lt.{0}
                                                                                                                      Real
                                                                                                                      Real.instLT
                                                                                                                      (@OfNat.ofNat.{0}
                                                                                                                        Real
                                                                                                                        (nat_lit
                                                                                                                          0)
                                                                                                                        (@Zero.toOfNat0.{0}
                                                                                                                          Real
                                                                                                                          Real.instZero))
                                                                                                                      phi →
                                                                                                                    @HighamBench.p16NearRankDeficient
                                                                                                                      n
                                                                                                                      (@HAdd.hAdd.{0,
                                                                                                                            0,
                                                                                                                            0}
                                                                                                                        Nat
                                                                                                                        Nat
                                                                                                                        Nat
                                                                                                                        (@instHAdd.{0}
                                                                                                                          Nat
                                                                                                                          instAddNat)
                                                                                                                        keyDimension
                                                                                                                        (@OfNat.ofNat.{0}
                                                                                                                          Nat
                                                                                                                          (nat_lit
                                                                                                                            1)
                                                                                                                          (instOfNatNat
                                                                                                                            (nat_lit
                                                                                                                              1))))
                                                                                                                      (@HighamBench.p16Augment
                                                                                                                        n
                                                                                                                        keyDimension
                                                                                                                        residualLow
                                                                                                                        phi
                                                                                                                        arnoldiProduct)
                                                                                                                      (@HMul.hMul.{0,
                                                                                                                            0,
                                                                                                                            0}
                                                                                                                        Real
                                                                                                                        Real
                                                                                                                        Real
                                                                                                                        (@instHMul.{0}
                                                                                                                          Real
                                                                                                                          Real.instMul)
                                                                                                                        (@HMul.hMul.{0,
                                                                                                                              0,
                                                                                                                              0}
                                                                                                                          Real
                                                                                                                          Real
                                                                                                                          Real
                                                                                                                          (@instHMul.{0}
                                                                                                                            Real
                                                                                                                            Real.instMul)
                                                                                                                          (@HAdd.hAdd.{0,
                                                                                                                                0,
                                                                                                                                0}
                                                                                                                            Real
                                                                                                                            Real
                                                                                                                            Real
                                                                                                                            (@instHAdd.{0}
                                                                                                                              Real
                                                                                                                              Real.instAdd)
                                                                                                                            (@HAdd.hAdd.{0,
                                                                                                                                  0,
                                                                                                                                  0}
                                                                                                                              Real
                                                                                                                              Real
                                                                                                                              Real
                                                                                                                              (@instHAdd.{0}
                                                                                                                                Real
                                                                                                                                Real.instAdd)
                                                                                                                              epsilonC
                                                                                                                              epsilonB)
                                                                                                                            epsilonLS)
                                                                                                                          (HighamBench.p16PolynomialFactorValue
                                                                                                                            dimensionFactor
                                                                                                                            n
                                                                                                                            keyDimension))
                                                                                                                        (@HighamBench.p16RectFrobNorm
                                                                                                                          n
                                                                                                                          (@HAdd.hAdd.{0,
                                                                                                                                0,
                                                                                                                                0}
                                                                                                                            Nat
                                                                                                                            Nat
                                                                                                                            Nat
                                                                                                                            (@instHAdd.{0}
                                                                                                                              Nat
                                                                                                                              instAddNat)
                                                                                                                            keyDimension
                                                                                                                            (@OfNat.ofNat.{0}
                                                                                                                              Nat
                                                                                                                              (nat_lit
                                                                                                                                1)
                                                                                                                              (instOfNatNat
                                                                                                                                (nat_lit
                                                                                                                                  1))))
                                                                                                                          (@HighamBench.p16Augment
                                                                                                                            n
                                                                                                                            keyDimension
                                                                                                                            residualLow
                                                                                                                            phi
                                                                                                                            arnoldiProduct)))) →
                                                                                                            (key_image_full_rank :
                                                                                                                @LT.lt.{0}
                                                                                                                  Real
                                                                                                                  Real.instLT
                                                                                                                  (@HMul.hMul.{0,
                                                                                                                        0,
                                                                                                                        0}
                                                                                                                    Real
                                                                                                                    Real
                                                                                                                    Real
                                                                                                                    (@instHMul.{0}
                                                                                                                      Real
                                                                                                                      Real.instMul)
                                                                                                                    (@HAdd.hAdd.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                      Real
                                                                                                                      Real
                                                                                                                      Real
                                                                                                                      (@instHAdd.{0}
                                                                                                                        Real
                                                                                                                        Real.instAdd)
                                                                                                                      (@HAdd.hAdd.{0,
                                                                                                                            0,
                                                                                                                            0}
                                                                                                                        Real
                                                                                                                        Real
                                                                                                                        Real
                                                                                                                        (@instHAdd.{0}
                                                                                                                          Real
                                                                                                                          Real.instAdd)
                                                                                                                        epsilonC
                                                                                                                        epsilonB)
                                                                                                                      epsilonLS)
                                                                                                                    (@HighamBench.p16RectFrobNorm
                                                                                                                      n
                                                                                                                      keyDimension
                                                                                                                      arnoldiProduct))
                                                                                                                  imageLowerGain) →
                                                                                                              (alpha
                                                                                                                  beta
                                                                                                                  lambda :
                                                                                                                  Real) →
                                                                                                                (coefficients_nonneg :
                                                                                                                    And
                                                                                                                      (@LE.le.{0}
                                                                                                                        Real
                                                                                                                        Real.instLE
                                                                                                                        (@OfNat.ofNat.{0}
                                                                                                                          Real
                                                                                                                          (nat_lit
                                                                                                                            0)
                                                                                                                          (@Zero.toOfNat0.{0}
                                                                                                                            Real
                                                                                                                            Real.instZero))
                                                                                                                        alpha)
                                                                                                                      (And
                                                                                                                        (@LE.le.{0}
                                                                                                                          Real
                                                                                                                          Real.instLE
                                                                                                                          (@OfNat.ofNat.{0}
                                                                                                                            Real
                                                                                                                            (nat_lit
                                                                                                                              0)
                                                                                                                            (@Zero.toOfNat0.{0}
                                                                                                                              Real
                                                                                                                              Real.instZero))
                                                                                                                          beta)
                                                                                                                        (@LE.le.{0}
                                                                                                                          Real
                                                                                                                          Real.instLE
                                                                                                                          (@OfNat.ofNat.{0}
                                                                                                                            Real
                                                                                                                            (nat_lit
                                                                                                                              0)
                                                                                                                            (@Zero.toOfNat0.{0}
                                                                                                                              Real
                                                                                                                              Real.instZero))
                                                                                                                          lambda))) →
                                                                                                                  (alpha_eq :
                                                                                                                      @Eq.{1}
                                                                                                                        Real
                                                                                                                        alpha
                                                                                                                        (@HDiv.hDiv.{0,
                                                                                                                              0,
                                                                                                                              0}
                                                                                                                          Real
                                                                                                                          Real
                                                                                                                          Real
                                                                                                                          (@instHDiv.{0}
                                                                                                                            Real
                                                                                                                            (@DivInvMonoid.toDiv.{0}
                                                                                                                              Real
                                                                                                                              Real.instDivInvMonoid))
                                                                                                                          (@HighamBench.p16RectFrobNorm
                                                                                                                            n
                                                                                                                            keyDimension
                                                                                                                            arnoldiProduct)
                                                                                                                          (@HMul.hMul.{0,
                                                                                                                                0,
                                                                                                                                0}
                                                                                                                            Real
                                                                                                                            Real
                                                                                                                            Real
                                                                                                                            (@instHMul.{0}
                                                                                                                              Real
                                                                                                                              Real.instMul)
                                                                                                                            basisLowerGain
                                                                                                                            (@HighamBench.p16FrobNorm
                                                                                                                              n
                                                                                                                              A)))) →
                                                                                                                    (beta_eq :
                                                                                                                        @Eq.{1}
                                                                                                                          Real
                                                                                                                          beta
                                                                                                                          (@Max.max.{0}
                                                                                                                            Real
                                                                                                                            Real.instMax
                                                                                                                            (@OfNat.ofNat.{0}
                                                                                                                              Real
                                                                                                                              (nat_lit
                                                                                                                                1)
                                                                                                                              (@One.toOfNat1.{0}
                                                                                                                                Real
                                                                                                                                Real.instOne))
                                                                                                                            alpha)) →
                                                                                                                      (lambda_eq :
                                                                                                                          @Eq.{1}
                                                                                                                            Real
                                                                                                                            lambda
                                                                                                                            (@HDiv.hDiv.{0,
                                                                                                                                  0,
                                                                                                                                  0}
                                                                                                                              Real
                                                                                                                              Real
                                                                                                                              Real
                                                                                                                              (@instHDiv.{0}
                                                                                                                                Real
                                                                                                                                (@DivInvMonoid.toDiv.{0}
                                                                                                                                  Real
                                                                                                                                  Real.instDivInvMonoid))
                                                                                                                              (@HighamBench.p16RectFrobNorm
                                                                                                                                n
                                                                                                                                keyDimension
                                                                                                                                basis)
                                                                                                                              basisLowerGain)) →
                                                                                                                        (modularAccuracy :
                                                                                                                            Real) →
                                                                                                                          (modular_accuracy_eq :
                                                                                                                              @Eq.{1}
                                                                                                                                Real
                                                                                                                                modularAccuracy
                                                                                                                                (@HAdd.hAdd.{0,
                                                                                                                                      0,
                                                                                                                                      0}
                                                                                                                                  Real
                                                                                                                                  Real
                                                                                                                                  Real
                                                                                                                                  (@instHAdd.{0}
                                                                                                                                    Real
                                                                                                                                    Real.instAdd)
                                                                                                                                  (@HAdd.hAdd.{0,
                                                                                                                                        0,
                                                                                                                                        0}
                                                                                                                                    Real
                                                                                                                                    Real
                                                                                                                                    Real
                                                                                                                                    (@instHAdd.{0}
                                                                                                                                      Real
                                                                                                                                      Real.instAdd)
                                                                                                                                    (@HAdd.hAdd.{0,
                                                                                                                                          0,
                                                                                                                                          0}
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      (@instHAdd.{0}
                                                                                                                                        Real
                                                                                                                                        Real.instAdd)
                                                                                                                                      (@HMul.hMul.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHMul.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instMul)
                                                                                                                                        alpha
                                                                                                                                        epsilonC)
                                                                                                                                      (@HMul.hMul.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHMul.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instMul)
                                                                                                                                        beta
                                                                                                                                        epsilonB))
                                                                                                                                    (@HMul.hMul.{0,
                                                                                                                                          0,
                                                                                                                                          0}
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      (@instHMul.{0}
                                                                                                                                        Real
                                                                                                                                        Real.instMul)
                                                                                                                                      beta
                                                                                                                                      epsilonLS))
                                                                                                                                  (@HMul.hMul.{0,
                                                                                                                                        0,
                                                                                                                                        0}
                                                                                                                                    Real
                                                                                                                                    Real
                                                                                                                                    Real
                                                                                                                                    (@instHMul.{0}
                                                                                                                                      Real
                                                                                                                                      Real.instMul)
                                                                                                                                    lambda
                                                                                                                                    epsilonX))) →
                                                                                                                            (dimension_factor_bound :
                                                                                                                                @LE.le.{0}
                                                                                                                                  Real
                                                                                                                                  Real.instLE
                                                                                                                                  (@HAdd.hAdd.{0,
                                                                                                                                        0,
                                                                                                                                        0}
                                                                                                                                    Real
                                                                                                                                    Real
                                                                                                                                    Real
                                                                                                                                    (@instHAdd.{0}
                                                                                                                                      Real
                                                                                                                                      Real.instAdd)
                                                                                                                                    (@HAdd.hAdd.{0,
                                                                                                                                          0,
                                                                                                                                          0}
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      (@instHAdd.{0}
                                                                                                                                        Real
                                                                                                                                        Real.instAdd)
                                                                                                                                      (@HMul.hMul.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHMul.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instMul)
                                                                                                                                        alpha
                                                                                                                                        productWeight)
                                                                                                                                      (@HMul.hMul.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHMul.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instMul)
                                                                                                                                        beta
                                                                                                                                        (@HAdd.hAdd.{0,
                                                                                                                                              0,
                                                                                                                                              0}
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          (@instHAdd.{0}
                                                                                                                                            Real
                                                                                                                                            Real.instAdd)
                                                                                                                                          (@OfNat.ofNat.{0}
                                                                                                                                            Real
                                                                                                                                            (nat_lit
                                                                                                                                              1)
                                                                                                                                            (@One.toOfNat1.{0}
                                                                                                                                              Real
                                                                                                                                              Real.instOne))
                                                                                                                                          leastSquaresWeight)))
                                                                                                                                    (@HMul.hMul.{0,
                                                                                                                                          0,
                                                                                                                                          0}
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      (@instHMul.{0}
                                                                                                                                        Real
                                                                                                                                        Real.instMul)
                                                                                                                                      lambda
                                                                                                                                      correctionWeight))
                                                                                                                                  (HighamBench.p16PolynomialFactorValue
                                                                                                                                    dimensionFactor
                                                                                                                                    n
                                                                                                                                    keyDimension)) →
                                                                                                                              (backward_correction_bound :
                                                                                                                                  @LE.le.{0}
                                                                                                                                    Real
                                                                                                                                    Real.instLE
                                                                                                                                    (@HDiv.hDiv.{0,
                                                                                                                                          0,
                                                                                                                                          0}
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      (@instHDiv.{0}
                                                                                                                                        Real
                                                                                                                                        (@DivInvMonoid.toDiv.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instDivInvMonoid))
                                                                                                                                      (@HighamBench.p16VecNorm
                                                                                                                                        n
                                                                                                                                        (@HSub.hSub.{0,
                                                                                                                                              0,
                                                                                                                                              0}
                                                                                                                                          (HighamBench.P16Vector
                                                                                                                                            n)
                                                                                                                                          (HighamBench.P16Vector
                                                                                                                                            n)
                                                                                                                                          (HighamBench.P16Vector
                                                                                                                                            n)
                                                                                                                                          (@instHSub.{0}
                                                                                                                                            (HighamBench.P16Vector
                                                                                                                                              n)
                                                                                                                                            (@Pi.instSub.{0,
                                                                                                                                                  0}
                                                                                                                                              (Fin
                                                                                                                                                n)
                                                                                                                                              (fun
                                                                                                                                                  (a :
                                                                                                                                                    Fin
                                                                                                                                                      n) =>
                                                                                                                                                Real)
                                                                                                                                              fun
                                                                                                                                                (i :
                                                                                                                                                  Fin
                                                                                                                                                    n) =>
                                                                                                                                              Real.instSub))
                                                                                                                                          residualHat
                                                                                                                                          (@HighamBench.p16MatVec
                                                                                                                                            n
                                                                                                                                            A
                                                                                                                                            correctionHat)))
                                                                                                                                      (@HAdd.hAdd.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHAdd.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instAdd)
                                                                                                                                        (@HighamBench.p16VecNorm
                                                                                                                                          n
                                                                                                                                          b)
                                                                                                                                        (@HMul.hMul.{0,
                                                                                                                                              0,
                                                                                                                                              0}
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          (@instHMul.{0}
                                                                                                                                            Real
                                                                                                                                            Real.instMul)
                                                                                                                                          (@HighamBench.p16FrobNorm
                                                                                                                                            n
                                                                                                                                            A)
                                                                                                                                          (@HighamBench.p16VecNorm
                                                                                                                                            n
                                                                                                                                            xNext))))
                                                                                                                                    (@HMul.hMul.{0,
                                                                                                                                          0,
                                                                                                                                          0}
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      Real
                                                                                                                                      (@instHMul.{0}
                                                                                                                                        Real
                                                                                                                                        Real.instMul)
                                                                                                                                      (@HMul.hMul.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHMul.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instMul)
                                                                                                                                        (@HMul.hMul.{0,
                                                                                                                                              0,
                                                                                                                                              0}
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          (@instHMul.{0}
                                                                                                                                            Real
                                                                                                                                            Real.instMul)
                                                                                                                                          (HighamBench.p16PolynomialFactorValue
                                                                                                                                            dimensionFactor
                                                                                                                                            n
                                                                                                                                            keyDimension)
                                                                                                                                          uLow)
                                                                                                                                        (@HighamBench.p16ConditionNumberF
                                                                                                                                          n
                                                                                                                                          A
                                                                                                                                          Ainv))
                                                                                                                                      (@HighamBench.p16BackwardError
                                                                                                                                        n
                                                                                                                                        A
                                                                                                                                        b
                                                                                                                                        xCurrent))) →
                                                                                                                                (forward_correction_bound :
                                                                                                                                    @LE.le.{0}
                                                                                                                                      Real
                                                                                                                                      Real.instLE
                                                                                                                                      (@HDiv.hDiv.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHDiv.{0}
                                                                                                                                          Real
                                                                                                                                          (@DivInvMonoid.toDiv.{0}
                                                                                                                                            Real
                                                                                                                                            Real.instDivInvMonoid))
                                                                                                                                        (@HighamBench.p16VecNorm
                                                                                                                                          n
                                                                                                                                          (@HSub.hSub.{0,
                                                                                                                                                0,
                                                                                                                                                0}
                                                                                                                                            (HighamBench.P16Vector
                                                                                                                                              n)
                                                                                                                                            (HighamBench.P16Vector
                                                                                                                                              n)
                                                                                                                                            (HighamBench.P16Vector
                                                                                                                                              n)
                                                                                                                                            (@instHSub.{0}
                                                                                                                                              (HighamBench.P16Vector
                                                                                                                                                n)
                                                                                                                                              (@Pi.instSub.{0,
                                                                                                                                                    0}
                                                                                                                                                (Fin
                                                                                                                                                  n)
                                                                                                                                                (fun
                                                                                                                                                    (a :
                                                                                                                                                      Fin
                                                                                                                                                        n) =>
                                                                                                                                                  Real)
                                                                                                                                                fun
                                                                                                                                                  (i :
                                                                                                                                                    Fin
                                                                                                                                                      n) =>
                                                                                                                                                Real.instSub))
                                                                                                                                            (@HAdd.hAdd.{0,
                                                                                                                                                  0,
                                                                                                                                                  0}
                                                                                                                                              (HighamBench.P16Vector
                                                                                                                                                n)
                                                                                                                                              (HighamBench.P16Vector
                                                                                                                                                n)
                                                                                                                                              (HighamBench.P16Vector
                                                                                                                                                n)
                                                                                                                                              (@instHAdd.{0}
                                                                                                                                                (HighamBench.P16Vector
                                                                                                                                                  n)
                                                                                                                                                (@Pi.instAdd.{0,
                                                                                                                                                      0}
                                                                                                                                                  (Fin
                                                                                                                                                    n)
                                                                                                                                                  (fun
                                                                                                                                                      (a :
                                                                                                                                                        Fin
                                                                                                                                                          n) =>
                                                                                                                                                    Real)
                                                                                                                                                  fun
                                                                                                                                                    (i :
                                                                                                                                                      Fin
                                                                                                                                                        n) =>
                                                                                                                                                  Real.instAdd))
                                                                                                                                              xCurrent
                                                                                                                                              correctionHat)
                                                                                                                                            xExact))
                                                                                                                                        (@HighamBench.p16VecNorm
                                                                                                                                          n
                                                                                                                                          xExact))
                                                                                                                                      (@HMul.hMul.{0,
                                                                                                                                            0,
                                                                                                                                            0}
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        Real
                                                                                                                                        (@instHMul.{0}
                                                                                                                                          Real
                                                                                                                                          Real.instMul)
                                                                                                                                        (@HMul.hMul.{0,
                                                                                                                                              0,
                                                                                                                                              0}
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          Real
                                                                                                                                          (@instHMul.{0}
                                                                                                                                            Real
                                                                                                                                            Real.instMul)
                                                                                                                                          (@HMul.hMul.{0,
                                                                                                                                                0,
                                                                                                                                                0}
                                                                                                                                            Real
                                                                                                                                            Real
                                                                                                                                            Real
                                                                                                                                            (@instHMul.{0}
                                                                                                                                              Real
                                                                                                                                              Real.instMul)
                                                                                                                                            (HighamBench.p16PolynomialFactorValue
                                                                                                                                              dimensionFactor
                                                                                                                                              n
                                                                                                                                              keyDimension)
                                                                                                                                            uLow)
                                                                                                                                          (@HighamBench.p16ConditionNumberF
                                                                                                                                            n
                                                                                                                                            A
                                                                                                                                            Ainv))
                                                                                                                                        (@HighamBench.p16ForwardError
                                                                                                                                          n
                                                                                                                                          xExact
                                                                                                                                          xCurrent))) →
                                                                                                                                  @HighamBench.P16FixedLowPrecisionMGSRestart
                                                                                                                                    n
                                                                                                                                    A
                                                                                                                                    Ainv
                                                                                                                                    b
                                                                                                                                    xExact
                                                                                                                                    xCurrent
                                                                                                                                    xNext
                                                                                                                                    residualHat
                                                                                                                                    correctionHat
                                                                                                                                    uLow
                                                                                                                                    dimensionFactor
```

### D037: `HighamBench.P16PolynomialFactor.mk`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `a8c6eea74c2a2a0885d42f9c23e54ef3821e761dedc0f21c6e669d08797687ae`

Type:

```lean
(degreeN degreeK : Nat) →
  (coefficient : Fin (instHAdd.hAdd degreeN 1) → Fin (instHAdd.hAdd degreeK 1) → Real) →
    (∀ (i : Fin (instHAdd.hAdd degreeN 1)) (j : Fin (instHAdd.hAdd degreeK 1)), Real.instLE.le 0 (coefficient i j)) →
      HighamBench.P16PolynomialFactor
```

Fully explicit type:

```lean
(degreeN degreeK : Nat) →
  (coefficient :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeN
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeK
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) →
    (coefficient_nonneg :
        ∀
          (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeN
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (j :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeK
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (coefficient i j)) →
      HighamBench.P16PolynomialFactor
```

### D038: `HighamBench.P16RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `ed6ed4c3dc41190752faa97194bb8058e9dd7deadfbd18631c282a8f04103d81`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(m k : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun m k => Matrix (Fin m) (Fin k) Real
```

### D039: `HighamBench.p16Augment`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b8a20ccd1a0141e32676a45d1777c354b7c37d97677afb2234a664e7158d3cea`

Type:

```lean
{n k : Nat} →
  HighamBench.P16Vector n → Real → HighamBench.P16RectMatrix n k → HighamBench.P16RectMatrix n (instHAdd.hAdd k 1)
```

Fully explicit type:

```lean
{n k : Nat} →
  (b : HighamBench.P16Vector n) →
    (phi : Real) →
      (C : HighamBench.P16RectMatrix n k) →
        HighamBench.P16RectMatrix n
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b phi C i i_1 => Fin.cases (instHMul.hMul (b i) phi) (fun j => C i j) i_1
```

### D040: `HighamBench.p16AugmentedColumn`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `edff7146376ef770366aba2e1853be47a9dd93c72ecd327c90997fcd05811128`

Type:

```lean
{n k : Nat} →
  HighamBench.P16Vector n → HighamBench.P16RectMatrix n k → Fin (instHAdd.hAdd k 1) → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n k : Nat} →
  (rhs : HighamBench.P16Vector n) →
    (C : HighamBench.P16RectMatrix n k) →
      (j :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n k} rhs C j => Fin.cases rhs (fun q row => C row q) j
```

### D041: `HighamBench.p16IsLeastSquaresSolution`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `bdfc265c3df9de57c6f0acfa56fa518d59187a9636cb68597f1faf194c63a797`

Type:

```lean
{m k : Nat} → HighamBench.P16RectMatrix m k → HighamBench.P16Vector m → HighamBench.P16Vector k → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P16RectMatrix m k) → (b : HighamBench.P16Vector m) → (y : HighamBench.P16Vector k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : HighamBench.P16Vector k),
    Real.instLE.le (HighamBench.p16VecNorm (instHSub.hSub b (HighamBench.p16RectMatVec A y)))
      (HighamBench.p16VecNorm (instHSub.hSub b (HighamBench.p16RectMatVec A z)))
```

### D042: `HighamBench.p16MinGainAtLeast`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `aea1bd8a88cb85c24aad7b9fbf82abc6098fc02caa123478bbd558b3d3759768`

Type:

```lean
{m k : Nat} → HighamBench.P16RectMatrix m k → Real → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P16RectMatrix m k) → (sigma : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A sigma =>
  ∀ (x : HighamBench.P16Vector k),
    Real.instLE.le (instHMul.hMul sigma (HighamBench.p16VecNorm x))
      (HighamBench.p16VecNorm (HighamBench.p16RectMatVec A x))
```

### D043: `HighamBench.p16NearRankDeficient`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `552e2d22c81360084216ba06ab4ea330e4c6339472649bada4698b2510af7ab9`

Type:

```lean
{m k : Nat} → HighamBench.P16RectMatrix m k → Real → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P16RectMatrix m k) → (delta : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A delta =>
  Exists fun x =>
    And (Eq (HighamBench.p16VecNorm x) 1)
      (Real.instLE.le (HighamBench.p16VecNorm (HighamBench.p16RectMatVec A x)) delta)
```

### D044: `HighamBench.p16RectFrobNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `a2ed232b7b5960b8a6f9c5907344e0b80314d5f88f6285f45b4409ed2a6d7203`

Type:

```lean
{m k : Nat} → HighamBench.P16RectMatrix m k → Real
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P16RectMatrix m k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D045: `HighamBench.p16RectMatVec`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6f698af222e83d101b281cbccf24e989a885c3a996fa1b73f33092817b45db0c`

Type:

```lean
{m k : Nat} → HighamBench.P16RectMatrix m k → HighamBench.P16Vector k → HighamBench.P16Vector m
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P16RectMatrix m k) → (x : HighamBench.P16Vector k) → HighamBench.P16Vector m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D046: `HighamBench.p16SquareRectMul`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `0053caf146fae0af9f54e65099d1a3e27476c2f20502180d10ba739f1bc05026`

Type:

```lean
{n k : Nat} → HighamBench.P16Matrix n → HighamBench.P16RectMatrix n k → HighamBench.P16RectMatrix n k
```

Fully explicit type:

```lean
{n k : Nat} → (A : HighamBench.P16Matrix n) → (B : HighamBench.P16RectMatrix n k) → HighamBench.P16RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
```

### D047: `And`

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

### D048: `HAdd.hAdd`

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

### D049: `HMul.hMul`

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

### D050: `LE.le`

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

### D051: `LT.lt`

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

### D052: `Nat`

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

### D053: `OfNat.ofNat`

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

### D054: `One.toOfNat1`

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

### D055: `Real`

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

### D056: `Real.instAdd`

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

### D057: `Real.instLE`

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

### D058: `Real.instLT`

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

### D059: `Real.instMul`

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

### D060: `Real.instOne`

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

### D061: `Real.instZero`

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

### D062: `Zero.toOfNat0`

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

### D063: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D064: `instHAdd`

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

### D065: `instHMul`

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

### D066: `instOfNatNat`

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

### D067: `DivInvMonoid.toDiv`

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

### D068: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D069: `HDiv.hDiv`

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

### D070: `HSub.hSub`

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

### D071: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D072: `Real.instDivInvMonoid`

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

### D073: `Real.instSub`

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

### D074: `instHDiv`

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

### D075: `instHSub`

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

### D076: `Eq`

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

### D077: `Fin.fintype`

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

### D078: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D079: `Finset.sum`

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

### D080: `Finset.univ`

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

### D081: `HPow.hPow`

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

### D082: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D083: `Monoid.toNatPow`

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

### D084: `Nat.cast`

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

### D085: `Ne`

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

### D086: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D087: `Pi.instZero`

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

### D088: `Real.instAddCommMonoid`

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

### D089: `Real.instAddGroup`

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

### D090: `Real.instMonoid`

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

### D091: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D092: `Real.lattice`

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

### D094: `abs`

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

### D095: `instHPow`

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

### D096: `instLTNat`

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

### D097: `Function.Bijective`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `2da1e723243113bf4396d64f6b64f6ee8db3b9e981ad6ec7448e7745e511e5e2`

Type:

```lean
{α : Sort u₁} → {β : Sort u₂} → (α → β) → Prop
```

Fully explicit type:

```lean
{α : Sort u₁} → {β : Sort u₂} → (f : α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => And (Function.Injective f) (Function.Surjective f)
```

### D098: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`

Type:

```lean
{m : Type u_3} → {α : Type u_5} → [Fintype m] → [RCLike α] → [DecidableEq m] → NormedRing (Matrix m m α)
```

Fully explicit type:

```lean
{m : Type u_3} →
  {α : Type u_5} →
    [Fintype.{u_3} m] →
      [RCLike.{u_5} α] → [DecidableEq.{u_3 + 1} m] → NormedRing.{max u_5 u_3} (Matrix.{u_3, u_3, u_5} m m α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {α} [Fintype m] [RCLike α] [DecidableEq m] =>
  let __src := Matrix.frobeniusSeminormedAddCommGroup;
  let __src_1 := Matrix.instRing;
  { toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := ⋯, toMul := __src_1.toMul, left_distrib := ⋯,
    right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯, toOne := __src_1.toOne, one_mul := ⋯,
    mul_one := ⋯, toNatCast := __src_1.toNatCast, natCast_zero := ⋯, natCast_succ := ⋯, npow := __src_1.npow,
    npow_zero := ⋯, npow_succ := ⋯, toNeg := __src.toNeg, toSub := __src.toSub, sub_eq_add_neg := ⋯,
    zsmul := __src.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯,
    toIntCast := __src_1.toIntCast, intCast_ofNat := ⋯, intCast_negSucc := ⋯,
    toPseudoMetricSpace := __src.toPseudoMetricSpace, eq_of_dist_eq_zero := ⋯, dist_eq := ⋯, norm_mul_le := ⋯ }
```

### D099: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Fully explicit type:

```lean
{E : Type u_8} → [self : Norm.{u_8} E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D100: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`

Type:

```lean
{α : Type u_5} → [self : NormedRing α] → Norm α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : NormedRing.{u_5} α] → Norm.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NormedRing α] => self.1
```

### D101: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`

Type:

```lean
RCLike Real
```

Fully explicit type:

```lean
RCLike.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toDenselyNormedField := Real.denselyNormedField, toStarRing := instStarRingReal,
  toNormedAlgebra := NormedAlgebra.id Real, toCompleteSpace := Real.instCompleteSpace, re := AddMonoidHom.id Real,
  im := 0, I := 0, I_re_ax := Real.instRCLike._proof_1, I_mul_I_ax := Real.instRCLike._proof_8, re_add_im_ax := ⋯,
  ofReal_re_ax := Real.instRCLike._proof_11, ofReal_im_ax := Real.instRCLike._proof_12, mul_re_ax := ⋯, mul_im_ax := ⋯,
  conj_re_ax := ⋯, conj_im_ax := ⋯, conj_I_ax := Real.instRCLike._proof_7, norm_sq_eq_def_ax := ⋯, mul_im_I_ax := ⋯,
  toPartialOrder := Real.partialOrder, le_iff_re_im := @Real.instRCLike._proof_13, toDecidableEq := Real.decidableEq }
```

### D102: `instDecidableEqFin`

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

### D103: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D104: `Fin.instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `8f9c302902ae8c66b3f71728ffe02994a026b562f27b9df8d4f84793e455e26b`

Type:

```lean
{n : Nat} → [NeZero n] → {i : Nat} → OfNat (Fin n) i
```

Fully explicit type:

```lean
{n : Nat} → [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n] → {i : Nat} → OfNat.{0} (Fin n) i
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] {i} => { ofNat := Fin.ofNat n i }
```

### D105: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

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
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D106: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D107: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `6fa198061d1b8595a7b8b0ed74bd9e48f2c7a18aa01bf39d9c30be49c1d4741c`

Type:

```lean
{α : Type u} → [self : Max α] → α → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Max.{u} α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Max α] => self.1
```

### D108: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `5`
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

### D109: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `313f6558836157f8e8b4ea7be18fb6953bf9aefc4dcb68940ef5c4889e18a763`

Type:

```lean
Max Real
```

Fully explicit type:

```lean
Max.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ max := Real.sup✝ }
```

### D110: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D111: `instNeZeroNatHAdd_1`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `4cf1e3f35432e064f333472fa6363b628df31521c110222df9633f8b8ba8cd25`

Type:

```lean
∀ {n m : Nat} [h : NeZero m], NeZero (instHAdd.hAdd n m)
```

Fully explicit type:

```lean
∀ {n m : Nat} [h : @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) m],
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n m)
```

### D112: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D113: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `38edd2256cd8f4f33f2c43ce7c36a1e1c7aded652580ec57a0adaf0ec346b64d`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive 0 → ((i : Fin n) → motive i.succ) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Fully explicit type:

```lean
{n : Nat} →
  {motive :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Sort u_1} →
    (zero :
        motive
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))) →
      (succ : (i : Fin n) → motive (@Fin.succ n i)) →
        (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} zero succ i => Fin.induction zero (fun i x => succ i) i
```

### D114: `Matrix.frobeniusNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `3f944d9003e72c887b38048a3f469c42c010d0e141780ed19b0137eb25d742ba`

Type:

```lean
{m : Type u_3} →
  {n : Type u_4} →
    {α : Type u_5} → [Fintype m] → [Fintype n] → [NormedAddCommGroup α] → NormedAddCommGroup (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_3} →
  {n : Type u_4} →
    {α : Type u_5} →
      [Fintype.{u_3} m] →
        [Fintype.{u_4} n] →
          [NormedAddCommGroup.{u_5} α] → NormedAddCommGroup.{max (max u_5 u_4) u_3} (Matrix.{u_3, u_4, u_5} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Fintype m] [Fintype n] [NormedAddCommGroup α] => PiLp.normedAddCommGroupToPi 2 fun a => n → α
```

### D115: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Fully explicit type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup.{u_8} E] → Norm.{u_8} E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D116: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `9ff0d896c635e2a38531d689d24ee70cfffa41565354ce15f6ff59b51650bd93`

Type:

```lean
NormedAddCommGroup Real
```

Fully explicit type:

```lean
NormedAddCommGroup.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Real.norm, toAddCommGroup := Real.instAddCommGroup, toMetricSpace := Real.metricSpace, dist_eq := ⋯ }
```
